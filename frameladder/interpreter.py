"""Run the COBOL subset concretely, to check a plan and to say where it failed.

This is tier 1.  A plan that type-checks symbolically can still be wrong -
a guard the ladder never lifted, an ordering it got backwards - and the
only way to know is to run it.  When a plan does fail, the useful output
is not "false" but *which guard on the chain went the wrong way*, because
that is the single question worth handing to an agent.

State is bytes where the data division says how, and a field map where it
does not.  ``storage.FieldMap`` keeps the ``{FIELD: value}`` interface every
caller uses, but a name with a known layout is a *window* onto a record
rather than a cell of its own - which is what COBOL storage is, and what
makes subscripts, REDEFINES of any shape, MOVE truncation and USAGE one
mechanism instead of four approximations of one.  A name with no layout - a
table index, a harness slot, a value a plan supplies for something the
program never declared - stays an ordinary dictionary entry, which is what
lets this be adopted a record at a time rather than all at once.

An *unsubscripted* reference to a table reads occurrence 1, because there is
nothing else to pick; :attr:`Trace.approximations` records that rather than
hiding it.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .conditions import condition_atoms, when_condition
from .ir import base_name, holds, is_arithmetic, norm, parse_term


def _decimals(spec: str) -> int:
    """Digits after the implied decimal point in a PIC clause."""
    m = re.search(r"V9\((\d+)\)", spec)
    if m:
        return int(m.group(1))
    m = re.search(r"V(9+)", spec)
    return len(m.group(1)) if m else 0

# Reaching a target takes hundreds of steps, not thousands. A
# generous ceiling only means a non-terminating plan burns
# seconds before saying so.
MAX_STEPS = 20_000
MAX_DEPTH = 64
MAX_LOOP = 200
RUNAWAY = 400        # one paragraph running this often is a loop, not progress

# Standard runtime services that terminate the program rather than return.
# Knowing these is the same kind of knowledge as knowing that abort() does
# not return - it is about the platform, not about any one program - and
# without it every abend path looks like it carries on executing.
TERMINATING_CALLS = {"CEE3ABD", "ILBOABN0", "ILBOABN", "CANCEL"}

# CICS commands that hand control away and never come back. RETURN ends the
# program, XCTL replaces it, ABEND kills the task - none of them fall through
# to the next statement. Running on past one is the CICS equivalent of running
# on past GOBACK: every statement after it looks reachable when it is not.
TERMINATING_EXECS = {"EXEC:CICS:RETURN", "EXEC:CICS:XCTL", "EXEC:CICS:ABEND"}

# A pseudo-conversational program does not run once. `EXEC CICS RETURN
# TRANSID(T) COMMAREA(C)` ends *this* task and asks CICS to start T again on
# the next input, handing it back C - so the program is re-entered from the
# top with its own saved state and EIBCALEN non-zero. Modelling one task per
# run is correct for the task and wrong for the application: everything the
# program does on re-entry becomes unreachable, which on a screen program is
# most of it. Bounded, because each task is a fixed point once the commarea
# stops changing.
MAX_TASKS = 4
_EXEC_HEAD = re.compile(r"\bEXEC\s+(CICS|SQL|DLI)\b", re.I)
_RETURN_TRANSID = re.compile(r"\bTRANSID\s*\(", re.I)
_RETURN_COMMAREA = re.compile(r"\bCOMMAREA\s*\(\s*([A-Z0-9-]+)", re.I)

# FUNCTION CURRENT-DATE returns YYYYMMDDhhmmssttshhmm. Reading the real clock
# would break determinism, which is an invariant here, so one instant stands
# for "now" in every run.
FIXED_NOW = "20240101120000000+0000"
# The slot the harness sets to move the clock. A space makes it impossible to
# collide with a COBOL identifier.
CLOCK_SLOT = "FUNCTION CURRENT-DATE"
CLOCK_VALUES = ("20240101120000000+0000", "20241231235959000+0000",
                "20240229120000000+0000", "20240615000000000+0000")


# A figurative constant is as wide as whatever receives it. `MOVE SPACES TO
# <group>` blanks the whole group and `MOVE ZEROS` fills it with the
# *character* zero - one byte of it padded out is a different record. The
# term parser collapses these to a single Python value, correctly, because
# every other consumer wants the value; execution wants the width too.
_FILL = {"ZERO": "0", "ZEROS": "0", "ZEROES": "0",
         "SPACE": " ", "SPACES": " ",
         "LOW-VALUE": "\x00", "LOW-VALUES": "\x00",
         "HIGH-VALUE": "\xff", "HIGH-VALUES": "\xff",
         "QUOTE": "\"", "QUOTES": "\""}
_ALL_LITERAL = re.compile(r"^ALL\s+(?:'(.)'|\"(.)\")$", re.I)


def _fill_char(source: str) -> str:
    """The repeating byte a figurative source stands for, or ''."""
    text = norm(source or "").upper()
    if text in _FILL:
        return _FILL[text]
    m = _ALL_LITERAL.match(text)
    if m:
        return m.group(1) or m.group(2) or ""
    return ""


def _numval(text: str) -> float:
    """FUNCTION NUMVAL / NUMVAL-C. Currency, commas and a trailing sign are
    part of the notation rather than part of the number."""
    body = (text or "").strip()
    trailing = body.endswith("-") or body.upper().endswith("CR") \
        or body.upper().endswith("DB")
    kept = [c for c in body if c.isdigit() or c == "."]
    if not kept:
        return 0.0
    try:
        value = float("".join(kept))
    except ValueError:
        return 0.0
    if body.startswith("-") or trailing:
        value = -value
    return value


def _test_numval(text: str) -> int:
    """FUNCTION TEST-NUMVAL[-C]: 0 when the whole item is a valid number,
    otherwise the one-based position of the first character that is not."""
    body = (text or "")
    stripped = body.strip()
    if not stripped:
        return len(body) + 1
    seen_digit, seen_dot = False, False
    for offset, ch in enumerate(stripped, 1):
        if ch.isdigit():
            seen_digit = True
        elif ch == "." and not seen_dot:
            seen_dot = True
        elif ch in "+-" and offset == 1:
            continue
        elif ch in "+-" and offset == len(stripped):
            continue
        elif ch in ",$ ":
            continue
        else:
            return body.index(ch) + 1 if ch in body else offset
    return 0 if seen_digit else len(body) + 1


def _integer_of_date(yyyymmdd: int) -> int:
    import datetime
    try:
        d = datetime.date(yyyymmdd // 10000, (yyyymmdd // 100) % 100,
                          yyyymmdd % 100)
    except ValueError:
        return 0
    return (d - datetime.date(1600, 12, 31)).days


def _date_of_integer(days: int) -> int:
    import datetime
    try:
        d = datetime.date(1600, 12, 31) + datetime.timedelta(days=days)
    except (ValueError, OverflowError):
        return 0
    return d.year * 10000 + d.month * 100 + d.day


# --------------------------------------------------------------------------
# INSPECT
# --------------------------------------------------------------------------
#
# INSPECT is the language's only string-scanning verb, and all three of its
# formats produce a value some later condition turns on: TALLYING writes a
# count, REPLACING and CONVERTING rewrite the item in place.  Skipped, the
# counter keeps whatever it held - usually zero, because the program has just
# initialised it - so `IF WS-N > 0` is false however the data is shaped and
# that direction cannot be reached by any input.
#
# The three functions below are the scan itself, kept free of the interpreter
# so they can be tested against the standard's own examples.  All of them work
# on the *bytes of the item*, which is why the caller pads to the declared
# width first: `INSPECT WS-A TALLYING N FOR ALL SPACE` on a PIC X(6) holding
# 'AB' counts four, and counts nothing at all if the trailing spaces were
# dropped on the way in.

_INSPECT_SECTIONS = ("TALLYING", "REPLACING", "CONVERTING")


def _inspect_region(text: str, before, after) -> tuple:
    """The span of ``text`` one item is allowed to examine.

    ``AFTER INITIAL d`` starts the span just past the first ``d``; ``BEFORE
    INITIAL d`` ends it at the first ``d`` from there on.  A delimiter that
    does not occur makes an AFTER span empty and leaves a BEFORE span whole,
    which is what the standard says and is the opposite of what "ignore the
    phrase" would do.
    """
    lo, hi = 0, len(text)
    if after is not None:
        found = text.find(after) if after else -1
        lo = found + len(after) if found >= 0 else len(text)
    if before is not None:
        found = text.find(before, lo) if before else -1
        hi = found if found >= 0 else hi
    return lo, max(lo, min(hi, len(text)))


def inspect_tally(text: str, items: list) -> list:
    """Counts for each TALLYING item, in one left-to-right pass.

    The items share the pass: at every position they are compared in the
    order written and the *first* match wins, then the cursor advances past
    what it matched.  Counting each item independently would double-count
    overlapping arguments, and `ALL 'AA'` over 'AAA' is one occurrence rather
    than two for exactly this reason.

    ``LEADING`` stops for good at the first position in its region where it
    does not match, which is what makes it different from ``ALL``.
    """
    counts = [0] * len(items)
    alive = [True] * len(items)
    position, size = 0, len(text)
    while position < size:
        matched = False
        for index, item in enumerate(items):
            lo, hi = item["lo"], item["hi"]
            if not lo <= position < hi:
                continue
            if item["kind"] == "CHARACTERS":
                counts[index] += 1
                position += 1
                matched = True
                break
            if not alive[index]:
                continue
            arg = item["arg"]
            if arg and position + len(arg) <= hi \
                    and text[position:position + len(arg)] == arg:
                counts[index] += 1
                position += len(arg)
                matched = True
                break
            if item["kind"] == "LEADING":
                alive[index] = False
        if not matched:
            position += 1
    return counts


def inspect_replace(text: str, items: list) -> str:
    """The item after REPLACING has run.

    Matching is against the original bytes and writing is to a copy: a
    replacement never becomes part of a later comparison, because the cursor
    has already moved past it.  ``FIRST`` retires after one hit and
    ``LEADING`` at its first miss.
    """
    out = list(text)
    alive = [True] * len(items)
    position, size = 0, len(text)
    while position < size:
        matched = False
        for index, item in enumerate(items):
            lo, hi = item["lo"], item["hi"]
            if not lo <= position < hi:
                continue
            if item["kind"] == "CHARACTERS":
                replacement = item["to"] or " "
                out[position] = replacement[0]
                position += 1
                matched = True
                break
            if not alive[index]:
                continue
            arg = item["arg"]
            if arg and position + len(arg) <= hi \
                    and text[position:position + len(arg)] == arg:
                replacement = (item["to"] or "")
                # The standard requires the two to be the same size; a source
                # that disagrees is padded rather than allowed to shift every
                # byte after it.
                replacement = replacement.ljust(len(arg))[:len(arg)]
                out[position:position + len(arg)] = list(replacement)
                if item["kind"] == "FIRST":
                    alive[index] = False
                position += len(arg)
                matched = True
                break
            if item["kind"] == "LEADING":
                alive[index] = False
        if not matched:
            position += 1
    return "".join(out)


def inspect_convert(text: str, source: str, target: str, lo: int, hi: int) -> str:
    """CONVERTING is a character translation over the region.

    A single-character target - which is what a figurative constant gives -
    stands for every position, so ``CONVERTING 'ABC' TO SPACES`` blanks all
    three.
    """
    if not source:
        return text
    table = {}
    for index, ch in enumerate(source):
        if index < len(target):
            table.setdefault(ch, target[index])
        elif target:
            table.setdefault(ch, target[-1])
    out = list(text)
    for position in range(max(0, lo), min(hi, len(text))):
        if out[position] in table:
            out[position] = table[out[position]]
    return "".join(out)


def _inspect_words(body: str) -> list:
    """Split an INSPECT body into words, keeping quoted literals whole."""
    return re.findall(r"'[^']*'|\"[^\"]*\"|[^\s]+", body or "")


def _inspect_region_words(words: list, at: int) -> tuple:
    """Read any BEFORE/AFTER phrases starting at ``at``.

    Returns ``(before, after, next-index)`` with the delimiters as raw
    operand text.
    """
    before = after = None
    while at < len(words) and words[at].upper() in ("BEFORE", "AFTER"):
        sense = words[at].upper()
        at += 1
        if at < len(words) and words[at].upper() == "INITIAL":
            at += 1
        if at >= len(words):
            break
        if sense == "BEFORE":
            before = words[at]
        else:
            after = words[at]
        at += 1
    return before, after, at


def parse_inspect(body: str):
    """The clauses of one INSPECT, as raw operand text.

    Values are left unresolved because an operand may be an identifier, and
    what it holds is a question for the run rather than for the parse.
    """
    words = _inspect_words(body)
    if not words:
        return None
    at, subject = 0, []
    while at < len(words) and words[at].upper() not in _INSPECT_SECTIONS:
        subject.append(words[at])
        at += 1
    if not subject:
        return None
    plan = {"subject": " ".join(subject), "tallying": [], "replacing": [],
            "converting": None}
    while at < len(words):
        section = words[at].upper()
        at += 1
        if section == "TALLYING":
            counter = None
            while at < len(words) and words[at].upper() not in _INSPECT_SECTIONS:
                word = words[at].upper()
                if word in ("ALL", "LEADING", "CHARACTERS"):
                    arg = None
                    at += 1
                    if word != "CHARACTERS":
                        if at >= len(words):
                            break
                        arg = words[at]
                        at += 1
                    before, after, at = _inspect_region_words(words, at)
                    if counter is not None:
                        plan["tallying"].append(
                            {"counter": counter, "kind": word, "arg": arg,
                             "before": before, "after": after})
                    continue
                if word == "FOR":
                    at += 1
                    continue
                counter = words[at]
                at += 1
        elif section == "REPLACING":
            while at < len(words) and words[at].upper() not in _INSPECT_SECTIONS:
                word = words[at].upper()
                if word not in ("ALL", "LEADING", "FIRST", "CHARACTERS"):
                    at += 1
                    continue
                at += 1
                arg = None
                if word != "CHARACTERS":
                    if at >= len(words):
                        break
                    arg = words[at]
                    at += 1
                if at < len(words) and words[at].upper() == "BY":
                    at += 1
                if at >= len(words):
                    break
                to = words[at]
                at += 1
                before, after, at = _inspect_region_words(words, at)
                plan["replacing"].append({"kind": word, "arg": arg, "to": to,
                                          "before": before, "after": after})
        elif section == "CONVERTING":
            if at >= len(words):
                break
            source = words[at]
            at += 1
            if at < len(words) and words[at].upper() == "TO":
                at += 1
            if at >= len(words):
                break
            target = words[at]
            at += 1
            before, after, at = _inspect_region_words(words, at)
            plan["converting"] = {"from": source, "to": target,
                                  "before": before, "after": after}
        else:
            at += 1
    return plan


class _Goto(Exception):
    def __init__(self, target: str):
        self.target = target


class _Stop(Exception):
    pass


class _NextTask(Exception):
    """`EXEC CICS RETURN TRANSID(...)`: this task ends, another one starts."""


class _ExitPerform(Exception):
    """`EXIT PERFORM` - leave the innermost inline PERFORM."""


class _ExitPerformCycle(Exception):
    """`EXIT PERFORM CYCLE` - end this iteration of it."""


class _ExitParagraph(Exception):
    """`EXIT PARAGRAPH` / `EXIT SECTION`: leave this paragraph, keep running."""


@dataclass
class GuardEvent:
    paragraph: str
    line: int
    kind: str
    condition: str
    result: bool
    values: dict = field(default_factory=dict)
    # Position of the decision within its paragraph. This, not `line`, is
    # what identifies it - COPY expansion gives many decisions one line.
    ordinal: int = -1
    # term key -> `origins.Origin`, when the run was asked to track them.
    # This is what says *which entry-state bytes* would have to change to
    # send this decision the other way, after the program's own writes.
    origins: dict = field(default_factory=dict)


@dataclass
class Trace:
    entered: list = field(default_factory=list)
    guards: list = field(default_factory=list)
    steps: int = 0
    stopped: str = ""
    runaway: str = ""
    approximations: list = field(default_factory=list)

    @property
    def entered_set(self) -> set:
        return set(self.entered)


class Interpreter:
    """Execute the subset, applying stub returns *at the call site*.

    Pinning a stub's return as an ordinary variable is wrong in a way that
    matters: a file read returns records and then end-of-file, and a plan
    that pins the return code to '00' forever describes a file that never
    ends.  Outcomes are therefore delivered per call, matched on the same
    discriminators the ladder used to tell two invocations apart, and a
    terminal value takes over once the planned ones run out.
    """

    def __init__(self, program, state: dict | None = None, *,
                 stubs: dict | None = None, terminals: dict | None = None,
                 defaults: dict | None = None, repeat: int = 1,
                 sequential: bool = True, track_origins: bool = False):
        self.program = program
        self.model = program.model
        # The layout is a property of the data division, so it is computed
        # once per program and shared; only the bytes belong to this run.
        from .storage import ByteMemory, FieldMap, layout_of
        self.memory = ByteMemory(layout_of(self.model))
        self._slots: dict = {}
        self.state = FieldMap(self.memory,
                              {k.upper(): v for k, v in (state or {}).items()})
        self.stubs = stubs or {}
        self.terminals = {k.upper(): {n.upper(): v for n, v in vals.items()}
                          for k, vals in (terminals or {}).items()}
        # A default is what an operation returns when no planned outcome
        # matches it at all - an OPEN succeeding while the plan only says
        # what a READ returns. A terminal is different: it is what happens
        # once the planned outcomes are used up, which is how a read loop
        # ends. Conflating them makes every open fail or every read endless.
        self.defaults = {k.upper(): {n.upper(): v for n, v in vals.items()}
                         for k, vals in (defaults or {}).items()}
        self.repeat = max(1, repeat)
        self.sequential = sequential
        self.trace = Trace()
        self._names = program.paragraph_names
        # Nothing is pinned. An entry state supplies a variable's *initial*
        # value; from then on the program owns it, and a COBOL program
        # assigns to its inputs constantly.
        #
        # Freezing them was the single largest source of wrong answers here.
        # `coverage --sample` draws a state over every name the program
        # compares against a literal - precisely the variables that gate
        # branches - so the run proceeded with its most decision-relevant
        # fields turned into read-only constants: file statuses that never
        # update, flags that never flip, end-of-file that never arrives. In
        # CBACT01C a failed OPEN would run `MOVE 12 TO APPL-RESULT` and the
        # very next line would still find `88 APPL-AOK VALUE 0` true, scoring
        # both arms in one run that no compiler can produce. Honouring
        # assignments costs a third of the reported coverage and agrees with
        # GnuCOBOL instead of contradicting it.
        #
        # A plan whose value the program overwrites before the target is a
        # plan that needs an obligation about that write - which is what
        # `blocking_writes` and `establishing_writes` are for - not a plan
        # that needs the write suppressed.
        # The level-88 table, handed to the condition parser so an
        # abbreviated relation never reads a condition-name as an
        # elided operand - see `conditions.expand_abbreviated`.
        self._names88 = frozenset(self.model.condition_names)
        self._pinned: set = set()
        self._delivered: dict = {}
        self._selector_cache: dict = {}
        self._visits: dict = {}
        self._layouts: dict = {}
        self.calls: dict = {}
        # ALTER rewrites another paragraph's GO TO at run time. A dispatcher
        # built on it - and CardDemo's is - cycles forever without this.
        self.altered: dict = {}
        # What the harness supplied at entry. A terminal read re-delivers it,
        # so it has to survive the program clearing the area first.
        #
        # Held as a snapshot of the *bytes*, not as a materialised map. Every
        # declared name has a slot, so `dict(state)` read one value per field
        # in the whole data division on every construction - 6,953 of them on
        # a 32,000-line program, once per run, on 38,000 runs. The snapshot
        # answers the same question: what did this name hold at entry.
        supplied = FieldMap(self.memory.copy(), {})
        supplied.extra = dict(self.state.extra)
        self._supplied = supplied
        # Which names the entry state actually spoke about - as given and as
        # base names, since a state may say `ACTIDINI OF COTRN2AI` and the
        # data model answers for `ACTIDINI`. `_supplied` cannot answer this:
        # it snapshots every declared slot, named or not.
        self._entry_names = set()
        for key in (state or {}):
            key = key.upper()
            self._entry_names.add(key)
            self._entry_names.add(key.split(" OF ")[0].strip())
        # Membership is asked of the same keys the materialised map had - the
        # laid-out names plus whatever had no slot - and not of `FieldMap`'s
        # own test, which resolves a qualified reference to its declaration
        # and would answer yes to a key the map never held.
        self._supplied_slots = self.memory.layout.slots
        # Two names over one set of bytes. Built once because it is a
        # property of the data division, not of the run.
        self._overlays = self._overlay_map()
        # Off by default and free when off: every other caller pays nothing,
        # and the search that wants it is the only one that carries the cost.
        # A name absent from this table has not been written on this run, so
        # it still holds what the entry state gave it - which is why the
        # table records `None` for an opaque write rather than deleting.
        self.track_origins = track_origins
        self._origin: dict = {}

    # -- values ------------------------------------------------------------
    def slot_of(self, name: str):
        """The byte window a name describes, or None when there is no layout."""
        key = (name or "").upper()
        if key in self._slots:
            return self._slots[key]
        found = self.memory.layout.slot_for(key)
        self._slots[key] = found
        return found

    def _indices(self, term) -> tuple:
        """A term's subscripts as numbers.

        ``WS-TAB(I)`` and ``WS-TAB(I + 1)`` both occur, so a subscript goes
        through the same expression evaluator a refmod offset does.
        """
        if not term.index:
            return ()
        return tuple(self._as_int(str(part), 1) for part in term.index)

    def value_of(self, term) -> object:
        if term.kind == "const":
            return term.value
        if term.func:
            return self._intrinsic(term)
        value = self._stored(term.name, self._indices(term))
        if term.refmod:
            value = self._slice(term, value)
        return value

    def _stored(self, name: str, index: tuple = ()) -> object:
        slot = self.slot_of(name)
        if slot is not None:
            if slot.dims and not index:
                # A table read with no subscript takes occurrence 1, because
                # there is nothing else to take. That is an approximation and
                # it is now reported as one, where before every occurrence of
                # every table was silently one cell.
                note = "unsubscripted table read: %s" % name
                if note not in self.trace.approximations:
                    self.trace.approximations.append(note)
            return self.memory.read(slot, index)
        # No layout for this name: the field map is the store, as before.
        # A value written to the group itself outranks one assembled from its
        # children: the plan pinned it, or a record area was filled whole.
        if name in self.state:
            return self.state[name]
        group = self._assembled(name)
        if group is not None:
            return group
        # A qualified reference names a declaration that is recorded under its
        # base name, so reads have to see through the qualifier exactly as
        # lookups elsewhere do - otherwise every write lands on one key, every
        # read misses, and the condition is decided on a default.
        found = self.model.look(self.state, name)
        if found is not None:
            return found
        found = self.model.look(self.model.initial, name)
        if found is not None:
            return found
        overlaid = self._read_overlay(name)
        if overlaid is not None:
            return overlaid
        spec = (self.model.pic_of(name) or "").upper()
        return 0 if spec and "9" in spec and "X" not in spec else ""

    def _assembled(self, name: str):
        """A group's value is its children's bytes, laid end to end.

        Without this, writing a field and then testing the record it belongs
        to - `MOVE 'AB' TO WS-1` then `IF WS-REC = SPACES` - reads whatever
        the group last held as a whole, so the test answers a question about
        a value nobody wrote.
        """
        key = name if name in self.model.children else base_name(name)
        fields = self._elementary(key) if key in self.model.children else []
        if not fields:
            return None
        if not any(f[0] in self.state for f in fields):
            return None
        width = max(o + n for _c, o, n in fields)
        buffer = [" "] * width
        # A REDEFINES sits on top of bytes another field already owns, so
        # laying the fields out end to end doubles them and the group comes
        # out longer than it is. Offsets, and first writer wins.
        written = [False] * width
        for child, offset, length in fields:
            if self.model.look(self.model.redefines, child):
                continue
            if any(written[offset:offset + length]):
                continue
            value = self.state.get(child)
            if value is None:
                value = self.model.initial.get(child)
            spec = (self.model.pic_of(child) or "").upper()
            if value is None:
                value = 0 if spec and "9" in spec and "X" not in spec else ""
            text = str(value)
            if spec and "9" in spec and "X" not in spec:
                text = text.split(".")[0] if "." in text else text
                text = text.rjust(length, "0")[-length:]
            else:
                text = text.ljust(length)[:length]
            buffer[offset:offset + length] = list(text)
            written[offset:offset + length] = [True] * length
        return "".join(buffer)

    def _width(self, name: str) -> int:
        """Declared byte width, or 0 when the copybook did not say.

        A slice reads *bytes of the field*, not bytes of whatever short string
        happens to be stored: `WS-A(1:5)` of a PIC X(10) holding 'AB' is
        'AB   '. Without the declared width the padding is missing and every
        comparison against SPACES or LOW-VALUES goes the wrong way.
        """
        from .layout import byte_length
        slot = self.slot_of(name)
        if slot is not None:
            return slot.length
        pic = self.model.pic_of(name)
        if not pic:
            return 0
        try:
            return byte_length(pic, self.model.usage_of(name),
                               self.model.look(self.model.sign, name, "") or "")
        except Exception:                                        # noqa: BLE001
            return 0

    def declared_length(self, name: str) -> int:
        """Byte size of a field or of a whole group.

        A group has no PIC, so `_width` returns 0 for it; its size is where
        its last elementary field ends. Every commarea in a pseudo-
        conversational program is sliced at group boundaries computed this
        way, so getting it wrong misplaces the whole saved state.
        """
        slot = self.slot_of(name)
        if slot is not None:
            return slot.length
        fields = self._elementary(name)
        if fields:
            return max(o + n for _c, o, n in fields)
        return self._width(name)

    def _text_of(self, name: str, value) -> str:
        text = "" if value is None else str(value)
        width = self._width(name)
        if width and len(text) < width:
            text = text.ljust(width)
        return text

    def _field_bytes(self, name: str, value) -> str:
        """The bytes a DISPLAY field holds, padded the way its category pads.

        A numeric item is right-justified and zero-filled and an alphanumeric
        one left-justified and space-filled.  Anything that scans a field
        character by character - INSPECT, and any port that serialises a
        record - has to agree with that or it counts the padding of the wrong
        end.
        """
        spec = (self.model.pic_of(name) or "").upper()
        width = self._width(name)
        text = "" if value is None else str(value)
        if spec and "9" in spec and "X" not in spec and "A" not in spec:
            body = text.strip().lstrip("+-")
            body = body.split(".")[0] if "." in body else body
            if not width:
                return body
            return body.rjust(width, "0")[-width:]
        return text.ljust(width)[:width] if width else text

    def _as_int(self, expression: str, default: int) -> int:
        if not expression:
            return default
        # A refmod offset is an arithmetic expression far more often than it
        # is a bare name - `X(LENGTH OF A + 1 : LENGTH OF B)` is the standard
        # way to append one group to another. Parsed as one identifier the
        # whole thing is a variable nobody writes, and the slice silently
        # starts at 1.
        # Split only on a *spaced* operator: COBOL requires a space either
        # side of one, and a hyphen without spaces is part of the name.
        total, sign, ok = 0.0, 1, False
        for piece in re.split(r"\s+([+-])\s+", expression):
            piece = piece.strip()
            if not piece:
                continue
            if piece in ("+", "-"):
                sign = 1 if piece == "+" else -1
                continue
            try:
                value = self.value_of(parse_term(piece))
                total += sign * float(str(value).strip())
                ok = True
            except (TypeError, ValueError):
                return default
            sign = 1
        return int(total) if ok else default

    def _sending_value(self, text: str):
        """The value of an operand that may be a literal *or* an identifier.

        `Term.value` is only ever set for a constant, so any place that reads
        it directly - SET, PERFORM VARYING's FROM and BY - silently stores
        None the moment the program writes a variable there instead of a
        number. None is not a COBOL value: it compares equal to nothing and
        arithmetic on it is skipped, so the loop or the index stops moving.
        """
        term = parse_term(text)
        if term.kind == "const":
            return term.value
        return self.value_of(term)

    def _slice(self, term, value) -> str:
        text = self._text_of(term.name, value)
        start = self._as_int(term.refmod[0], 1)
        if start < 1:
            start = 1
        if term.refmod[1]:
            length = self._as_int(term.refmod[1], len(text))
            return text[start - 1:start - 1 + max(0, length)]
        return text[start - 1:]

    def _intrinsic(self, term):
        """Evaluate an intrinsic function.

        Only the ones whose result a *condition* can turn on are worth having:
        an unevaluated intrinsic is not an approximation, it is a field with
        no value, and every comparison against it goes one fixed way.
        """
        name = term.func
        args = list(term.args)

        def text(i, pad=True):
            if i >= len(args):
                return ""
            a = args[i]
            value = self.value_of(a)
            if pad and a.kind == "var" and not a.refmod and not a.func:
                return self._text_of(a.name, value)
            return "" if value is None else str(value)

        def number(i, default=0.0):
            try:
                return float(str(self.value_of(args[i])).strip())
            except (TypeError, ValueError, IndexError):
                return default

        if name == "TRIM":
            how = (args[1].name.upper() if len(args) > 1 and args[1].kind == "var"
                   else "")
            body = text(0)
            if how == "LEADING":
                return body.lstrip()
            if how == "TRAILING":
                return body.rstrip()
            return body.strip()
        if name == "UPPER-CASE":
            return text(0).upper()
        if name == "LOWER-CASE":
            return text(0).lower()
        if name == "LENGTH":
            if args and args[0].kind == "var" and not args[0].refmod \
                    and not args[0].func:
                width = self._width(args[0].name)
                if width:
                    return width
                # A group has no PIC of its own; its length is where its last
                # field ends. Falling back to the length of the *value* makes
                # `LENGTH OF <commarea>` mean "however much happens to be in
                # it", which is a different number on every run.
                fields = self._elementary(args[0].name)
                if fields:
                    return max(offset + size for _n, offset, size in fields)
            return len(text(0))
        if name in ("NUMVAL", "NUMVAL-C"):
            return _numval(text(0))
        if name in ("TEST-NUMVAL", "TEST-NUMVAL-C"):
            return _test_numval(text(0))
        if name == "MOD":
            b = number(1, 1.0) or 1.0
            return number(0) - b * (number(0) // b)
        if name == "REM":
            b = number(1, 1.0) or 1.0
            return number(0) - b * int(number(0) / b)
        if name == "INTEGER":
            return int(number(0) // 1)
        if name == "MAX":
            return max((number(i) for i in range(len(args))), default=0)
        if name == "MIN":
            return min((number(i) for i in range(len(args))), default=0)
        if name in ("CURRENT-DATE", "WHEN-COMPILED"):
            # Determinism is an invariant here, so the clock is never read.
            # "now" is a *knob* rather than a constant: a program that rolls
            # a month over at the year end has a direction that only a
            # December date reaches, and pinning one instant puts that
            # direction permanently out of reach. The harness sets it like
            # any other input, and falls back to one fixed instant.
            return self.state.get(CLOCK_SLOT, FIXED_NOW)
        if name == "INTEGER-OF-DATE":
            return _integer_of_date(int(number(0)))
        if name == "DATE-OF-INTEGER":
            return _date_of_integer(int(number(0)))
        if name == "REVERSE":
            return text(0)[::-1]
        if name == "ORD":
            body = text(0)
            return ord(body[0]) + 1 if body else 0
        if name == "CHAR":
            return chr(max(0, int(number(0)) - 1) % 256)
        # Unknown intrinsic: fall back to the first argument, which at least
        # keeps a comparison against a real value rather than against nothing.
        return self.value_of(args[0]) if args else ""

    def evaluate(self, condition: str) -> bool:
        text = norm(condition)
        if not text:
            return True
        for alternative in condition_atoms(text, names=self._names88):
            if not alternative:
                continue
            if all(self._atom(a) for a in alternative):
                return True
        return False

    def _atom(self, atom) -> bool:
        lhs, rhs = atom.lhs, atom.rhs
        # `IF WS-A + WS-B > 10` compares an expression, and a term parser can
        # only see one operand. Left alone the whole left side becomes a field
        # nobody declared, so the comparison is decided on a default.
        if self._is_expression(lhs) or self._is_expression(rhs):
            return holds(self._side_value(lhs), atom.op, self._side_value(rhs))
        if rhs.kind == "const" and rhs.value is True and lhs.kind == "var":
            entry = self.model.condition_names.get(lhs.name)
            if entry:
                parent, values = entry
                actual = self.value_of(parse_term(parent))
                truth = any(holds(actual, "=", parse_term(v).value) for v in values)
                return truth if atom.op == "=" else not truth
        return holds(self.value_of(lhs), atom.op, self.value_of(rhs))

    @staticmethod
    def _is_expression(term) -> bool:
        return (term.kind == "var" and not term.func and not term.refmod
                and not term.index and is_arithmetic(term.name))

    def _side_value(self, term):
        if self._is_expression(term):
            try:
                return self.number_of(term.name)
            except (TypeError, ValueError, ZeroDivisionError):
                return 0.0
        return self.value_of(term)

    def _elementary(self, group: str) -> list:
        """The elementary fields of a group, with offset and width.

        Cached: a group move happens thousands of times in a run and the
        layout is a property of the declaration, not of the state.
        """
        if group in self._layouts:
            return self._layouts[group]
        fields: list = []
        if self.model.descendants(group):
            from .layout import record_layout
            try:
                fields = [(f.name, f.offset, f.length)
                          for f in record_layout(self.model, group)
                          if f.length and not self.model.descendants(f.name)]
            except Exception:                                    # noqa: BLE001
                fields = []
        self._layouts[group] = fields
        return fields

    def _overlay_map(self) -> dict:
        """field -> the fields that share its bytes, both directions."""
        pairs: dict = {}
        for name, over in (self.model.redefines or {}).items():
            pairs.setdefault(name.upper(), set()).add(over.upper())
            pairs.setdefault(over.upper(), set()).add(name.upper())
        return {k: sorted(v) for k, v in pairs.items()}

    def _reinterpret(self, value, target: str):
        """One field's value read through another field's PIC.

        Only the same-width elementary case, and only DISPLAY. A packed or
        binary overlay is a different byte pattern entirely and guessing at
        it would be worse than leaving it alone - which is the whole reason
        the complete fix wants a byte-level store rather than this.
        """
        spec = (self.model.pic_of(target) or "").upper()
        if not spec:
            return None
        text = "" if value is None else str(value)
        if "9" in spec and "X" not in spec and "A" not in spec:
            stripped = text.strip()
            if stripped and stripped.lstrip("+-").isdigit():
                return int(stripped)
            return 0
        return text

    def _alias(self, name: str, value) -> None:
        """Writing one name writes every name over the same bytes.

        `IF CC-ACCT-ID IS NUMERIC` passes on '11111111111' while
        `CC-ACCT-ID-N REDEFINES CC-ACCT-ID` reads 0, because the two names
        were separate cells. That is the CICS validation idiom, and without
        aliasing every check built on it decides on a value the program
        never had.
        """
        for other in self._overlays.get(name, ()):
            if other == name:
                continue
            if self._width(name) != self._width(other):
                continue           # a partial overlay needs real bytes
            fresh = self._reinterpret(value, other)
            if fresh is not None:
                self.state[other] = fresh

    def _read_overlay(self, name: str):
        """Read through the overlay when this name has no value of its own.

        The write side alone is not enough: `01 WS-A PIC X(4) VALUE '1234'`
        with `01 WS-B REDEFINES WS-A PIC 9(4)` never assigns anything, and
        WS-B still has to read 1234 - the bytes were laid down by the VALUE
        clause.
        """
        for other in self._overlays.get(name, ()):
            if self._width(name) != self._width(other):
                continue
            raw = self.state.get(other)
            if raw is None:
                raw = self.model.look(self.model.initial, other)
            if raw is None:
                continue
            return self._reinterpret(raw, name)
        return None

    def assign_slice(self, term, value) -> None:
        """``MOVE A TO B(start:length)`` - replace those bytes of B, keep the rest.

        The receiving item is the *slice*, so the move is alphanumeric and
        left-aligned within it, and everything outside it is untouched. This
        is how a pseudo-conversational commarea is built: the shared header
        goes to `WS-COMMAREA`, then the program's own area is appended at
        `LENGTH OF header + 1`. Writing the whole of B for the second MOVE
        throws the header away, which is precisely the state the next task
        branches on.
        """
        name = term.name.upper()
        if name in self._pinned:
            return
        index = self._indices(term)
        slot = self.slot_of(name)
        if slot is not None:
            # The receiving item is the slice, so this is a byte splice and
            # nothing outside it moves - including the bytes of a packed or
            # binary neighbour that happens to share the group.
            start = max(1, self._as_int(term.refmod[0], 1))
            text = "" if value is None else str(value)
            length = (self._as_int(term.refmod[1], len(text))
                      if term.refmod[1] else len(text))
            if length <= 0:
                return
            from .storage import CODEC
            piece = text[:length].ljust(length).encode(CODEC, "replace")
            raw = bytearray(self.memory.raw(slot, index))
            end = start - 1 + length
            if end > len(raw):
                piece = piece[:max(0, len(raw) - (start - 1))]
                end = len(raw)
            raw[start - 1:end] = piece
            self.memory.write_raw(slot, bytes(raw), index)
            self._note(name, None)
            return
        width = self.declared_length(name)
        current = self._text_of(name, self._stored(name))
        if width and len(current) < width:
            current = current.ljust(width)
        start = max(1, self._as_int(term.refmod[0], 1))
        text = "" if value is None else str(value)
        length = self._as_int(term.refmod[1], len(text)) if term.refmod[1] \
            else len(text)
        if length <= 0:
            return
        piece = text[:length].ljust(length)
        end = start - 1 + length
        if len(current) < end:
            current = current.ljust(end)
        updated = current[:start - 1] + piece + current[end:]
        self.assign(name, updated)

    def _fit(self, name: str, value):
        """Store a value the way the receiving field actually holds it.

        COBOL truncates on *both* kinds of MOVE and in opposite directions:
        an alphanumeric field is left-aligned, so the tail is lost, while a
        numeric one aligns on the decimal point, so the high-order digits go
        and `MOVE 12345 TO PIC 9(2)` leaves 45. A port that treats a field as
        a string or an int loses one of those two, silently, and the
        difference only surfaces as a branch going the other way.

        This is a parity tool, so getting it wrong here is not a rounding
        error - it is the class of defect the tool exists to find.
        """
        spec = (self.model.pic_of(name) or "").upper()
        if not spec or value is None or isinstance(value, bool):
            return value
        m = re.search(r"[XA9]\((\d+)\)", spec)
        width = int(m.group(1)) if m else len(re.sub(r"[^XA9]", "", spec))
        if not width:
            return value
        if "X" in spec or "A" in spec:
            text = value if isinstance(value, str) else str(value)
            # JUSTIFIED RIGHT aligns on the receiver's right-hand end: the
            # padding goes in front and an over-long sending item loses its
            # left characters, both the opposite way round from the default.
            if name.upper() in getattr(self.model, "justified", ()):
                return text[-width:] if len(text) > width else text.rjust(width)
            return text[:width] if len(text) > width else text
        if isinstance(value, str) and not value.strip().lstrip("+-").isdigit():
            return value                     # not a number; leave it alone
        try:
            number = int(str(value).strip())
        except (TypeError, ValueError):
            return value
        digits = width - _decimals(spec)
        if digits <= 0:
            return number
        limit = 10 ** digits
        kept = abs(number) % limit
        return -kept if number < 0 else kept

    # -- where a value came from -------------------------------------------
    def _origin_of_name(self, name: str):
        """The entry bytes this field still holds, or None for opaque."""
        name = (name or "").upper()
        if not name:
            return None
        if name in self._origin:
            return self._origin[name]
        kids = self.model.descendants(name)
        if kids and any(child in self._origin for child in kids):
            # The group was never written but a child was, so reading it
            # assembles bytes the entry state no longer decides. Claiming the
            # whole group is still an input would send the search after a
            # value that cannot arrive.
            return None
        from .origins import Origin
        return Origin(name, 0, None)

    def origin_of(self, term):
        """The entry bytes a *term* evaluates to, reference modification and
        all. A function of its arguments is opaque: nothing about the entry
        state survives `FUNCTION TRIM`, and pretending otherwise proposes a
        value that the intrinsic will not reproduce."""
        if not self.track_origins:
            return None
        if term.kind == "const" or term.func or term.index:
            return None
        origin = self._origin_of_name(term.name)
        if origin is None or not term.refmod:
            return origin
        start = self._as_int(term.refmod[0], 1) - 1
        if start < 0:
            return None
        if term.refmod[1]:
            length = self._as_int(term.refmod[1], -1)
            # An unevaluable length reads to the end of the text, which is
            # what `_slice` does; the origin has to agree with it or the
            # bytes the search writes are not the bytes the run reads.
            if length >= 0:
                return origin.slice(start, start + length)
        return origin.slice(start, None)

    def _origins(self, condition: str) -> dict:
        if not self.track_origins:
            return {}
        out: dict = {}
        for alternative in condition_atoms(condition,
                                           names=self._names88):
            for atom in alternative:
                for term in (atom.lhs, atom.rhs):
                    if term.kind != "var":
                        continue
                    out[term.key] = self.origin_of(term)
                    # A bare 88-level names its parent's value, so the byte
                    # range that matters belongs to the parent and the atom
                    # carries only the condition-name.
                    entry = self.model.condition_names.get(term.name)
                    if entry:
                        out[entry[0]] = self._origin_of_name(entry[0])
        return out

    def _note(self, name: str, origin) -> None:
        if self.track_origins:
            self._origin[name.upper()] = origin

    def assign(self, name: str, value, origin=None, index: tuple = (),
               fill: str = "") -> None:
        name = name.upper()
        # Values the plan pins are the stub returns and program inputs; the
        # program overwriting them mid-run would undo the very thing being
        # tested, so they hold.
        if name in self._pinned:
            return
        slot = self.slot_of(name)
        if slot is not None:
            # One write, into the bytes the name describes. Truncation, the
            # sign, the packed or binary representation and every overlapping
            # name fall out of the layout instead of being reproduced here.
            self.memory.write(slot, value, index, fill)
            self._note(name, origin)
            if self.track_origins and slot.category == "group":
                # A group move hands each child a different piece of the
                # source, so each child inherits a different piece of the
                # source's origin.
                for child, offset, length in self._elementary(name):
                    self._note(child, origin.slice(offset, offset + length)
                               if origin is not None else None)
            return
        self.state[name] = self._fit(name, value)
        self._note(name, origin)
        fields = self._elementary(name)
        if not fields:
            for child in self.model.descendants(name):
                if child not in self._pinned:
                    self.state[child] = value
                    self._note(child, origin)
            return
        # A group move copies *bytes*, so each child gets the piece of the
        # source that lands on it. Handing every child the whole value makes
        # `MOVE FUNCTION CURRENT-DATE TO WS-DATE` leave the month field
        # holding the entire timestamp, and every test on it then compares a
        # 21-character string against a number.
        text = "" if value is None else str(value)
        width = fields[-1][1] + fields[-1][2]
        text = text.ljust(width) if len(text) < width else text
        for child, offset, length in fields:
            if child in self._pinned:
                continue
            piece = text[offset:offset + length]
            # A group move hands each child a different piece of the source,
            # so each child inherits a different piece of the source's
            # origin. This is the step that carries an obligation on a field
            # inside a commarea back to a byte range of the commarea itself.
            self._note(child, origin.slice(offset, offset + length)
                       if origin is not None else None)
            spec = (self.model.pic_of(child) or "").upper()
            if spec and "9" in spec and "X" not in spec:
                try:
                    self.state[child] = int(piece)
                except (TypeError, ValueError):
                    self.state[child] = piece
            else:
                self.state[child] = piece

    # -- execution ---------------------------------------------------------
    def run(self, entry: str) -> Trace:
        start = self._names.index(entry.upper()) if entry.upper() in self._names else 0
        for task in range(MAX_TASKS):
            if self._one_task(start, task) is not True:
                break
        return self.trace

    def _one_task(self, start: int, task: int) -> bool:
        """Run one CICS task. True when another one follows."""
        # A re-entered transaction arrives with a commarea, and every
        # program worth the name branches on whether it has one. Leaving
        # EIBCALEN at its first-task value makes every re-entry look like a
        # first entry, so the whole re-entry half of the program stays dark.
        if task:
            saved = getattr(self, "_commarea", "")
            if saved:
                value = self._stored(saved)
                if value is not None:
                    self.state["DFHCOMMAREA"] = value
                    self._note("DFHCOMMAREA", None)
                if "EIBCALEN" not in self._pinned:
                    self.state["EIBCALEN"] = self._width(saved) or 100
                    self._note("EIBCALEN", None)
            elif "EIBCALEN" not in self._pinned:
                self.state["EIBCALEN"] = 100
                self._note("EIBCALEN", None)
        index = start
        while 0 <= index < len(self._names):
            para = self.program.paragraphs[index]
            try:
                self.perform(para["name"], depth=0)
            except _NextTask:
                return True
            except _Stop:
                if not self.trace.stopped:
                    self.trace.stopped = ("runaway loop in %s" % self.trace.runaway
                                          if self.trace.runaway
                                          else "STOP RUN / GOBACK")
                return False
            except _Goto as jump:
                if jump.target in self._names:
                    index = self._names.index(jump.target)
                    continue
                return False
            except RecursionError:
                self.trace.stopped = "recursion limit"
                return False
            if not self.sequential:
                return False
            index += 1
        return False

    def _tick(self, name: str) -> None:
        """Notice a paragraph running away.

        Burning the whole step budget and reporting "not reached" hides the
        actual finding, which is that one paragraph ran thousands of times -
        usually a read loop with no end-of-file, or an abend handler that
        returns. Naming it turns a timeout into a diagnosis.
        """
        self._visits[name] = self._visits.get(name, 0) + 1
        if self._visits[name] > RUNAWAY:
            self.trace.runaway = name
            raise _Stop()

    def perform(self, spec: str, depth: int) -> None:
        """Run one paragraph, or a THRU range.

        ``PERFORM A THRU B`` runs every paragraph from A to B in source
        order - fall-through inside the range included.  Treating it as
        ``PERFORM A`` silently skips the middle of the range, which is
        where the interesting code usually is.
        """
        if depth > MAX_DEPTH:
            return
        start, _, end = spec.partition(" THRU ")
        start, end = start.strip().upper(), end.strip().upper()
        if not end or end not in self._names or start not in self._names:
            para = self.program.paragraph(start)
            if para is None:
                return
            self.trace.entered.append(start)
            self._tick(start)
            try:
                self.block(para.get("statements", []), para["name"], depth)
            except _ExitParagraph:
                pass
            return

        first, last = self._names.index(start), self._names.index(end)
        if last < first:
            first, last = last, first
        index = first
        while first <= index <= last:
            para = self.program.paragraphs[index]
            self.trace.entered.append(para["name"])
            self._tick(para["name"])
            try:
                try:
                    self.block(para.get("statements", []), para["name"], depth)
                except _ExitParagraph:
                    pass
            except _Goto as jump:
                # A jump inside the range keeps the PERFORM alive; one that
                # leaves the range propagates out of it.
                if jump.target in self._names:
                    landing = self._names.index(jump.target)
                    if first <= landing <= last:
                        index = landing
                        continue
                raise
            index += 1

    def block(self, statements, para: str, depth: int) -> None:
        for stmt in statements:
            self.step(stmt, para, depth)

    def step(self, stmt, para: str, depth: int) -> None:
        self.trace.steps += 1
        if self.trace.steps > MAX_STEPS:
            raise _Stop()
        kind = stmt.get("type", "")
        attrs = stmt.get("attributes", {})
        line = stmt.get("line_start", 0)
        ordinal = stmt.get("ordinal", -1)
        children = stmt.get("children") or []

        if kind == "IF":
            condition = attrs.get("condition", "")
            result = self.evaluate(condition)
            self.trace.guards.append(GuardEvent(para, line, "IF", condition, result,
                                                self._snapshot(condition), ordinal,
                                                self._origins(condition)))
            branch = [c for c in children if c.get("type") != "ELSE"]
            other = [c for c in children if c.get("type") == "ELSE"]
            if result:
                self.block(branch, para, depth)
            elif other:
                self.block(other[0].get("children") or [], para, depth)
            return

        if kind == "EVALUATE":
            subject = attrs.get("subject", "")
            arms = [c for c in children if c.get("type") == "WHEN"]
            for arm in arms:
                value = norm(arm.get("attributes", {}).get("value", ""))
                if value.upper() in ("OTHER", "ANY"):
                    continue
                condition = when_condition(subject, value)
                result = self.evaluate(condition)
                if norm(subject).upper() == "FALSE":
                    result = not result
                self.trace.guards.append(
                    GuardEvent(para, arm.get("line_start", line), "WHEN",
                               condition, result, self._snapshot(condition),
                               arm.get("ordinal", -1), self._origins(condition)))
                if result:
                    # An earlier arm matching is exactly how WHEN OTHER goes
                    # the other way. Without recording it, OTHER only ever
                    # reports True and its False direction is uncoverable by
                    # construction - it sits in the denominator for good.
                    for rest in arms:
                        if norm(rest.get("attributes", {}).get("value", "")
                                ).upper() in ("OTHER", "ANY"):
                            self.trace.guards.append(
                                GuardEvent(para, rest.get("line_start", line),
                                           "WHEN", "OTHER", False, {},
                                           rest.get("ordinal", -1)))
                    self.block(arm.get("children") or [], para, depth)
                    return
            for arm in arms:
                if norm(arm.get("attributes", {}).get("value", "")).upper() in ("OTHER", "ANY"):
                    self.trace.guards.append(
                        GuardEvent(para, arm.get("line_start", line), "WHEN",
                                   "OTHER", True, {}, arm.get("ordinal", -1)))
                    self.block(arm.get("children") or [], para, depth)
                    return
            return

        if kind == "PERFORM":
            target = (attrs.get("target") or "").strip()
            condition = attrs.get("condition")
            if condition and children:
                self._loop(condition, children, para, depth, line, ordinal,
                           bool(attrs.get("test_after")))
                return
            # An out-of-line loop has no inline body; its body is the target.
            # `_varying`, `_times` and `_loop` are all correct already and
            # were simply never reached from here, so the induction variable
            # of `PERFORM A VARYING I FROM 1 BY 1 UNTIL I > 3` was never
            # initialised or stepped and the body ran zero times.
            body = ([{"type": "PERFORM", "text": "PERFORM " + target,
                      "line_start": line, "line_end": line,
                      "attributes": {"target": target}, "children": []}]
                    if target else [])
            varying = attrs.get("varying")
            if varying and body:
                self._varying(varying, body, para, depth, line, ordinal)
                return
            times = attrs.get("times")
            if times and body:
                self._times(times, body, para, depth, line, ordinal)
                return
            if condition:
                if body:
                    self._loop(condition, body, para, depth, line, ordinal,
                               bool(attrs.get("test_after")))
                    return
                count = 0
                while not self.evaluate(condition) and count < MAX_LOOP:
                    self.perform(target, depth + 1)
                    count += 1
                self.trace.guards.append(GuardEvent(para, line, "PERFORM_UNTIL",
                                                    condition, count > 0, {},
                                                    ordinal,
                                                    self._origins(condition)))
                return
            if target:
                self.perform(target, depth + 1)
            return

        if kind == "PERFORM_INLINE":
            varying = attrs.get("varying")
            if varying:
                self._varying(varying, children, para, depth, line, ordinal)
                return
            condition = attrs.get("condition")
            if condition:
                self._loop(condition, children, para, depth, line, ordinal,
                           bool(attrs.get("test_after")))
                return
            times = attrs.get("times")
            if times:
                self._times(times, children, para, depth, line, ordinal)
                return
            self._cycle(children, para, depth)
            return

        if kind in ("GO_TO", "GOTO"):
            target = self.altered.get(para) or attrs.get("target")
            # `GO TO L1 L2 L3 DEPENDING ON K` selects the K-th label,
            # one-based, and falls through when K is outside the list.
            # Always taking the first turns an n-way switch into an
            # unconditional branch.
            if attrs.get("depending") and not self.altered.get(para):
                labels = attrs.get("targets") or []
                try:
                    index = int(float(str(self.value_of(
                        parse_term(attrs.get("selector", "")))).strip()))
                except (TypeError, ValueError):
                    index = 0
                if 1 <= index <= len(labels):
                    raise _Goto(labels[index - 1].upper())
                return                       # out of range: fall through
            if target:
                raise _Goto(target.upper())
            return

        if kind == "EXIT_PARAGRAPH":
            raise _ExitParagraph()

        if kind == "EXIT_PERFORM":
            raise _ExitPerform()

        if kind == "EXIT_PERFORM_CYCLE":
            raise _ExitPerformCycle()

        if kind == "ALTER":
            altered, destination = attrs.get("altered"), attrs.get("destination")
            if altered and destination:
                self.altered[altered.upper()] = destination.upper()
            return

        if kind in ("GOBACK", "STOP"):
            raise _Stop()

        if kind == "MOVE":
            source = parse_term(attrs.get("source", ""))
            from .ir import move_targets
            # `MOVE DFHCOMMAREA(1:EIBCALEN) TO <commarea>` on re-entry is the
            # program taking back the state it saved at RETURN. Modelled as an
            # ordinary group move it copies an empty linkage area over that
            # state and clears the re-entry flag, so every task believes it is
            # the first - which is why a screen program appears to have an
            # unreachable second half. The contents are carried across the
            # task boundary as fields, because that is what they are here:
            # the group itself holds no bytes of its own.
            if source.name == "DFHCOMMAREA":
                # `_carried is None` means no task has returned yet, so this
                # is the first task and the commarea is *caller* input -
                # whatever program transferred control here staged it. That
                # makes this the same input boundary a RECEIVE is for the
                # map: the linkage area itself is an anonymous byte array
                # the entry state cannot usefully address, so the fields the
                # entry state *named inside the receiving area* stand for
                # the staged bytes - the ordinary move runs, then those
                # fields are re-delivered over it. Fields the entry never
                # named keep what the move left, so a run that supplies
                # nothing still models an empty commarea.
                #
                # On a re-entered task the commarea belongs to the previous
                # cycle, never to the entry state - the second cycle earns
                # its state from the first - so the bytes the RETURN saved
                # are moved (`_one_task` staged them under DFHCOMMAREA; the
                # refmod arithmetic in `MOVE DFHCOMMAREA(LENGTH OF A + 1:
                # ...)` runs against them, which matters when the saved area
                # is a childless PIC X(n) the program assembles by slices),
                # and the carried fields overlay them for the names whose
                # state-dict values are finer than their bytes. From here on
                # the program owns every one of them (nothing is pinned).
                carried = getattr(self, "_carried", None)
                value = self.value_of(source)
                for name in move_targets(attrs.get("targets", "")):
                    self.assign(name, value, self.origin_of(source))
                    if carried is None:
                        self._deliver_entry_fields(name)
                for child, kept in (carried or {}).items():
                    if child not in self._pinned:
                        self.state[child] = kept
                        self._note(child, None)
                return
            value = self.value_of(source)
            origin = self.origin_of(source)
            fill = _fill_char(attrs.get("source", ""))
            # `MOVE A TO B(n:m)` replaces m bytes of B and leaves the rest
            # alone. Assigning the whole of B is how a commarea assembled in
            # two pieces - header, then the program's own area at
            # `LENGTH OF header + 1` - ends up holding only the second one.
            from .ir import move_target_terms
            terms = move_target_terms(attrs.get("targets", ""))
            if not terms:
                for name in move_targets(attrs.get("targets", "")):
                    self.assign(name, value, origin, fill=fill)
                return
            for term in terms:
                if term.refmod:
                    self.assign_slice(term, value)
                else:
                    self.assign(term.name, value, origin,
                                self._indices(term), fill)
            return

        if kind == "SET":
            names = attrs.get("names") or ([attrs.get("name")]
                                           if attrs.get("name") else [])
            raw = attrs.get("value")
            direction = attrs.get("direction")
            if names and direction:
                # `SET IX UP BY 2` steps the index. Ignored, the index keeps
                # the occurrence the last SET or SEARCH left it at, so every
                # reference through it reads that one entry for the rest of
                # the run.
                step = self._operand_number(attrs.get("amount") or "1")
                for name in names:
                    current = self._operand_number(name)
                    self.assign(name, int(current
                                          + (step if direction == "UP" else -step)))
                return
            if names and raw:
                for name in names:
                    entry = self.model.condition_names.get(name.upper())
                    if entry and raw.upper() == "TRUE":
                        parent, values = entry
                        if values:
                            self.assign(parent, parse_term(values[0]).value)
                        continue
                    # The sending operand is an identifier as often as it is a
                    # literal - `SET IX TO WS-SAVED-IX`, `SET WS-N TO IX`.
                    # Reading only `Term.value` stores None for every one of
                    # those, and a field holding None compares equal to
                    # nothing the program ever tests.
                    self.assign(name, self._sending_value(raw))
            return

        # A conditional phrase belongs to more than the I/O verbs: `ADD ... ON
        # SIZE ERROR` and `STRING ... ON OVERFLOW` are decisions in the same
        # sense, they are already counted as branch directions, and running
        # the statement without them left both directions uncoverable.
        if kind in ("ADD", "SUBTRACT", "COMPUTE", "MULTIPLY", "DIVIDE"):
            self._arithmetic(kind, stmt)
            self._maybe_phrases(stmt, children, para, depth, line, ordinal)
            return

        if kind == "INITIALIZE":
            self._initialize(stmt)
            return

        if kind == "STRING":
            self._string(stmt)
            self._maybe_phrases(stmt, children, para, depth, line, ordinal)
            return

        if kind == "UNSTRING":
            self._unstring(stmt)
            self._maybe_phrases(stmt, children, para, depth, line, ordinal)
            return

        if kind == "INSPECT":
            self._inspect(stmt)
            return

        if kind == "SEARCH":
            self._search(stmt, para, depth, line)
            return

        from .provenance import STUB_KINDS, op_key
        if kind in STUB_KINDS:
            self._record_transfer(kind, stmt, before=True)
            self._external(stmt, para, line)
            self._record_transfer(kind, stmt, before=False)
            if children and any(c.get("type") == "PHRASE" for c in children):
                self._phrases(stmt, children, para, depth, line, ordinal)
            elif children:
                self.block(children, para, depth)
            return

        if children:
            self.block(children, para, depth)

    # File status values that mean "no record": end-of-file for a sequential
    # read, not-found for a keyed one. These are the codes the standard fixes,
    # not a guess.
    _AT_END = {"10", "46", 10, 46}
    _INVALID_KEY = {"21", "22", "23", "24", 21, 22, 23, 24}

    # Whether the statement that just ran raised its exception condition -
    # size error, overflow. None means "no model", which is what every verb
    # without one leaves behind.
    _raised = None

    def _too_wide(self, name: str, value) -> bool:
        """Does an arithmetic result have more integer digits than fit?"""
        from .layout import digits_of
        text = (name or "").strip()
        if not text:
            return False
        term = parse_term(text)
        base = term.name if term.kind == "var" else text.split("(")[0].strip()
        spec = (self.model.pic_of(base) or "").upper()
        if not spec or "X" in spec or "A" in spec:
            return False
        try:
            whole, _decimals = digits_of(spec)
            return whole > 0 and abs(float(value)) >= 10 ** whole
        except (TypeError, ValueError):
            return False

    def _maybe_phrases(self, stmt, children, para: str, depth: int, line: int,
                       ordinal: int) -> None:
        if children and any(c.get("type") == "PHRASE" for c in children):
            self._phrases(stmt, children, para, depth, line, ordinal)
        else:
            self._raised = None

    def _phrases(self, stmt, children, para: str, depth: int, line: int,
                 ordinal: int) -> None:
        """Run the handler the operation's outcome selects, and only that one.

        `AT END` is a decision, and running its body unconditionally is how a
        read loop sets end-of-file on its first pass and skips everything it
        was written to do. It is recorded as a guard so it counts as a branch
        direction like any other - it is one.
        """
        from .provenance import op_key
        key = op_key(norm(stmt.get("text", "")))
        status = ""
        if ":" in key:
            status = self.model.file_status.get(key.rsplit(":", 1)[-1], "")
        value = self._stored(status) if status else None
        at_end = value in self._AT_END
        invalid = value in self._INVALID_KEY
        raised, self._raised = self._raised, None
        for arm in children:
            if arm.get("type") != "PHRASE":
                continue
            phrase = arm.get("attributes", {}).get("phrase", "")
            if phrase in ("at_end", "not_at_end"):
                taken = at_end if phrase == "at_end" else not at_end
            elif phrase in ("invalid_key", "not_invalid_key"):
                taken = invalid if phrase == "invalid_key" else not invalid
            elif raised is not None and ("size_error" in phrase
                                         or "overflow" in phrase):
                # The verb that just ran said whether the condition fired:
                # a result too wide for its receiver, or a STRING that ran off
                # the end of one. Both are decisions the program takes, and
                # both used to be settled in favour of the quiet arm.
                taken = raised if not phrase.startswith("not_") else not raised
            else:
                # EXCEPTION and anything else the interpreter has no model of:
                # the non-error arm is the one taken and the error arm is
                # reported as unmodelled rather than quietly run.
                taken = phrase.startswith("not_")
                if not taken and "%s:%s" % (para, phrase) not in self.trace.approximations:
                    self.trace.approximations.append("%s:%s" % (para, phrase))
            self.trace.guards.append(
                GuardEvent(para, arm.get("line_start", line), "PHRASE",
                           phrase, taken, {}, arm.get("ordinal", -1)))
            if taken:
                self.block(arm.get("children") or [], para, depth)

    # A terminal read is an INPUT channel, and the source says so: the
    # command names the area it fills. `EXEC CICS RECEIVE MAP(m) INTO(a)`
    # puts the operator's keystrokes into `a` - so a field under `a` is a
    # program input that arrives *at the RECEIVE*, not at entry.
    #
    # This matters because a screen program clears its own map area before
    # sending, and on a BMS layout the output map REDEFINES the input map, so
    # the clear lands on the very bytes the operator's input will occupy.
    # Deliver nothing here and every field the next screen validates reads as
    # LOW-VALUES however the harness was set up, and every arm behind it is
    # unreachable. It looked reachable before only because two names over one
    # set of bytes were two separate cells, which the compiler says they are
    # not.
    _INPUT_OPS = ("EXEC:CICS:RECEIVE",)

    def _deliver_entry_fields(self, area: str) -> None:
        """Re-deliver the entry-named fields of one receiving area.

        Only names the entry state explicitly spoke about: everything else
        keeps what the program's own move just left there, so the area is
        exactly "what the caller staged" and nothing more.
        """
        for name in [area] + list(self.model.descendants(area)):
            if name in self._entry_names and name not in self._pinned:
                self.state[name] = self._supplied[name]
                self._note(name, None)

    def _deliver_terminal_input(self, key: str, stmt) -> None:
        if not key.startswith(self._INPUT_OPS):
            return
        from .origins import Origin
        from .provenance import stub_outputs
        for area in stub_outputs(norm(stmt.get("text", ""))):
            names = [area] + list(self.model.descendants(area))
            for name in names:
                if name in self._supplied_slots or name in self._supplied.extra:
                    self.state[name] = self._supplied[name]
                    # The value delivered here *is* the entry state's value
                    # for this field, re-arriving at the RECEIVE - so the
                    # entry state still decides it, and the origin says so.
                    # Noting None instead made every screen field opaque to
                    # the frontier search on exactly the routes where the
                    # harness could set it: a guard on re-received operator
                    # input was unliftable by construction.
                    self._note(name, Origin(name, 0, None))

    _WRITE_FROM = re.compile(r"^(?:WRITE|REWRITE|RELEASE)\s+(\S+)\s+FROM\s+"
                             r"([A-Z0-9][A-Z0-9-]*(?:\s*\([^)]*\))?)", re.I)

    def _record_transfer(self, kind: str, stmt, before: bool) -> None:
        """The implicit MOVE that `WRITE ... FROM` carries.

        `WRITE rec FROM ws` moves the working copy into the record area and
        then writes it, which is how a program keeps the two apart. Dropped,
        the record area still holds whatever it held before, so a program
        that inspects it - or a REDEFINES over it - sees the previous record.

        The other half, `READ ... INTO`, is deliberately not done here: the
        read stub already delivers its payload straight to the INTO target
        (`sequences.read_targets`), and moving the record area over it
        afterwards would overwrite the record the world just supplied.
        """
        if not before or kind not in ("WRITE", "REWRITE", "RELEASE"):
            return
        m = self._WRITE_FROM.match(norm(stmt.get("text", "")))
        if m:
            self.assign(m.group(1), self._sending_value(m.group(2)))

    def _external(self, stmt, para: str, line: int) -> None:
        """Deliver the planned outcome for one external operation."""
        from .provenance import op_key
        key = op_key(norm(stmt.get("text", "")))
        self.calls[key] = self.calls.get(key, 0) + 1
        if key.startswith("CALL:") and key[5:] in TERMINATING_CALLS:
            self.trace.stopped = "terminated by %s" % key[5:]
            raise _Stop()
        if key in TERMINATING_EXECS:
            # RETURN *with* TRANSID re-invokes the transaction; RETURN
            # without one hands control back for good.
            if key == "EXEC:CICS:RETURN" and _RETURN_TRANSID.search(
                    stmt.get("text", "") or ""):
                # What this task returns as its commarea is literally what
                # the next task receives in DFHCOMMAREA. Without the handoff
                # the re-entered program copies an empty DFHCOMMAREA over its
                # own state and resets the very flag that tells it this is a
                # re-entry - so every task looks like the first one and the
                # whole second half of the program stays dark.
                m = _RETURN_COMMAREA.search(stmt.get("text", "") or "")
                if m:
                    self._commarea = m.group(1).upper()
                    kept = {}
                    for child in self.model.descendants(self._commarea):
                        if child in self.state:
                            kept[child] = self.state[child]
                    self._carried = kept
                else:
                    # A RETURN with no COMMAREA still re-enters, with
                    # nothing carried. `None` is reserved for "no task has
                    # returned yet" - the first-task commarea is caller
                    # input, a re-entered one never is.
                    self._carried = {}
                raise _NextTask()
            self.trace.stopped = "terminated by %s" % key
            raise _Stop()
        self._deliver_terminal_input(key, stmt)
        entries = self.stubs.get(key, [])
        selectors = self._selectors_of(stmt)

        def wanted(entry) -> bool:
            for k, v in (entry.get("when") or {}).items():
                k = k.upper()
                # Two kinds of discriminator arrive here under one name. A
                # field set before the call is read from the state; a clause
                # the command itself names - `MAP('...')`, `DATASET(...)` -
                # is a property of *this statement* and there is no field by
                # that name to read. Looked up as a field it came back empty,
                # so no entry ever matched and every outcome the ladder
                # derived for a CICS command was silently replaced by the
                # default. That is invisible from the plan, which looks
                # perfectly well formed.
                here = selectors[k] if k in selectors else self.value_of(
                    parse_term(k))
                if not holds(here, "=", v):
                    return False
            return True

        matched = any(wanted(entry) for entry in entries)
        if not matched:
            for name, value in self.defaults.get(key, {}).items():
                self._force(name, value)
            return
        for index, entry in enumerate(entries):
            if not wanted(entry):
                continue
            if self._delivered.get((key, index), 0) >= self.repeat:
                continue
            self._delivered[(key, index)] = self._delivered.get((key, index), 0) + 1
            for name, value in (entry.get("set") or {}).items():
                self._force(name, value)
            return
        for name, value in self.terminals.get(key, {}).items():
            self._force(name, value)

    def _selectors_of(self, stmt) -> dict:
        """The resources this command names, as `provenance` recorded them."""
        text = stmt.get("text", "") or ""
        cached = self._selector_cache.get(id(stmt))
        if cached is None:
            from .provenance import exec_selectors
            cached = exec_selectors(text) if _EXEC_HEAD.search(text) else {}
            self._selector_cache[id(stmt)] = cached
        return cached

    def _force(self, name: str, value) -> None:
        """Deliver a stub's outcome, bypassing everything that would refuse it.

        A record area filled by an operation is filled with *bytes*, and each
        field under it gets the piece of the record that lands on it - the
        same rule a group MOVE follows. Handing every child the whole record
        instead makes a one-character flag hold the entire 350-byte image, so
        every comparison against it is false and the payload reaches no
        decision at all. That is not a corner case: it is how a batch program
        reads a record, and it is why an outcome that names a record area
        could not previously move a branch.

        A value too short to be a record image, or a group whose layout is not
        known, keeps the old behaviour, because there are no bytes to divide.
        """
        name = name.upper()
        self.state[name] = value
        self._note(name, None)
        if self.slot_of(name) is not None:
            # With a byte store the group's bytes *are* the children's bytes,
            # so the write is already done and splitting it again would
            # overwrite the record with a re-encoding of itself.
            for child in self.model.descendants(name):
                self._note(child, None)
            return
        children = self.model.descendants(name)
        if not children:
            return
        fields = self._elementary(name)
        width = max((offset + size for _n, offset, size in fields), default=0)
        if fields and isinstance(value, str) and len(value) >= width > 0:
            for child, offset, size in fields:
                piece = value[offset:offset + size]
                spec = (self.model.pic_of(child) or "").upper()
                if spec and "9" in spec and "X" not in spec:
                    try:
                        self.state[child] = int(piece)
                    except (TypeError, ValueError):
                        self.state[child] = piece
                else:
                    self.state[child] = piece
                self._note(child, None)
            return
        for child in children:
            self.state[child] = value
            self._note(child, None)

    def _snapshot(self, condition: str) -> dict:
        out = {}
        for alternative in condition_atoms(condition,
                                           names=self._names88):
            for atom in alternative:
                for term in (atom.lhs, atom.rhs):
                    if term.kind == "var":
                        out[term.name] = self.value_of(term)
        return out

    def _cycle(self, children, para: str, depth: int) -> bool:
        """Run one iteration of an inline loop; False means stop looping.

        `EXIT PERFORM CYCLE` ends the iteration, `EXIT PERFORM` ends the loop.
        """
        try:
            self.block(children, para, depth)
        except _ExitPerformCycle:
            pass
        except _ExitPerform:
            return False
        return True

    def _times(self, clause: str, children, para: str, depth: int, line: int,
               ordinal: int = -1):
        """`PERFORM n TIMES` runs the body n times, not once.

        The count is evaluated once, on entry: a body that assigns to the
        same field does not shorten its own loop. Ignoring the phrase runs
        everything the loop accumulates exactly one time, and every branch
        that tests the total is decided on that.
        """
        m = re.match(r"(.*?)\s+TIMES\b", norm(clause), re.I)
        try:
            total = int(self._operand_number(m.group(1).strip())) if m else 0
        except (TypeError, ValueError):
            total = 0
        done = 0
        while done < min(total, MAX_LOOP):
            if not self._cycle(children, para, depth):
                break
            done += 1
        self.trace.guards.append(GuardEvent(para, line, "PERFORM_TIMES",
                                            norm(clause), done > 0, {}, ordinal))

    def _loop(self, condition: str, children, para: str, depth: int, line: int,
              ordinal: int = -1, test_after: bool = False):
        count = 0
        # WITH TEST AFTER is do-while: the body runs once before the
        # condition is ever looked at. Treated as the default TEST BEFORE, a
        # loop that always executes becomes one that may never execute, and
        # whatever it was counting is still zero at the branch below it.
        running = True
        if test_after:
            running = self._cycle(children, para, depth)
            count += 1
        while running and count < MAX_LOOP and not self.evaluate(condition):
            running = self._cycle(children, para, depth)
            count += 1
        self.trace.guards.append(GuardEvent(para, line, "PERFORM_UNTIL", condition,
                                            count > 0, self._snapshot(condition),
                                            ordinal, self._origins(condition)))

    def _varying(self, clause: str, children, para: str, depth: int, line: int,
                 ordinal: int = -1):
        # One phrase per VARYING/AFTER. AFTER nests *inside*: the last phrase
        # runs its whole range for every value of the one before it, and is
        # reset to its FROM each time. Executing only the first phrase runs
        # the body n times where COBOL runs it n*m, so anything counting
        # inside the loop lands on the wrong number.
        phrases = re.findall(
            r"(?:VARYING|AFTER)\s+([A-Z0-9-]+)\s+FROM\s+(\S+)\s+BY\s+(\S+)"
            r"\s+UNTIL\s+(.*?)(?=\s+AFTER\s+|$)", norm(clause), re.I)
        if not phrases:
            self.block(children, para, depth)
            return
        entered = [False]
        budget = [MAX_LOOP * MAX_LOOP]

        def level(index: int) -> None:
            var, start, by, until = phrases[index]
            var = var.upper()
            self.assign(var, self._sending_value(start))
            step = self._sending_value(by)
            count = 0
            while count < MAX_LOOP and budget[0] > 0 and not self.evaluate(until):
                budget[0] -= 1
                if index + 1 < len(phrases):
                    level(index + 1)
                else:
                    entered[0] = True
                    try:
                        self.block(children, para, depth)
                    except _ExitPerformCycle:
                        pass
                try:
                    self.assign(var, float(self.value_of(parse_term(var)))
                                + float(step))
                except (TypeError, ValueError):
                    break
                count += 1

        try:
            level(0)
        except _ExitPerform:
            # `EXIT PERFORM` leaves the whole inline PERFORM, every AFTER
            # level of it, without stepping the loop variables again.
            pass
        self.trace.guards.append(GuardEvent(para, line, "PERFORM_VARYING",
                                            phrases[0][3], entered[0],
                                            self._snapshot(phrases[0][3]),
                                            ordinal,
                                            self._origins(phrases[0][3])))

    # -- arithmetic --------------------------------------------------------
    def number_of(self, text: str) -> float:
        """One operand or a whole expression, as a number.

        `COMPUTE` and a condition like `IF A + B > 10` want the same thing,
        so they go through the same door.
        """
        from .ir import eval_arith, is_arithmetic
        if is_arithmetic(text):
            return eval_arith(text, self._operand_number)
        return self._operand_number(text)

    def _operand_number(self, text: str) -> float:
        value = self.value_of(parse_term(text))
        if isinstance(value, bool):
            return 1.0 if value else 0.0
        try:
            return float(str(value).strip())
        except (TypeError, ValueError):
            return 0.0

    @staticmethod
    def _round(value: float, decimals: int, mode: str) -> float:
        """COBOL's ROUNDED, which is not Python's `round`.

        The standard's default is NEAREST-AWAY-FROM-ZERO: a half goes away
        from zero, so 2.5 is 3 and -2.5 is -3. Python's `round` is
        NEAREST-EVEN, which makes 2.5 come out 2 - a value the compiler never
        produces, on the one operation a rounded COMPUTE exists to control.
        `ROUNDED MODE IS ...` names the other modes explicitly.
        """
        import math
        scale = 10.0 ** decimals
        scaled = value * scale
        sign = -1.0 if scaled < 0 else 1.0
        body = abs(scaled)
        if mode == "TRUNCATION":
            out = math.floor(body)
        elif mode == "NEAREST-EVEN":
            out = abs(round(scaled))
        elif mode == "NEAREST-TOWARD-ZERO":
            out = math.ceil(body - 0.5)
        elif mode == "TOWARD-GREATER":
            return math.ceil(scaled - 1e-9) / scale
        elif mode == "TOWARD-LESSER":
            return math.floor(scaled + 1e-9) / scale
        elif mode == "AWAY-FROM-ZERO":
            out = math.ceil(body - 1e-9)
        else:                                    # NEAREST-AWAY-FROM-ZERO
            out = math.floor(body + 0.5 + 1e-9)
        return sign * out / scale

    def _store_number(self, name: str, value: float, rounded: bool = False,
                      mode: str = ""):
        """Write an arithmetic result, respecting the receiver's PIC.

        `DIVIDE 10 BY 4 GIVING R` where R is PIC 9(3) is 2, not 2.5. Keeping
        the Python quotient makes every later comparison on R disagree with
        the compiler by a fraction, which is exactly the kind of difference
        an equality test turns into a wrong branch.
        """
        from .layout import digits_of
        term = parse_term(name.strip()) if name.strip() else None
        base = (term.name if term is not None and term.kind == "var"
                else name.split("(")[0].strip())
        index = self._indices(term) if term is not None else ()
        pic = self.model.pic_of(base)
        try:
            _whole, decimals = digits_of(pic) if pic else (0, None)
        except Exception:                                        # noqa: BLE001
            decimals = None
        if pic and not decimals:
            value = (self._round(value, 0, mode) if rounded
                     else float(int(value)))
        elif rounded and decimals:
            value = self._round(value, decimals, mode)
        self.assign(base, value, index=index)

    _RECEIVER = None

    def _receivers(self, text: str) -> list:
        import re
        out = []
        # `ADD 1 TO WS-TOTAL (I)` names one receiver, not two. Splitting on
        # whitespace makes the subscript a second operand called "(I)" and
        # sends the result to occurrence 1 whatever I holds.
        for word in re.split(r"\s+", norm(text)):
            if not word:
                continue
            if word.startswith("(") and out:
                out[-1] = out[-1] + word
                continue
            if word.upper() in ("ROUNDED", "TO", "GIVING", "FROM", "BY", "INTO"):
                continue
            out.append(word.strip(".,"))
        return out

    def _arithmetic(self, kind: str, stmt) -> None:
        import re
        text = norm(stmt.get("text", ""))
        # Anything after these phrases is a conditional handler, not operands.
        text = re.split(r"\b(?:ON\s+SIZE\s+ERROR|NOT\s+ON\s+SIZE\s+ERROR)\b",
                        text, maxsplit=1, flags=re.I)[0].strip()
        rounded = bool(re.search(r"\bROUNDED\b", text, re.I))
        # `ROUNDED MODE IS TRUNCATION` names the rounding rule. Left in the
        # text its three words parse as three more receivers, so the result
        # is written to fields called MODE, IS and TRUNCATION and the real
        # receiver keeps its old value.
        mode = ""
        m = re.search(r"\bROUNDED\s+MODE\s+IS\s+([A-Z-]+)", text, re.I)
        if m:
            mode = m.group(1).upper()
            text = text[:m.start()] + " ROUNDED " + text[m.end():]

        # A result too wide for its receiver, or a division by zero, raises the
        # size-error condition. Where the statement handles it the receiver is
        # left alone and the handler runs; where it does not, the standard
        # leaves the result undefined and the compiler truncates, so the old
        # behaviour is what matches it. Only the guarded case changes, and it
        # is the one whose two arms were both being scored the same way.
        guarded = any(c.get("type") == "PHRASE"
                      and "size_error" in (c.get("attributes") or {}).get("phrase", "")
                      for c in (stmt.get("children") or []))
        self._raised = False

        def store(name, value, rnd=None):
            if self._too_wide(name, value):
                self._raised = True
                if guarded:
                    return
            self._store_number(name, value, rounded if rnd is None else rnd, mode)

        try:
            if kind == "COMPUTE":
                m = re.match(r"COMPUTE\s+(.*?)\s*=\s*(.*)$", text, re.I)
                if not m:
                    return
                value = self.number_of(m.group(2))
                for name in self._receivers(m.group(1)):
                    store(name, value)
                return

            if kind == "ADD":
                m = re.match(r"ADD\s+(.*?)\s+TO\s+(.*?)\s+GIVING\s+(.*)$",
                             text, re.I)
                if m:
                    total = (sum(self._operand_number(o)
                                 for o in self._receivers(m.group(1)))
                             + self._operand_number(m.group(2)))
                    for name in self._receivers(m.group(3)):
                        store(name, total)
                    return
                m = re.match(r"ADD\s+(.*?)\s+GIVING\s+(.*)$", text, re.I)
                if m:
                    total = sum(self._operand_number(o)
                                for o in self._receivers(m.group(1)))
                    for name in self._receivers(m.group(2)):
                        store(name, total)
                    return
                m = re.match(r"ADD\s+(.*?)\s+TO\s+(.*)$", text, re.I)
                if m:
                    addend = sum(self._operand_number(o)
                                 for o in self._receivers(m.group(1)))
                    # `ADD 1 TO A B` adds to *each* receiver; treating only
                    # the first as one means every later counter stays put.
                    for name in self._receivers(m.group(2)):
                        store(name, self._operand_number(name) + addend)
                    return
                return

            if kind == "SUBTRACT":
                m = re.match(r"SUBTRACT\s+(.*?)\s+FROM\s+(.*?)\s+GIVING\s+(.*)$",
                             text, re.I)
                if m:
                    total = (self._operand_number(m.group(2))
                             - sum(self._operand_number(o)
                                   for o in self._receivers(m.group(1))))
                    for name in self._receivers(m.group(3)):
                        store(name, total)
                    return
                m = re.match(r"SUBTRACT\s+(.*?)\s+FROM\s+(.*)$", text, re.I)
                if m:
                    amount = sum(self._operand_number(o)
                                 for o in self._receivers(m.group(1)))
                    for name in self._receivers(m.group(2)):
                        store(name, self._operand_number(name) - amount)
                    return
                return

            if kind == "MULTIPLY":
                m = re.match(r"MULTIPLY\s+(.*?)\s+BY\s+(.*?)\s+GIVING\s+(.*)$",
                             text, re.I)
                if m:
                    product = (self._operand_number(m.group(1))
                               * self._operand_number(m.group(2)))
                    for name in self._receivers(m.group(3)):
                        store(name, product)
                    return
                m = re.match(r"MULTIPLY\s+(.*?)\s+BY\s+(.*)$", text, re.I)
                if m:
                    factor = self._operand_number(m.group(1))
                    for name in self._receivers(m.group(2)):
                        store(name, self._operand_number(name) * factor)
                    return
                return

            if kind == "DIVIDE":
                remainder = None
                m = re.search(r"\bREMAINDER\s+(\S+)\s*$", text, re.I)
                if m:
                    remainder, text = m.group(1), text[:m.start()].strip()
                m = re.match(r"DIVIDE\s+(.*?)\s+(BY|INTO)\s+(.*?)\s+GIVING\s+(.*)$",
                             text, re.I)
                if m:
                    left, right = (self._operand_number(m.group(1)),
                                   self._operand_number(m.group(3)))
                    top, bottom = ((left, right) if m.group(2).upper() == "BY"
                                   else (right, left))
                    if not bottom:
                        self._raised = True
                    quotient = top / bottom if bottom else 0.0
                    for name in self._receivers(m.group(4)):
                        if bottom or not guarded:
                            store(name, quotient)
                    if remainder:
                        store(remainder, top - bottom * int(quotient), False)
                    return
                m = re.match(r"DIVIDE\s+(.*?)\s+INTO\s+(.*)$", text, re.I)
                if m:
                    divisor = self._operand_number(m.group(1))
                    if not divisor:
                        self._raised = True
                    for name in self._receivers(m.group(2)):
                        top = self._operand_number(name)
                        if divisor or not guarded:
                            store(name, top / divisor if divisor else 0.0)
                    return
                return
        except (TypeError, ValueError, ZeroDivisionError, OverflowError):
            self.trace.approximations.append("arithmetic failed: %s" % text[:60])

    def _string(self, stmt) -> None:
        """STRING concatenates its sources into one receiver.

        Skipped, the receiver keeps its previous contents - usually spaces -
        and any later test on the assembled text takes one direction only.
        """
        import re
        text = norm(stmt.get("text", ""))
        text = re.split(r"\b(?:ON\s+OVERFLOW|NOT\s+ON\s+OVERFLOW|END-STRING)\b",
                        text, maxsplit=1, flags=re.I)[0]
        m = re.match(r"STRING\s+(.*?)\s+INTO\s+(.*)$", text, re.I)
        if not m:
            return
        sources, tail = m.group(1), m.group(2)
        target = re.split(r"\bWITH\s+POINTER\b", tail, maxsplit=1,
                          flags=re.I)[0].strip()
        pieces = re.findall(
            r"(.+?)\s+DELIMITED\s+BY\s+(SIZE|SPACES?|'[^']*'|\"[^\"]*\"|[A-Z0-9-]+)"
            r"(?=\s|$)", sources, re.I)
        if not pieces:
            return
        out = []
        for operand, delimiter in pieces:
            term = parse_term(operand.strip())
            value = self.value_of(term)
            body = "" if value is None else str(value)
            if term.kind == "var" and not term.refmod and not term.func:
                body = self._text_of(term.name, value)
            upper = delimiter.upper()
            if upper == "SIZE":
                out.append(body)
            elif upper in ("SPACE", "SPACES"):
                out.append(body.split(" ")[0])
            else:
                stop = self.value_of(parse_term(delimiter))
                stop = "" if stop is None else str(stop)
                out.append(body.split(stop)[0] if stop else body)
        name = target.split("(")[0].strip().upper()
        width = self._width(name)
        joined = "".join(out)
        # WITH POINTER says where in the receiver to start, and it is left
        # holding one past the last character stored - which is how a program
        # assembles a line in several statements. Ignored, every STRING
        # overwrites the receiver from byte one and the earlier pieces are
        # gone.
        pointer = re.search(r"\bWITH\s+POINTER\s+([A-Z0-9][A-Z0-9-]*(?:\s*\([^)]*\))?)",
                            norm(stmt.get("text", "")), re.I)
        start = 0
        if pointer:
            start = int(self._operand_number(pointer.group(1))) - 1
        # Overflow is a decision, not a diagnostic: it fires when the pointer
        # is outside the receiver or the sources do not fit in what is left.
        self._raised = bool(start < 0 or (width and start >= width)
                            or (width and start + len(joined) > width))
        if start < 0 or (width and start >= width):
            return                        # nothing is transferred
        current = self._text_of(name, self._stored(name))
        if width:
            current = current.ljust(width)[:width]
        room = (width - start) if width else len(joined)
        body = joined[:room]
        assembled = current[:start] + body + current[start + len(body):]
        self.assign(name, assembled[:width] if width else assembled)
        if pointer:
            self.assign(pointer.group(1).strip(), start + len(body) + 1)

    _UNSTRING_HEAD = re.compile(r"UNSTRING\s+(\S+)(.*)$", re.I)

    def _unstring(self, stmt) -> None:
        """UNSTRING splits one sending item across several receivers.

        Skipped, every receiver keeps whatever it held - normally spaces - so
        each field the program went on to test has one reachable value. The
        verb is how a delimited record, a screen field or a CICS commarea is
        taken apart, and the fields it produces are exactly the ones later
        conditions turn on.
        """
        import re as _re
        text = norm(stmt.get("text", ""))
        text = _re.split(r"\b(?:ON\s+OVERFLOW|NOT\s+ON\s+OVERFLOW|END-UNSTRING)\b",
                         text, maxsplit=1, flags=_re.I)[0].strip()
        m = self._UNSTRING_HEAD.match(text)
        if not m:
            return
        source_text, rest = m.group(1), m.group(2)
        term = parse_term(source_text)
        value = self.value_of(term)
        body = (self._text_of(term.name, value)
                if term.kind == "var" and not term.refmod and not term.func
                else ("" if value is None else str(value)))

        delimiters: list = []
        d = _re.match(r"\s*DELIMITED\s+BY\s+(.*?)\s+INTO\s+(.*)$", rest, _re.I)
        if d:
            for piece in _re.split(r"\s+OR\s+", d.group(1), flags=_re.I):
                piece = piece.strip()
                piece = _re.sub(r"^ALL\s+", "", piece, flags=_re.I).strip()
                one = self._sending_value(piece)
                one = "" if one is None else str(one)
                if piece.upper() in ("SPACE", "SPACES"):
                    one = " "
                if one:
                    delimiters.append(one)
            rest = d.group(2)
        else:
            d = _re.match(r"\s*INTO\s+(.*)$", rest, _re.I)
            if not d:
                return
            rest = d.group(1)

        pointer_name = tally_name = ""
        p = _re.search(r"\bWITH\s+POINTER\s+(\S+)", rest, _re.I)
        if p:
            pointer_name = p.group(1)
        t = _re.search(r"\bTALLYING\s+IN\s+(\S+)", rest, _re.I)
        if t:
            tally_name = t.group(1)
        rest = _re.split(r"\bWITH\s+POINTER\b|\bTALLYING\s+IN\b", rest,
                         maxsplit=1, flags=_re.I)[0]

        # `INTO A COUNT IN C1 B DELIMITER IN D2 C` - each receiver may be
        # followed by its own DELIMITER IN and COUNT IN.
        receivers: list = []
        words = [w for w in _re.split(r"[,\s]+", rest.strip()) if w]
        index = 0
        while index < len(words):
            word = words[index]
            if word.upper() in ("DELIMITER", "COUNT") and receivers:
                which = 1 if word.upper() == "DELIMITER" else 2
                if index + 2 < len(words) and words[index + 1].upper() == "IN":
                    receivers[-1][which] = words[index + 2]
                    index += 3
                    continue
            receivers.append([word, "", ""])
            index += 1
        if not receivers:
            return

        at = int(self._operand_number(pointer_name)) - 1 if pointer_name else 0
        if at < 0 or at >= len(body):
            self._raised = True           # pointer outside the sending item
            return
        taken = 0
        for name, delim_name, count_name in receivers:
            if at >= len(body):
                break
            if delimiters:
                hits = [(body.find(d, at), d) for d in delimiters]
                hits = [(i, d) for i, d in hits if i >= 0]
                cut, hit = min(hits) if hits else (len(body), "")
            else:
                cut, hit = min(len(body), at + max(1, self._width(name))), ""
            field = body[at:cut]
            self.assign(name, self._fit(name.upper(), field))
            if delim_name:
                self.assign(delim_name, hit)
            if count_name:
                self.assign(count_name, len(field))
            at = cut + len(hit)
            taken += 1
        if tally_name:
            # TALLYING counts up from what the field already held.
            self.assign(tally_name, self._operand_number(tally_name) + taken)
        if pointer_name:
            self.assign(pointer_name, at + 1)
        self._raised = at < len(body)     # characters left with no receiver

    # -- SEARCH ------------------------------------------------------------
    def _table_of(self, name: str) -> str:
        """The OCCURS item a SEARCH operand names, or the one above it.

        ``SEARCH WS-ENTRY`` names the repeating item itself, but a program
        may also name a group that contains it. Walking up is what lets the
        verb find the occurrence count and the KEY clause wherever the
        declaration put them.
        """
        current = (name or "").upper()
        seen = 0
        while current and seen < 8:
            if self.model.occurs.get(current):
                return current
            current = self.model.parent.get(current, "")
            seen += 1
        return (name or "").upper()

    def _index_name(self, table: str) -> str:
        names = self.model.indexes.get(table) or []
        return names[0] if names else ""

    def _set_index(self, table: str, index: str, varying: str,
                   occurrence: int) -> None:
        if index:
            self.state[index] = occurrence
            self._note(index, None)
        # `VARYING identifier` steps in lockstep with the index; VARYING a
        # *second index* of the same table does too. Either way the program
        # reads it after the SEARCH to find out which occurrence matched.
        if varying and varying != index:
            self.assign(varying, occurrence)
        del table

    def _search(self, stmt, para: str, depth: int, line: int) -> None:
        """SEARCH scans a table; SEARCH ALL bisects an ordered one.

        Both are decisions and both are recorded as such: an arm that was
        evaluated and did not match is a direction, and so is AT END.
        """
        attrs = stmt.get("attributes", {})
        children = stmt.get("children") or []
        arms = [c for c in children if c.get("type") == "WHEN"]
        ends = [c for c in children if c.get("type") == "PHRASE"]
        table = self._table_of(attrs.get("table", ""))
        occurrences = self.model.occurs.get(table, 0)
        index = self._index_name(table)
        varying = (attrs.get("varying") or "").upper()

        def take(arm, occurrence) -> None:
            self._set_index(table, index, varying, occurrence)
            self.block(arm.get("children") or [], para, depth)

        def at_end() -> None:
            for arm in ends:
                self.trace.guards.append(
                    GuardEvent(para, arm.get("line_start", line), "PHRASE",
                               "at_end", True, {}, arm.get("ordinal", -1)))
                self.block(arm.get("children") or [], para, depth)

        def not_at_end() -> None:
            for arm in ends:
                self.trace.guards.append(
                    GuardEvent(para, arm.get("line_start", line), "PHRASE",
                               "at_end", False, {}, arm.get("ordinal", -1)))

        if not occurrences or not arms:
            # A table with no OCCURS is not a table. Reporting it rather than
            # guessing keeps a parse failure from being scored as coverage.
            note = "%s:SEARCH %s" % (para, attrs.get("table", ""))
            if note not in self.trace.approximations:
                self.trace.approximations.append(note)
            at_end()
            return

        if attrs.get("all"):
            found = self._search_all(table, index, varying, arms, occurrences,
                                     para, line)
            if found is not None:
                not_at_end()
                take(arms[found[0]], found[1])
                return
            at_end()
            return

        # Serial SEARCH begins at whatever the index holds, which the program
        # is required to have set. Starting at 1 regardless would make a
        # resumed search - `SET IX UP BY 1` then SEARCH again - find the same
        # occurrence for ever.
        start = self._occurrence(index)
        for occurrence in range(start, occurrences + 1):
            self._set_index(table, index, varying, occurrence)
            for position, arm in enumerate(arms):
                condition = norm(arm.get("attributes", {}).get("value", ""))
                result = self.evaluate(condition)
                self.trace.guards.append(
                    GuardEvent(para, arm.get("line_start", line), "WHEN",
                               condition, result, self._snapshot(condition),
                               arm.get("ordinal", -1), self._origins(condition)))
                if result:
                    not_at_end()
                    take(arm, occurrence)
                    return
                del position
        # The index is left one past the end, which is what the compiler does
        # and what a program testing it afterwards expects.
        self._set_index(table, index, varying, occurrences + 1)
        at_end()

    def _occurrence(self, index: str) -> int:
        if not index:
            return 1
        try:
            value = int(float(str(self._stored(index)).strip()))
        except (TypeError, ValueError):
            return 1
        return value if value >= 1 else 1

    def _search_all(self, table: str, index: str, varying: str, arms: list,
                    occurrences: int, para: str, line: int):
        """Bisect an ordered table. Returns ``(arm, occurrence)`` or None.

        The KEY clause decides which way to step, so the condition is taken
        apart into its equality conjuncts and matched against the declared
        keys, most significant first. A key the condition does not mention
        contributes nothing, which is the standard's own rule; a condition
        that mentions no key at all leaves nothing to bisect on, and that is
        reported rather than turned into a linear scan wearing the wrong name.
        """
        keys = [name for _direction, name in self.model.keys.get(table, [])]
        direction = {name: way for way, name
                     in self.model.keys.get(table, [])}
        low, high = 1, occurrences
        probes = 0
        # A bisection over n occurrences takes ceil(log2(n)) + 1 probes; the
        # ceiling is generous and only bounds a table whose declaration lies.
        while low <= high and probes <= occurrences + 2:
            probes += 1
            middle = (low + high) // 2
            self._set_index(table, index, varying, middle)
            step = 0
            for position, arm in enumerate(arms):
                condition = norm(arm.get("attributes", {}).get("value", ""))
                result = self.evaluate(condition)
                self.trace.guards.append(
                    GuardEvent(para, arm.get("line_start", line), "WHEN",
                               condition, result, self._snapshot(condition),
                               arm.get("ordinal", -1), self._origins(condition)))
                if result:
                    return position, middle
                if not step:
                    step = self._key_step(condition, keys, direction)
            if step > 0:
                low = middle + 1
            elif step < 0:
                high = middle - 1
            else:
                note = "%s:SEARCH ALL without a key comparison" % para
                if note not in self.trace.approximations:
                    self.trace.approximations.append(note)
                return None
        return None

    def _key_step(self, condition: str, keys: list, direction: dict) -> int:
        """+1 to look higher up the table, -1 lower, 0 when undecidable."""
        alternatives = condition_atoms(condition, names=self._names88)
        if not alternatives:
            return 0
        ranked: list = []
        for atom in alternatives[0]:
            for side, other in ((atom.lhs, atom.rhs), (atom.rhs, atom.lhs)):
                if side.kind != "var":
                    continue
                name = base_name(side.name)
                if name not in keys:
                    continue
                ranked.append((keys.index(name), name, side, other))
                break
        # Which side of the `=` the key sits on does not change the step: the
        # comparison that decides the half is always the *key* against the
        # value, and `WHEN 5 = WS-K (IX)` is the same search as
        # `WHEN WS-K (IX) = 5`.
        for _rank, name, side, other in sorted(ranked, key=lambda r: r[0]):
            actual, wanted = self.value_of(side), self.value_of(other)
            if holds(actual, "=", wanted):
                continue
            below = holds(actual, "<", wanted)
            ascending = direction.get(name, "ASCENDING") == "ASCENDING"
            return 1 if below == ascending else -1
        return 0

    def _operand_text(self, raw: str) -> str:
        """An INSPECT operand as the bytes it stands for.

        A literal is itself; an identifier is its contents padded to its own
        declared width, because that is what the comparison uses.
        """
        term = parse_term(raw)
        value = self.value_of(term)
        if term.kind == "var" and not term.refmod and not term.func:
            return self._field_bytes(term.name, value)
        return "" if value is None else str(value)

    def _inspect(self, stmt) -> None:
        """INSPECT: count occurrences, replace them, or translate characters.

        The receiving counter is *added to*, not set - the standard is
        explicit that INSPECT does not initialise it, and a program that
        tallies twice into one counter is relying on that.
        """
        text = norm(stmt.get("text", ""))
        plan = parse_inspect(re.sub(r"^INSPECT\s+", "", text, flags=re.I))
        if not plan:
            return
        subject = parse_term(plan["subject"])
        if subject.kind != "var" or not subject.name:
            return
        raw = self.value_of(subject)
        body = (self._slice(subject, self._stored(subject.name))
                if subject.refmod else self._field_bytes(subject.name, raw))

        def span(entry):
            before = (self._operand_text(entry["before"])
                      if entry.get("before") else None)
            after = (self._operand_text(entry["after"])
                     if entry.get("after") else None)
            # A delimiter is compared as written rather than padded to the
            # width of whatever holds it: `AFTER INITIAL WS-D` where WS-D is
            # PIC X(10) holding '/' looks for a slash, not for a slash and
            # nine spaces.
            if before is not None:
                before = before.rstrip() or before
            if after is not None:
                after = after.rstrip() or after
            return _inspect_region(body, before, after)

        if plan["tallying"]:
            items = []
            for entry in plan["tallying"]:
                lo, hi = span(entry)
                items.append({"kind": entry["kind"],
                              "arg": (self._operand_text(entry["arg"])
                                      if entry["arg"] else ""),
                              "lo": lo, "hi": hi})
            counts = inspect_tally(body, items)
            totals: dict = {}
            for entry, count in zip(plan["tallying"], counts):
                name = parse_term(entry["counter"]).name
                if name:
                    totals[name] = totals.get(name, 0) + count
            for name, count in totals.items():
                try:
                    current = float(str(self.value_of(parse_term(name))).strip())
                except (TypeError, ValueError):
                    current = 0.0
                self.assign(name, int(current + count))

        if plan["replacing"]:
            items = []
            for entry in plan["replacing"]:
                lo, hi = span(entry)
                items.append({"kind": entry["kind"],
                              "arg": (self._operand_text(entry["arg"])
                                      if entry["arg"] else ""),
                              "to": self._operand_text(entry["to"]),
                              "lo": lo, "hi": hi})
            body = inspect_replace(body, items)

        if plan["converting"]:
            entry = plan["converting"]
            lo, hi = span(entry)
            body = inspect_convert(body, self._operand_text(entry["from"]),
                                   self._operand_text(entry["to"]), lo, hi)

        if plan["replacing"] or plan["converting"]:
            if subject.refmod:
                self.assign_slice(subject, body)
            else:
                self.assign(subject.name, body)

    def _initialize(self, stmt) -> None:
        """INITIALIZE sets every elementary item under an operand to its
        category's zero - numeric to 0, everything else to spaces.

        Treated as a no-op the operand keeps whatever the last record left in
        it, so a field the program has just cleared still compares equal to
        the value it held, and the direction that depends on it is unreachable.
        """
        import re
        text = norm(stmt.get("text", ""))
        # REPLACING names a category and a value: `REPLACING NUMERIC BY 7`
        # leaves every alphanumeric field alone and puts 7 in the numeric
        # ones. Dropped, the statement clears fields the program meant to
        # keep and sets the rest to the wrong value.
        replacing: list = []
        parts = re.split(r"\bREPLACING\b", text, maxsplit=1, flags=re.I)
        if len(parts) > 1:
            for m in re.finditer(
                    r"\b(ALPHANUMERIC-EDITED|NUMERIC-EDITED|ALPHANUMERIC|"
                    r"ALPHABETIC|NUMERIC|NATIONAL)(?:\s+DATA)?\s+BY\s+(\S+)",
                    parts[1], re.I):
                replacing.append((m.group(1).upper(), self._sending_value(m.group(2))))
        text = parts[0]
        body = re.sub(r"^INITIALIZE\s+", "", text, flags=re.I)
        for name in self._receivers(body):
            name = name.split("(")[0].strip().upper()
            if not name or name in ("ALL", "TO", "VALUE"):
                continue
            children = [c for c in self.model.descendants(name)
                        if self.model.pic_of(c)]
            for field in (children or [name]):
                if field in self._pinned:
                    continue
                spec = (self.model.pic_of(field) or "").upper()
                numeric = bool(spec) and "9" in spec and "X" not in spec
                if replacing:
                    # Only the named categories are written; everything else
                    # keeps what it held.
                    want = "NUMERIC" if numeric else "ALPHANUMERIC"
                    chosen = [v for c, v in replacing if c.startswith(want[:5])]
                    if not chosen:
                        continue
                    self.assign(field, chosen[0])
                    continue
                # FILLER occupies bytes and has no name a program can write,
                # and INITIALIZE leaves it exactly as it was. Clearing it
                # blanks bytes the record still holds, which a group read or
                # a REDEFINES then sees.
                if self._is_filler(field):
                    continue
                if self._blank(field):
                    self._note(field, None)
                    continue
                blank = 0 if numeric else " "
                self.state[field.upper()] = blank
                self._note(field, None)
            if not children and name not in self._pinned \
                    and self.slot_of(name) is None:
                spec = (self.model.pic_of(name) or "").upper()
                self.state[name] = (0 if spec and "9" in spec and "X" not in spec
                                    else " ")
                self._note(name, None)

    @staticmethod
    def _is_filler(name: str) -> bool:
        """FILLER occupies bytes and carries no name a statement can reach."""
        upper = (name or "").upper()
        return upper == "FILLER" or upper.startswith("FILLER#")

    def _blank(self, name: str) -> bool:
        """Clear one field to its category's zero, every occurrence of it.

        INITIALIZE reaches the whole table, not its first element; writing
        only occurrence 1 leaves the rest holding whatever the last record
        put there, and a later scan of the table then finds it.
        """
        slot = self.slot_of(name)
        if slot is None:
            return False
        from .storage import occurrence_count, occurrence_index
        blank = 0 if slot.numeric or slot.category == "edited" else " "
        for ordinal in range(occurrence_count(slot)):
            self.memory.write(slot, blank, occurrence_index(slot, ordinal))
        return True


def verify(program, plan, entry: str, *, terminals: dict | None = None,
           defaults: dict | None = None, repeat: int = 1) -> dict:
    """Run the plan and report whether the target was reached, and if not,
    the first guard on the chain that went the wrong way."""
    interp = Interpreter(program, plan.input_state(), stubs=plan.stub_plan(),
                         terminals=terminals or plan.terminals,
                         defaults=defaults, repeat=repeat)
    trace = interp.run(entry)
    reached = plan.target in trace.entered_set
    chain = [c for c in plan.chain]
    frontier = None
    for frame in chain:
        if frame not in trace.entered_set:
            frontier = frame
            break

    blocking = []
    if not reached:
        wanted = set(chain)
        for event in trace.guards:
            if event.paragraph in wanted and not event.result:
                blocking.append(event)

    return {
        "reached": reached,
        "entry": entry,
        "target": plan.target,
        "chain": chain,
        "chain_reached": [c for c in chain if c in trace.entered_set],
        "first_missing_frame": frontier,
        "steps": trace.steps,
        "stopped": trace.stopped,
        "paragraphs_entered": len(trace.entered_set),
        "approximations": trace.approximations[:5],
        "exhausted_steps": trace.steps >= MAX_STEPS,
        "runaway": trace.runaway,
        "external_calls": interp.calls,
        "blocking_guards": [
            {"paragraph": e.paragraph, "line": e.line, "ordinal": e.ordinal,
             "kind": e.kind,
             "condition": e.condition, "values": e.values}
            for e in blocking[:12]
        ],
    }
