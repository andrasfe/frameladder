"""Run the COBOL subset concretely, to check a plan and to say where it failed.

This is tier 1.  A plan that type-checks symbolically can still be wrong -
a guard the ladder never lifted, an ordering it got backwards - and the
only way to know is to run it.  When a plan does fail, the useful output
is not "false" but *which guard on the chain went the wrong way*, because
that is the single question worth handing to an agent.

Subscripts are flattened: ``WS-TAB(I)`` and ``WS-TAB`` are the same cell.
That mirrors how the rest of the toolchain models tables and keeps the
interpreter small; it means array-indexed plans are verified loosely, and
:attr:`Trace.approximations` says so rather than hiding it.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .conditions import condition_atoms
from .ir import holds, norm, parse_term


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


class _Goto(Exception):
    def __init__(self, target: str):
        self.target = target


class _Stop(Exception):
    pass


class _NextTask(Exception):
    """`EXEC CICS RETURN TRANSID(...)`: this task ends, another one starts."""


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
        self.state = {k.upper(): v for k, v in (state or {}).items()}
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
        self._pinned: set = set()
        self._delivered: dict = {}
        self._visits: dict = {}
        self._layouts: dict = {}
        self.calls: dict = {}
        # ALTER rewrites another paragraph's GO TO at run time. A dispatcher
        # built on it - and CardDemo's is - cycles forever without this.
        self.altered: dict = {}
        # Off by default and free when off: every other caller pays nothing,
        # and the search that wants it is the only one that carries the cost.
        # A name absent from this table has not been written on this run, so
        # it still holds what the entry state gave it - which is why the
        # table records `None` for an opaque write rather than deleting.
        self.track_origins = track_origins
        self._origin: dict = {}

    # -- values ------------------------------------------------------------
    def value_of(self, term) -> object:
        if term.kind == "const":
            return term.value
        if term.func:
            return self._intrinsic(term)
        value = self._stored(term.name)
        if term.refmod:
            value = self._slice(term, value)
        return value

    def _stored(self, name: str) -> object:
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
        spec = (self.model.pic_of(name) or "").upper()
        return 0 if spec and "9" in spec and "X" not in spec else ""

    def _assembled(self, name: str):
        """A group's value is its children's bytes, laid end to end.

        Without this, writing a field and then testing the record it belongs
        to - `MOVE 'AB' TO WS-1` then `IF WS-REC = SPACES` - reads whatever
        the group last held as a whole, so the test answers a question about
        a value nobody wrote.
        """
        from .ir import base_name
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
        pic = self.model.pic_of(name)
        if not pic:
            return 0
        try:
            return byte_length(pic, self.model.usage_of(name),
                               self.model.look(self.model.sign, name, "") or "")
        except Exception:                                        # noqa: BLE001
            return 0

    def _text_of(self, name: str, value) -> str:
        text = "" if value is None else str(value)
        width = self._width(name)
        if width and len(text) < width:
            text = text.ljust(width)
        return text

    def _as_int(self, expression: str, default: int) -> int:
        if not expression:
            return default
        try:
            # `X(LENGTH OF A + 1:n)` is an expression, not an operand, and
            # every commarea split in a CICS program is written that way.
            # Parsing it as one term reads a field nobody declared and starts
            # the slice at byte 1, so the second half of the record is
            # overlaid on the first.
            from .ir import is_arithmetic
            if is_arithmetic(expression):
                return int(self.number_of(expression))
            return int(float(str(self.value_of(parse_term(expression))).strip()))
        except (TypeError, ValueError, ZeroDivisionError):
            return default

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
        from .ir import parse_term as _pt
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
        for alternative in condition_atoms(text):
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
        from .ir import is_arithmetic
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
        for alternative in condition_atoms(condition):
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

    def assign(self, name: str, value, origin=None) -> None:
        name = name.upper()
        # Values the plan pins are the stub returns and program inputs; the
        # program overwriting them mid-run would undo the very thing being
        # tested, so they hold.
        if name in self._pinned:
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
                from .conditions import when_condition
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
            if condition:
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
            self.block(children, para, depth)
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
            if source.name == "DFHCOMMAREA" and getattr(self, "_carried", None):
                for name in move_targets(attrs.get("targets", "")):
                    for child, value in self._carried.items():
                        if child not in self._pinned:
                            self.state[child] = value
                            self._note(child, None)
                    del name
                return
            value = self.value_of(source)
            origin = self.origin_of(source)
            for name in move_targets(attrs.get("targets", "")):
                self.assign(name, value, origin)
            return

        if kind == "SET":
            name, raw = attrs.get("name"), attrs.get("value")
            if name and raw:
                entry = self.model.condition_names.get(name.upper())
                if entry and raw.upper() == "TRUE":
                    parent, values = entry
                    if values:
                        self.assign(parent, parse_term(values[0]).value)
                else:
                    self.assign(name, parse_term(raw).value)
            return

        if kind in ("ADD", "SUBTRACT", "COMPUTE", "MULTIPLY", "DIVIDE"):
            self._arithmetic(kind, stmt)
            return

        if kind == "INITIALIZE":
            self._initialize(stmt)
            return

        if kind == "STRING":
            self._string(stmt)
            return

        from .provenance import STUB_KINDS, op_key
        if kind in STUB_KINDS:
            self._external(stmt, para, line)
            if children:
                self.block(children, para, depth)
            return

        if children:
            self.block(children, para, depth)

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
                raise _NextTask()
            self.trace.stopped = "terminated by %s" % key
            raise _Stop()
        entries = self.stubs.get(key, [])
        matched = False
        for index, entry in enumerate(entries):
            when = {k.upper(): v for k, v in (entry.get("when") or {}).items()}
            if all(holds(self.value_of(parse_term(k)), "=", v)
                   for k, v in when.items()):
                matched = True
                break
        if not matched:
            for name, value in self.defaults.get(key, {}).items():
                self._force(name, value)
            return
        for index, entry in enumerate(entries):
            when = {k.upper(): v for k, v in (entry.get("when") or {}).items()}
            if not all(holds(self.value_of(parse_term(k)), "=", v)
                       for k, v in when.items()):
                continue
            if self._delivered.get((key, index), 0) >= self.repeat:
                continue
            self._delivered[(key, index)] = self._delivered.get((key, index), 0) + 1
            for name, value in (entry.get("set") or {}).items():
                self._force(name, value)
            return
        for name, value in self.terminals.get(key, {}).items():
            self._force(name, value)

    def _force(self, name: str, value) -> None:
        name = name.upper()
        self.state[name] = value
        self._note(name, None)
        for child in self.model.descendants(name):
            self.state[child] = value
            self._note(child, None)

    def _snapshot(self, condition: str) -> dict:
        out = {}
        for alternative in condition_atoms(condition):
            for atom in alternative:
                for term in (atom.lhs, atom.rhs):
                    if term.kind == "var":
                        out[term.name] = self.value_of(term)
        return out

    def _loop(self, condition: str, children, para: str, depth: int, line: int,
              ordinal: int = -1, test_after: bool = False):
        count = 0
        # WITH TEST AFTER is do-while: the body runs once before the
        # condition is ever looked at. Treated as the default TEST BEFORE, a
        # loop that always executes becomes one that may never execute, and
        # whatever it was counting is still zero at the branch below it.
        if test_after:
            self.block(children, para, depth)
            count += 1
        while count < MAX_LOOP and not self.evaluate(condition):
            self.block(children, para, depth)
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
            self.assign(var, parse_term(start).value)
            step = parse_term(by).value
            count = 0
            while count < MAX_LOOP and budget[0] > 0 and not self.evaluate(until):
                budget[0] -= 1
                if index + 1 < len(phrases):
                    level(index + 1)
                else:
                    entered[0] = True
                    self.block(children, para, depth)
                try:
                    self.assign(var, float(self.value_of(parse_term(var)))
                                + float(step))
                except (TypeError, ValueError):
                    break
                count += 1

        level(0)
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

    def _store_number(self, name: str, value: float, rounded: bool = False):
        """Write an arithmetic result, respecting the receiver's PIC.

        `DIVIDE 10 BY 4 GIVING R` where R is PIC 9(3) is 2, not 2.5. Keeping
        the Python quotient makes every later comparison on R disagree with
        the compiler by a fraction, which is exactly the kind of difference
        an equality test turns into a wrong branch.
        """
        from .layout import digits_of
        base = name.split("(")[0].strip()
        pic = self.model.pic_of(base)
        try:
            _whole, decimals = digits_of(pic) if pic else (0, None)
        except Exception:                                        # noqa: BLE001
            decimals = None
        if pic and not decimals:
            value = round(value) if rounded else float(int(value))
        elif rounded and decimals:
            value = round(value, decimals)
        self.assign(base, value)

    _RECEIVER = None

    def _receivers(self, text: str) -> list:
        import re
        out = []
        for word in re.split(r"\s+", norm(text)):
            if not word or word.upper() in ("ROUNDED", "TO", "GIVING", "FROM",
                                            "BY", "INTO"):
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
        try:
            if kind == "COMPUTE":
                m = re.match(r"COMPUTE\s+(.*?)\s*=\s*(.*)$", text, re.I)
                if not m:
                    return
                value = self.number_of(m.group(2))
                for name in self._receivers(m.group(1)):
                    self._store_number(name, value, rounded)
                return

            if kind == "ADD":
                m = re.match(r"ADD\s+(.*?)\s+TO\s+(.*?)\s+GIVING\s+(.*)$",
                             text, re.I)
                if m:
                    total = (sum(self._operand_number(o)
                                 for o in self._receivers(m.group(1)))
                             + self._operand_number(m.group(2)))
                    for name in self._receivers(m.group(3)):
                        self._store_number(name, total, rounded)
                    return
                m = re.match(r"ADD\s+(.*?)\s+GIVING\s+(.*)$", text, re.I)
                if m:
                    total = sum(self._operand_number(o)
                                for o in self._receivers(m.group(1)))
                    for name in self._receivers(m.group(2)):
                        self._store_number(name, total, rounded)
                    return
                m = re.match(r"ADD\s+(.*?)\s+TO\s+(.*)$", text, re.I)
                if m:
                    addend = sum(self._operand_number(o)
                                 for o in self._receivers(m.group(1)))
                    # `ADD 1 TO A B` adds to *each* receiver; treating only
                    # the first as one means every later counter stays put.
                    for name in self._receivers(m.group(2)):
                        self._store_number(name,
                                           self._operand_number(name) + addend,
                                           rounded)
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
                        self._store_number(name, total, rounded)
                    return
                m = re.match(r"SUBTRACT\s+(.*?)\s+FROM\s+(.*)$", text, re.I)
                if m:
                    amount = sum(self._operand_number(o)
                                 for o in self._receivers(m.group(1)))
                    for name in self._receivers(m.group(2)):
                        self._store_number(name,
                                           self._operand_number(name) - amount,
                                           rounded)
                    return
                return

            if kind == "MULTIPLY":
                m = re.match(r"MULTIPLY\s+(.*?)\s+BY\s+(.*?)\s+GIVING\s+(.*)$",
                             text, re.I)
                if m:
                    product = (self._operand_number(m.group(1))
                               * self._operand_number(m.group(2)))
                    for name in self._receivers(m.group(3)):
                        self._store_number(name, product, rounded)
                    return
                m = re.match(r"MULTIPLY\s+(.*?)\s+BY\s+(.*)$", text, re.I)
                if m:
                    factor = self._operand_number(m.group(1))
                    for name in self._receivers(m.group(2)):
                        self._store_number(name,
                                           self._operand_number(name) * factor,
                                           rounded)
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
                    quotient = top / bottom if bottom else 0.0
                    for name in self._receivers(m.group(4)):
                        self._store_number(name, quotient, rounded)
                    if remainder:
                        self._store_number(remainder,
                                           top - bottom * int(quotient))
                    return
                m = re.match(r"DIVIDE\s+(.*?)\s+INTO\s+(.*)$", text, re.I)
                if m:
                    divisor = self._operand_number(m.group(1))
                    for name in self._receivers(m.group(2)):
                        top = self._operand_number(name)
                        self._store_number(name,
                                           top / divisor if divisor else 0.0,
                                           rounded)
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
        joined = "".join(out)
        name = target.split("(")[0].strip().upper()
        width = self._width(name)
        self.assign(name, joined[:width] if width else joined)

    def _initialize(self, stmt) -> None:
        """INITIALIZE sets every elementary item under an operand to its
        category's zero - numeric to 0, everything else to spaces.

        Treated as a no-op the operand keeps whatever the last record left in
        it, so a field the program has just cleared still compares equal to
        the value it held, and the direction that depends on it is unreachable.
        """
        import re
        text = norm(stmt.get("text", ""))
        # REPLACING/THRU phrases change *what* it writes, not that it writes.
        text = re.split(r"\bREPLACING\b", text, maxsplit=1, flags=re.I)[0]
        body = re.sub(r"^INITIALIZE\s+", "", text, flags=re.I)
        for name in self._receivers(body):
            name = name.split("(")[0].strip().upper()
            if not name or name in ("ALL", "TO", "VALUE"):
                continue
            children = [c for c in self.model.descendants(name)
                        if self.model.pic_of(c)]
            for field in (children or [name]):
                spec = (self.model.pic_of(field) or "").upper()
                blank = 0 if spec and "9" in spec and "X" not in spec else " "
                if field not in self._pinned:
                    self.state[field.upper()] = blank
                    self._note(field, None)
            if not children and name not in self._pinned:
                spec = (self.model.pic_of(name) or "").upper()
                self.state[name] = (0 if spec and "9" in spec and "X" not in spec
                                    else " ")
                self._note(name, None)


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
