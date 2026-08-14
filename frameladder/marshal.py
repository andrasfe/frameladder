"""Validators solved once, screens composed from the answers.

The residual on input-edit programs has one shape: a long cascade of field
validations feeding a first-match chain whose arms test the per-field
verdicts. Arm *k* needs a run where fields 1..k-1 all passed and field *k*
alone failed - an almost-all-valid screen. Every existing phase reasons at
whole-run granularity, so each of them pays the combinatorics of the whole
screen to move one field.

This phase changes the unit of work. COBOL programs of this shape do not
inline their edits; they call them, through a marshalling convention that
is visible in the statement stream and needs no naming knowledge to see::

    MOVE <field>    TO <work-in>       *> work-in is live-in to the range
    PERFORM <A> THRU <B>
    MOVE <work-out> TO <verdict>       *> work-out is written by the range

That is a typed call: payload in, verdict out. So the validator can be
lifted out and run *as a sub-program* - a `Program` holding only its own
paragraphs - over a small pool of candidate bytes, and what comes back is
a table from verdict to the bytes that produce it. The table is computed
once per distinct range and reused at every call site that performs it,
which is where the leverage is: measured on the program that motivated
this, 24 call sites are served by 8 ranges.

Composition is then arithmetic rather than search. Read the table's
"valid" entry for every site, push each answer back through the site's own
in-MOVE to the field it came from, and the result is one entry state in
which every edit passes. Spoiling is the same operation with one site's
entry swapped for a failing verdict - a linear number of runs across a
combinatorially large space.

Two properties are worth stating because they are what distinguish this
from the phases either side of it:

* **No predicate is ever inverted.** The validator is executed forward on
  a small domain, so its shape - class condition, literal table, range
  test, reference-modified LENGTH idiom, an intrinsic this module has
  never heard of - is not something this code needs to model. A validator
  whose verdicts the pool cannot reach is *reported*, not guessed at.
* **The pool is evidence, not invention.** Figurative constants and the
  PIC shape of the payload say what the field can physically hold; the
  literals the range itself compares against say what it distinguishes;
  a variable used as a reference-modification *length* is offered lengths
  within its base, because that idiom's whole point is that the length is
  a number rather than a byte string.

Nothing is credited here on this module's say-so: candidates are handed to
the battery's deduplicating ``run`` and a fresh interpreter decides.
"""

from __future__ import annotations

import copy
import re

from .cobol import Program
from .interpreter import Interpreter
from .liveness import live_in

# Bounded fan-out, the discipline the neighbouring phases document.
MAX_LOOKBACK = 12       # statements before a PERFORM that may marshal into it
MAX_LOOKAHEAD = 8       # statements after it that may marshal out
MAX_POOL = 40           # candidate byte strings per in-variable
MAX_INVARS = 4          # in-variables swept per range

_THRU = re.compile(r"\s+(?:THRU|THROUGH)\s+", re.I)
_LITERAL = re.compile(r"'([^']*)'|\"([^\"]*)\"")
_INTEGER = re.compile(r"\b\d{1,6}\b")
_WORD = re.compile(r"[A-Z0-9][A-Z0-9-]*", re.I)
# `NAME(1:LEN)` / `NAME (1 : LEN)` - the length operand of a reference
# modification. Its pool is numbers, never bytes.
_REFMOD = re.compile(r"([A-Z0-9][A-Z0-9-]*)\s*\(\s*[^():]*:\s*([^()]*?)\s*\)", re.I)

_FIGURATIVE = {
    "LOW-VALUES": "\x00", "LOW-VALUE": "\x00",
    "SPACES": " ", "SPACE": " ",
    "ZEROS": "0", "ZEROES": "0", "ZERO": "0",
    "HIGH-VALUES": "\xff", "HIGH-VALUE": "\xff",
    "QUOTES": '"', "QUOTE": '"',
}


# ---------------------------------------------------------------------------
# Reading the statement stream
# ---------------------------------------------------------------------------

def _walk(stmt):
    yield stmt
    for child in stmt.get("children") or []:
        yield from _walk(child)


def _statements(para):
    for stmt in para.get("statements", []):
        yield from _walk(stmt)


def _targets(attributes) -> list:
    """Every name a MOVE or SET writes, however the parser spelled it."""
    raw = attributes.get("targets") or attributes.get("names") \
        or attributes.get("name") or ""
    if isinstance(raw, str):
        raw = [part for part in re.split(r"[,\s]+", raw) if part]
    return [str(part).upper() for part in raw]


def _text_of(stmt) -> str:
    attributes = stmt.get("attributes") or {}
    return " ".join(str(part) for part in
                    (stmt.get("text"), attributes.get("condition"),
                     attributes.get("value")) if part)


class _Index:
    """Everything about one program this module reads more than once."""

    def __init__(self, program):
        self.program = program
        self.model = program.model
        self.names = [name.upper() for name in program.paragraph_names]
        self.paragraphs = {para["name"].upper(): para
                           for para in program.paragraphs}
        self._live: dict = {}
        self._writes: dict = {}
        self._width: dict = {}

    # -- data division ----------------------------------------------------
    def ancestors(self, name: str) -> set:
        out, current = set(), str(name).upper()
        parents = self.model.parent or {}
        for _hop in range(12):
            current = parents.get(current)
            if not current:
                break
            out.add(str(current).upper())
        return out

    def kin(self, name: str) -> set:
        """A written name, its 88-level parent, and every group above.

        A validator SETs an 88; the call site moves the *group* that 88
        lives in. Without the widening the two halves of the convention
        never meet.
        """
        out = {str(name).upper()}
        entry = (self.model.condition_names or {}).get(str(name).upper())
        if entry:
            out.add(str(entry[0]).upper())
        for one in list(out):
            out |= self.ancestors(one)
        return out

    def width(self, name: str) -> int:
        key = str(name).upper()
        if key not in self._width:
            try:
                from .lift import _width
                self._width[key] = int(_width(self.model, key) or 0)
            except Exception:                                # noqa: BLE001
                self._width[key] = 0
        return self._width[key]

    # -- procedure division ------------------------------------------------
    def live_in(self, para: str) -> set:
        if para not in self._live:
            try:
                self._live[para] = {name.upper()
                                    for name in live_in(self.program, para)}
            except Exception:                                # noqa: BLE001
                self._live[para] = set()
        return self._live[para]

    def writes(self, para: str) -> set:
        if para not in self._writes:
            out: set = set()
            for stmt in _statements(self.paragraphs.get(para, {})):
                if stmt.get("type") in ("MOVE", "SET"):
                    for target in _targets(stmt.get("attributes") or {}):
                        out |= self.kin(target)
            self._writes[para] = out
        return self._writes[para]

    def members(self, raw) -> tuple:
        """`PERFORM A THRU B` enters at A and runs the range - not a call
        to a paragraph named "A THRU B"."""
        parts = _THRU.split(str(raw or ""))
        head = parts[0].strip().upper()
        if head not in self.names:
            return ()
        start = self.names.index(head)
        if len(parts) < 2:
            return (head,)
        tail = parts[1].strip().upper()
        stop = self.names.index(tail) if tail in self.names else start
        if stop < start:
            return (head,)
        return tuple(self.names[start:stop + 1])


# ---------------------------------------------------------------------------
# The marshalling convention
# ---------------------------------------------------------------------------

def sites(program) -> list:
    """Every ``MOVE-in / PERFORM range / MOVE-out`` call site.

    Returned as ``{"host", "range", "ins", "outs"}`` where ``ins`` is
    ``[(source_field, work_variable)]`` and ``outs`` is
    ``[(work_variable, verdict_field)]``.

    The convention is recognised structurally: the written half of a
    preceding MOVE must be live-in to the range (the range reads it before
    writing it, so it is a parameter), and the read half of a following
    MOVE must be something the range writes (so it is a result). Both
    halves are required - a MOVE that merely happens to sit next to a
    PERFORM satisfies neither.
    """
    index = _Index(program)
    out = []
    for host, para in index.paragraphs.items():
        sequence = list(para.get("statements", []))
        for position, stmt in enumerate(sequence):
            if stmt.get("type") != "PERFORM":
                continue
            attributes = stmt.get("attributes") or {}
            if attributes.get("until") or attributes.get("times") \
                    or attributes.get("varying"):
                # A repeated PERFORM is a loop, not a call with a verdict.
                continue
            members = index.members(attributes.get("target"))
            if not members:
                continue
            parameters: set = set()
            results: set = set()
            for member in members:
                parameters |= index.live_in(member)
                results |= index.writes(member)
            ins, outs = [], []
            for back in range(position - 1, max(-1, position - 1 - MAX_LOOKBACK), -1):
                previous = sequence[back]
                if previous.get("type") != "MOVE":
                    break
                fields = previous.get("attributes") or {}
                source = str(fields.get("source") or "").upper()
                for target in _targets(fields):
                    if target in parameters:
                        ins.append((source, target))
            for ahead in range(position + 1,
                               min(len(sequence), position + 1 + MAX_LOOKAHEAD)):
                following = sequence[ahead]
                if following.get("type") != "MOVE":
                    break
                fields = following.get("attributes") or {}
                source = str(fields.get("source") or "").upper()
                if source in results:
                    for target in _targets(fields):
                        outs.append((source, target))
            if ins and outs:
                out.append({"host": host, "range": members,
                            "ins": ins, "outs": outs})
    return out


# ---------------------------------------------------------------------------
# Candidate values
# ---------------------------------------------------------------------------

def _length_operands(index, members) -> set:
    """Variables used as the *length* of a reference modification.

    ``X(1:N)`` makes N a number of bytes. Offering it byte strings - which
    is what its PIC would suggest - lands a length of zero and every edit
    downstream reports the field empty, whatever the payload holds. The
    idiom is recognised from the statement text, not from the name.
    """
    out: set = set()
    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            for match in _REFMOD.finditer(_text_of(stmt)):
                for word in _WORD.findall(match.group(2) or ""):
                    name = word.upper()
                    if index.model.knows(name):
                        out.add(name)
    return out


def _pool(index, members, name, lengths) -> list:
    """Candidate values for one in-variable of one range."""
    width = index.width(name) or 8
    candidates: list = []
    if name in lengths:
        # A length operand measures some other field, so the numbers that
        # matter are the offsets inside the widest field the range names,
        # plus the degenerate ends.
        reach = max((index.width(other)
                     for other in _referenced_names(index, members)),
                    default=0)
        top = max(reach, width, 1)
        for number in sorted({1, 2, max(1, top // 2), max(1, top - 1), top}):
            candidates.append(number)
        return candidates[:MAX_POOL]
    # Degenerate and shape-driven bytes.
    for filler in ("\x00", " ", "0", "1", "9", "A"):
        candidates.append(filler * width)
    candidates.append(("A" * (width // 2) + "1" * (width - width // 2)))
    # Whatever the range itself compares against.
    seen: set = set()
    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            body = _text_of(stmt)
            for match in _LITERAL.finditer(body):
                literal = match.group(1) if match.group(1) is not None \
                    else match.group(2)
                if literal is None or literal in seen:
                    continue
                seen.add(literal)
                candidates.append((literal + " " * width)[:width])
            for word in _WORD.findall(body):
                figurative = _FIGURATIVE.get(word.upper())
                if figurative and figurative * width not in candidates:
                    candidates.append(figurative * width)
    # Integers the range names, and their neighbours - the boundaries of any
    # range test it applies.
    numbers: set = set()
    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            for token in _INTEGER.findall(_text_of(stmt)):
                numbers.add(int(token))
    for number in sorted(numbers)[:8]:
        for step in (-1, 0, 1):
            value = max(0, number + step)
            candidates.append(str(value).rjust(width, "0")[-width:])
    unique, marks = [], set()
    for candidate in candidates:
        mark = repr(candidate)
        if mark not in marks:
            marks.add(mark)
            unique.append(candidate)
    return unique[:MAX_POOL]


def _referenced_names(index, members) -> set:
    out: set = set()
    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            for word in _WORD.findall(_text_of(stmt)):
                if index.model.knows(word.upper()):
                    out.add(word.upper())
    return out


# ---------------------------------------------------------------------------
# Micro-execution
# ---------------------------------------------------------------------------

def _sub_program(index, members):
    """The range, alone, as a program that can be run."""
    paragraphs = [copy.deepcopy(index.paragraphs[member])
                  for member in members if member in index.paragraphs]
    return Program(index.program.name, paragraphs, index.model,
                   getattr(index.program, "source_path", None))


def _verdicts(index, members) -> set:
    """The 88-levels the range SETs - its result vocabulary."""
    out: set = set()
    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            if stmt.get("type") != "SET":
                continue
            for target in _targets(stmt.get("attributes") or {}):
                if target in (index.model.condition_names or {}):
                    out.add(target)
    return out


def _holds(index, verdict, state) -> bool:
    parent, values = (index.model.condition_names or {})[verdict]
    try:
        current = state.get(str(parent).upper())
    except Exception:                                        # noqa: BLE001
        return False
    if current is None:
        return False
    for raw in values:
        wanted = str(raw).strip()
        wanted = _FIGURATIVE.get(wanted.upper(), wanted.strip("'\""))
        if str(current).rstrip() == wanted.rstrip():
            return True
    return False


def outcome_table(program, members, cache=None, index=None,
                  work_variables=None) -> dict:
    """``{verdict_88: {in_variable: value}}`` for one validator range.

    Built by running the range as a sub-program over the candidate pool of
    each of its in-variables in turn. Memoised in ``cache`` on the range,
    which is the whole economy of this phase: distinct ranges are far
    fewer than call sites.

    ``work_variables`` is what the call sites actually marshal in. Without
    it the sweep falls back to the range's whole live-in set, which on a
    validator that reads its own result flags is mostly noise and crowds
    the real payload out of the cap.

    A reference-modification length is swept *around* the payload rather
    than beside it: the two are one idiom, and a payload read through a
    length of zero is indistinguishable from an empty field however good
    the payload is.
    """
    key = tuple(members)
    if cache is not None and key in cache:
        return cache[key]
    index = index or _Index(program)
    verdicts = _verdicts(index, members)
    table: dict = {}
    if not verdicts:
        if cache is not None:
            cache[key] = table
        return table
    parameters: set = set()
    for member in members:
        parameters |= index.live_in(member)
    wanted = {name.upper() for name in (work_variables or ())}
    parameters |= wanted
    lengths = _length_operands(index, members)
    known = sorted(name for name in parameters if index.model.knows(name))
    # What a call site marshals in is a payload on the program's own say-so;
    # the rest of the live-in set is a fallback for the sites whose in-MOVE
    # the convention did not see. Marshalled first so the cap never spends
    # itself on the fallback.
    payloads = [name for name in known if name not in lengths and name in wanted]
    payloads += [name for name in known
                 if name not in lengths and name not in wanted]
    payloads = payloads[:MAX_INVARS]
    length_vars = [name for name in sorted(parameters | lengths)
                   if name in lengths and index.model.knows(name)][:2]
    neutral = {name: " " * (index.width(name) or 8) for name in known
               if name not in lengths}
    # Every length assignment the idiom admits becomes a context the whole
    # payload pool is swept under. Bounded: |lengths| is at most two and
    # each pool is a handful of numbers.
    contexts = [{}]
    for name in length_vars:
        grown = []
        for context in contexts:
            for value in _pool(index, members, name, lengths):
                merged = dict(context)
                merged[name] = value
                grown.append(merged)
        contexts = grown[:MAX_POOL]
    sub = _sub_program(index, members)
    for context in contexts:
        for name in payloads:
            for candidate in _pool(index, members, name, lengths):
                state = dict(neutral)
                state.update(context)
                state[name] = candidate
                try:
                    interpreter = Interpreter(sub, dict(state))
                    interpreter.run(members[0])
                except Exception:                            # noqa: BLE001
                    continue
                for verdict in verdicts:
                    if verdict in table:
                        continue
                    if _holds(index, verdict, interpreter.state):
                        table[verdict] = dict(state)
    if cache is not None:
        cache[key] = table
    return table


# ---------------------------------------------------------------------------
# Composition
# ---------------------------------------------------------------------------

def _set_depth(index, members, verdict) -> int:
    """How far into the range the latest statement setting ``verdict`` is.

    A validator initialises its failure verdict at the top and confirms
    the pass at the bottom: the failure arms bail out early, so the
    statement that survives to the end of the range is the pass. Position
    within the range - not the name on the flag - is what says so.
    """
    best = -1
    for order, member in enumerate(members):
        for stmt in _statements(index.paragraphs.get(member, {})):
            if stmt.get("type") != "SET":
                continue
            if verdict in _targets(stmt.get("attributes") or {}):
                best = max(best, order * 100000 + int(stmt.get("line_start", 0)))
    return best


def _pass_rank(index, members, verdict, table):
    """Order a range's verdicts, pass first, on structure alone.

    Two signals, both mechanical and both about the shape of a cascade
    rather than about any name:

    * **How many guards the producing run evaluated.** Passing means every
      check in the range was reached and none of them bailed out, so the
      pass state is the one whose run saw the most decisions.
    * **How deep in the range its setting statement sits.** A validator
      sets its failure verdict defensively at the top and confirms success
      at the bottom, so among runs that saw equally many guards, the
      verdict written latest is the pass.

    Ties beyond that fall back to the verdict's own text purely so the
    order is stable between runs.
    """
    state = table.get(verdict)
    if state is None:
        return (1, 0, 0, verdict)
    sub = _sub_program(index, members)
    try:
        interpreter = Interpreter(sub, dict(state))
        trace = interpreter.run(members[0])
    except Exception:                                        # noqa: BLE001
        return (1, 0, 0, verdict)
    return (0, -len(trace.guards), -_set_depth(index, members, verdict),
            verdict)


MAX_PLACE_DEPTH = 4


def _place(index, prov, field, depth=0, seen=frozenset()) -> list:
    """The fields an entry state must hold for ``field`` to carry a value.

    The in-MOVE's source is where the *validator* reads from, which is not
    generally where the value can be *put*. On a screen program every one
    of those fields is rebuilt from the map on each cycle - measured: 22
    of 22 on the program that motivated this module, all MOVE-written by
    the receive paragraph - so an entry state that sets them is overwritten
    before the first edit runs, and the composed screen is inert.

    So the placement walks back along the MOVE chain: a field the program
    itself writes cannot be pinned at entry, but the field it copies *from*
    might be. The walk stops at the first field nothing MOVEs into, which
    is the one the outside world delivers and the entry state owns.
    Bounded, and it never returns a field the program overwrites.
    """
    name = str(field).upper()
    if depth > MAX_PLACE_DEPTH or name in seen or prov is None:
        return [name]
    seen = seen | {name}
    writers = []
    try:
        writers = list(prov.writes_to(name))
    except Exception:                                        # noqa: BLE001
        return [name]
    movers = [w for w in writers if w.kind == "MOVE" and getattr(w, "source", None)]
    if not movers:
        # Nothing copies into it: either the outside world delivers it or
        # the entry state does. Either way this is where the value goes.
        return [name]
    out: list = []
    for writer in movers[:3]:
        from .ir import parse_term
        try:
            source = parse_term(writer.source)
        except Exception:                                    # noqa: BLE001
            continue
        if source.kind != "var" or source.refmod:
            continue
        if not index.model.knows(source.name):
            continue
        if index.width(source.name) != index.width(name):
            # A differently-sized source lands the bytes at the wrong
            # offset; the value would be silently truncated or padded.
            continue
        for placed in _place(index, prov, source.name, depth + 1, seen):
            if placed not in out:
                out.append(placed)
    return out or [name]


def compose(program, site_list, tables, spoil=None, index=None,
            prov=None) -> dict:
    """One entry state in which every site's edit passes.

    ``spoil`` is ``(site_index, verdict)``; that one site is given that
    verdict's bytes instead of its passing ones, which is what puts a
    first-match chain on the arm that tests it.

    The value found for a work variable is pushed back through the site's
    own in-MOVE onto the field it was moved from, because that field is
    what the entry state owns. Where the in-MOVE's source is a literal
    (a message name, not a payload) there is nothing to place and the pair
    is skipped.
    """
    index = index or _Index(program)
    state: dict = {}
    for position, site in enumerate(site_list):
        table = tables.get(tuple(site["range"])) or {}
        if not table:
            continue
        ranked = sorted(table, key=lambda v: _pass_rank(index, site["range"],
                                                        v, table))
        if not ranked:
            continue
        wanted = ranked[0]
        if spoil is not None and position == spoil[0]:
            # The caller names *which* failure to stage. Taking merely the
            # first would collapse every site sharing a validator onto one
            # state, and the deduplicating `run` would then throw away all
            # but one of them - measured as 73 variants becoming 24 runs.
            wanted = spoil[1] if spoil[1] in table else None
            if wanted is None:
                continue
        answer = table[wanted]
        for source, work in site["ins"]:
            if work not in answer:
                continue
            if not source or source.startswith("'") or source.startswith('"'):
                continue
            if not index.model.knows(source):
                continue
            for placed in _place(index, prov, source):
                state[placed] = answer[work]
    return state


def spoil_variants(program, site_list, tables, index=None) -> list:
    """``(site_index, failing_verdict)`` for every site with a failure to
    offer - the one-field-spoiled family, one entry per site."""
    index = index or _Index(program)
    out = []
    for position, site in enumerate(site_list):
        table = tables.get(tuple(site["range"])) or {}
        ranked = sorted(table, key=lambda v: _pass_rank(index, site["range"],
                                                        v, table))
        for verdict in ranked[1:]:
            out.append((position, verdict))
    return out


# ---------------------------------------------------------------------------
# The phase
# ---------------------------------------------------------------------------

def _ledger_bases(ledger, site_list, limit=4) -> list:
    """Recipes that demonstrably ran the edits, from the ledger.

    A composed screen says what the fields hold; it does not say how the
    program came to read them. On a conversational program the edits sit
    behind a fetch: the first cycle validates a search key and leaves,
    and only a run that arrives with the record already fetched reaches
    the per-field cascade at all. Merged over a bare entry state the
    composed screen is inert, and measured that way it was - the run
    stopped at the fetch guard every time, whatever the screen held.

    A witness whose direction lies *inside* a validator range, or in the
    paragraph that hosts a call site, is exactly the evidence wanted: the
    ledger already holds a recipe that got there. Cheapest first, because
    a witness should demand the least staging a harness must reproduce.
    """
    if ledger is None:
        return []
    wanted: set = set()
    for site in site_list:
        wanted.add(site["host"])
        wanted |= set(site["range"])
    ranked = []
    for key, recipe in (getattr(ledger, "witnesses", None) or {}).items():
        paragraph = key[0] if isinstance(key, tuple) else None
        if paragraph not in wanted:
            continue
        payload = recipe.payload()
        ranked.append((len(payload.get("input_state") or {}),
                       (payload.get("input_state") or {},
                        payload.get("world"), payload.get("stubs"),
                        payload.get("terminals"))))
    ranked.sort(key=lambda item: item[0])
    out, marks = [], set()
    for _cost, base in ranked:
        mark = repr(base)
        if mark in marks:
            continue
        marks.add(mark)
        out.append(base)
        if len(out) >= limit:
            break
    return out


def marshal(program, ledger, run, *, budget: int = 120, on_witness=None,
            bases=None, prov=None, verbose=False) -> dict:
    """Compose an all-valid screen, then spoil one field at a time.

    ``run`` is the battery's crediting closure, so every direction claimed
    here is claimed by a fresh interpreter replaying a stored recipe.
    ``bases`` supplies recipes to merge the composed entry state over -
    the composed state says what the *screen* holds and a base says how the
    program got to the point of reading it, and neither is much use alone.

    Negatives are reported rather than absorbed: ``no_sites`` when the
    convention finds nothing, ``no_table`` per range whose verdicts the
    pool could not reach, ``unreachable`` per verdict with no candidate.
    """
    index = _Index(program)
    stats = {"budget": budget, "runs": 0, "sites": 0, "ranges": 0,
             "verdicts": 0, "reached": 0, "composed": 0, "spoils": 0,
             "unreached": []}
    site_list = sites(program)
    stats["sites"] = len(site_list)
    if not site_list:
        stats["reason"] = "no_sites"
        return stats
    distinct = sorted({tuple(site["range"]) for site in site_list})
    stats["ranges"] = len(distinct)
    cache: dict = {}
    for members in distinct:
        table = outcome_table(program, members, cache=cache, index=index)
        verdicts = _verdicts(index, members)
        stats["verdicts"] += len(verdicts)
        stats["reached"] += len(table)
        for verdict in sorted(verdicts - set(table)):
            stats["unreached"].append({"range": members[0],
                                       "verdict": verdict})
    tables = dict(cache)
    if not any(tables.values()):
        stats["reason"] = "no_table"
        return stats

    spent = [0]

    def offer(state, base, tag):
        if spent[0] >= budget:
            return
        merged = dict(base[0] or {})
        merged.update(state)
        outcome = run(merged, base[1], base[2], base[3], "marshal:%s" % tag)
        if outcome is not None:
            spent[0] += 1
            if on_witness is not None:
                on_witness((merged, base[1], base[2], base[3]))

    # The ledger's own reach comes first: a recipe that witnessed a
    # direction inside an edit is a recipe that ran the edit.
    base_list = _ledger_bases(ledger, site_list)
    stats["bases_from_ledger"] = len(base_list)
    base_list += list(bases or [({}, "populated", None, None)])
    valid = compose(program, site_list, tables, index=index, prov=prov)
    if valid:
        stats["composed"] = len(valid)
        for base in base_list:
            offer(valid, base, "valid")
    for position, verdict in spoil_variants(program, site_list, tables,
                                            index=index):
        if spent[0] >= budget:
            break
        spoiled = compose(program, site_list, tables,
                          spoil=(position, verdict), index=index, prov=prov)
        if not spoiled:
            continue
        stats["spoils"] += 1
        for base in base_list[:2]:
            offer(spoiled, base, "spoil@%d:%s" % (position, verdict))
    stats["runs"] = spent[0]
    return stats
