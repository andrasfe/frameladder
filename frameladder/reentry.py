"""Entry states shaped to complete cycle 1 and re-enter.

A pseudo-conversational program does not run once. ``EXEC CICS RETURN
TRANSID(T) COMMAREA(C)`` ends the task and asks CICS to start T again on the
next terminal input, handing back C - so the program re-enters from the top
holding the state it saved, with the key the user pressed in EIBAID and the
map fields the user typed arriving at RECEIVE. The interpreter models the
re-entry (``interpreter.MAX_TASKS``), but the witness battery's entry states
were all single-cycle-shaped: nothing arranged for a run to complete cycle 1
*and* arrive at cycle 2 holding what a re-entered task holds. Every direction
guarded by second-cycle state - the re-enter flag cycle 1 writes into the
commarea, the AID dispatch, validation of received fields - stayed dark, not
because no recipe exists but because no run was shaped to be one.

Everything here is evidence from this program's own text:

- the ``RETURN TRANSID`` statement says the program re-enters at all, and
  its ``COMMAREA`` operand says which area survives the boundary;
- the DFHAID names the source compares say which attention keys it
  distinguishes - the byte each name stands for is platform vocabulary
  (``ir.AID_VALUES``), fixed by CICS the way HTTP status codes are fixed,
  but *which* names matter comes from the comparisons the program wrote;
- the ``RECEIVE`` statements say which areas arrive from the terminal;
- the program's own literals (and its ``IS NUMERIC`` class tests) say what
  those fields could usefully hold.

No naming conventions anywhere: a field is an AID field because the source
compares it against a DFHAID name, never because it is called EIBAID.

A recipe built here spans several tasks and is still one recipe - one entry
state, one stub series - because the interpreter replays the whole
pseudo-conversation deterministically from it.
"""

from __future__ import annotations

import re

from .conditions import CLASS_OP, CLASS_OP_NOT, condition_atoms, when_condition
from .ir import AID_VALUES, base_name, norm, parse_term

_TRANSID = re.compile(r"\bTRANSID\s*\(", re.I)
_COMMAREA = re.compile(r"\bCOMMAREA\s*\(\s*([A-Z0-9-]+)", re.I)
_WORD = re.compile(r"[A-Z0-9][A-Z0-9-]*")


def _statements(program):
    def walk(stmt):
        yield stmt
        for child in stmt.get("children") or []:
            yield from walk(child)

    for para in program.paragraphs:
        for stmt in para.get("statements", []):
            yield from walk(stmt)


def return_commareas(program) -> list:
    """The areas saved at ``EXEC CICS RETURN TRANSID(...)``.

    Empty when the program never returns with a TRANSID - it is not
    pseudo-conversational and there is no second cycle to shape a run for.
    This is the evidence gate for the whole module.
    """
    from .provenance import op_key
    out: list = []
    for stmt in _statements(program):
        text = norm(stmt.get("text", "") or "")
        if not text or op_key(text) != "EXEC:CICS:RETURN":
            continue
        if not _TRANSID.search(text):
            continue
        m = _COMMAREA.search(text)
        name = m.group(1).upper() if m else ""
        if name not in out:
            out.append(name)
    return out


def commarea_targets(program) -> list:
    """The areas the program copies its commarea into.

    ``MOVE DFHCOMMAREA(...) TO <area>`` names where the caller-staged (or
    cycle-saved) state actually lives - and it is better evidence than the
    RETURN area's own fields, because a program that assembles its saved
    state by byte slices returns a childless ``PIC X(n)`` whose fields
    only exist on the receiving side of this move.
    """
    from .ir import move_targets
    out: list = []
    for stmt in _statements(program):
        if stmt.get("type") != "MOVE":
            continue
        attrs = stmt.get("attributes", {}) or {}
        source = parse_term(attrs.get("source", "") or "")
        if source.kind != "var" or base_name(source.name) != "DFHCOMMAREA":
            continue
        for name in move_targets(attrs.get("targets", "") or ""):
            if name not in out:
                out.append(name)
    return out


def aid_comparisons(program) -> dict:
    """Which fields the source compares against attention identifiers, and
    the key bytes it distinguishes: ``{field: [value, ...]}`` in source order.

    ``EVALUATE EIBAID WHEN DFHPF3`` names the subject and the key; an IF
    names both inside one condition. Either way the DFHAID name must appear
    in the program's own text - the table in :mod:`frameladder.ir` only says
    what byte the name stands for.
    """
    out: dict = {}

    def note(var: str, value: str) -> None:
        values = out.setdefault(var, [])
        if value not in values:
            values.append(value)

    for condition in _conditions(program):
        names = [w for w in _WORD.findall(condition.upper())
                 if w in AID_VALUES]
        if not names:
            continue
        # The parser already resolved the DFHAID name to its byte, so the
        # atom's constant side holds the byte; requiring the name in the
        # raw text above is what stops a plain literal '3' from counting
        # as a key comparison.
        wanted = {AID_VALUES[n] for n in names}
        try:
            alternatives = condition_atoms(condition)
        except Exception:                                    # noqa: BLE001
            continue
        for alt in alternatives:
            for atom in alt:
                for side, other in ((atom.lhs, atom.rhs),
                                    (atom.rhs, atom.lhs)):
                    if side.kind == "var" and other.kind == "const" \
                            and other.value in wanted:
                        note(side.name, other.value)
    return out


def _conditions(program):
    """Every condition the program states, WHEN arms restored to whole
    conditions - ``EVALUATE EIBAID WHEN DFHPF3`` and ``EVALUATE TRUE WHEN
    EIBAID = DFHENTER`` both come out as comparisons."""
    for stmt in _statements(program):
        kind = stmt.get("type", "")
        attrs = stmt.get("attributes", {}) or {}
        if kind == "IF":
            condition = attrs.get("condition", "") or ""
            if condition:
                yield condition
        elif kind == "EVALUATE":
            subject = attrs.get("subject", "") or ""
            for arm in stmt.get("children") or []:
                if arm.get("type") != "WHEN":
                    continue
                value = arm.get("attributes", {}).get("value", "") or ""
                if value and norm(value).upper() != "OTHER":
                    yield when_condition(subject, value)


def terminal_areas(program) -> list:
    """The areas terminal input arrives in - what RECEIVE fills."""
    return _output_areas(program, ("EXEC:CICS:RECEIVE",))


def stub_areas(program) -> list:
    """Every area an external operation writes - RECEIVE maps, READ INTO
    records, CALL USING parameters, SQL host variables.

    In the bare world those operations deliver nothing, so the area keeps
    whatever the entry state gave it: naming a field here is how a recipe
    says "the record the read would have delivered holds this". The staged
    worlds overwrite only the status fields, so the same values stand
    there too.
    """
    return _output_areas(program, ("EXEC:", "CALL:"))


def _output_areas(program, prefixes) -> list:
    from .provenance import op_key, stub_outputs
    out: list = []
    for stmt in _statements(program):
        text = norm(stmt.get("text", "") or "")
        if not text or not op_key(text).startswith(tuple(prefixes)):
            continue
        for area in stub_outputs(text):
            if area not in out:
                out.append(area)
    return out


def numeric_tested(program) -> set:
    """Base names of fields the source class-tests with ``IS [NOT] NUMERIC``.

    A class test constrains the shape of a value rather than its value, so
    the program's literal pool says nothing about satisfying it - digits
    sized to the PIC do.
    """
    out: set = set()
    for condition in _conditions(program):
        try:
            alternatives = condition_atoms(condition)
        except Exception:                                    # noqa: BLE001
            continue
        for alt in alternatives:
            for atom in alt:
                if atom.op in (CLASS_OP, CLASS_OP_NOT) \
                        and atom.rhs.kind == "const" \
                        and atom.rhs.value == "NUMERIC" \
                        and atom.lhs.kind == "var":
                    out.add(base_name(atom.lhs.name))
    return out


_ORDERING = {">", ">=", "<", "<="}


def _boundary_values(program) -> dict:
    """Values that step past an ordering comparison, per base name.

    ``IF CDEMO-CU00-PAGE-NUM > 1`` names the boundary and neither side of
    it; the literal pool keeps only the 1. One step either side of every
    numeric literal the field is order-compared against covers both
    directions of the comparison - evidence-derived boundary values, the
    same idea the divergence families spend on free slots.
    """
    out: dict = {}
    for condition in _conditions(program):
        try:
            alternatives = condition_atoms(condition)
        except Exception:                                    # noqa: BLE001
            continue
        for alt in alternatives:
            for atom in alt:
                if atom.op not in _ORDERING:
                    continue
                for side, other in ((atom.lhs, atom.rhs),
                                    (atom.rhs, atom.lhs)):
                    if side.kind != "var" or other.kind != "const" \
                            or isinstance(other.value, bool) \
                            or not isinstance(other.value, (int, float)):
                        continue
                    values = out.setdefault(base_name(side.name), [])
                    for candidate in (other.value + 1, other.value - 1):
                        if candidate >= 0 and candidate not in values:
                            values.append(candidate)
    return out


def _refmod_templates(program) -> dict:
    """A value assembled from every byte-range test the source states.

    ``TORIGDTI(1:4) IS NUMERIC``, ``(5:1) NOT EQUAL '-'``, ``(6:2)
    NUMERIC``, ``(8:1) NOT EQUAL '-'``, ``(9:2) NUMERIC`` is the program
    spelling out, one slice at a time, what a well-formed value looks like:
    ``1111-11-11``. Each equality places its literal (a disequality names
    the byte the valid value *has* - the arm fires on the malformed one),
    each NUMERIC slice places digits, and the whole is a candidate no
    single literal in the pool resembles.
    """
    pieces: dict = {}
    for condition in _conditions(program):
        try:
            alternatives = condition_atoms(condition)
        except Exception:                                    # noqa: BLE001
            continue
        for alt in alternatives:
            for atom in alt:
                for side, other in ((atom.lhs, atom.rhs),
                                    (atom.rhs, atom.lhs)):
                    if side.kind != "var" or not side.refmod \
                            or other.kind != "const":
                        continue
                    try:
                        start = int(str(side.refmod[0]))
                        length = int(str(side.refmod[1]))
                    except (TypeError, ValueError, IndexError):
                        continue
                    if start < 1 or length < 1 or start + length > 64:
                        continue
                    text = None
                    if atom.op in (CLASS_OP, CLASS_OP_NOT) \
                            and other.value == "NUMERIC":
                        text = "1" * length
                    elif atom.op in ("=", "!=") \
                            and isinstance(other.value, str) \
                            and len(other.value) == length:
                        text = other.value
                    if text is None:
                        continue
                    pieces.setdefault(base_name(side.name), {})[start] = text
    out: dict = {}
    for base, parts in pieces.items():
        if len(parts) < 2:
            continue                     # one slice is not a shape
        width = max(start + len(text) - 1 for start, text in parts.items())
        chars = ["1"] * width
        for start, text in sorted(parts.items()):
            chars[start - 1:start - 1 + len(text)] = list(text)
        out[base] = "".join(chars)
    return out


def _move_targets_of(program) -> dict:
    """One hop of the program's own MOVEs: source base name -> target bases.

    A received field is rarely compared directly; the program moves it
    somewhere and compares *that*. ``MOVE SEL0001I ... TO
    CDEMO-CU00-USR-SEL-FLG`` followed by ``EVALUATE CDEMO-CU00-USR-SEL-FLG
    WHEN 'U'`` means 'U' is a value worth typing into SEL0001I - the
    program's own dataflow says so, one hop is cheap, and the full version
    of this walk is what provenance does for the planner.
    """
    from .ir import move_targets
    out: dict = {}
    for stmt in _statements(program):
        if stmt.get("type") != "MOVE":
            continue
        attrs = stmt.get("attributes", {}) or {}
        source = parse_term(attrs.get("source", "") or "")
        if source.kind != "var":
            continue
        targets = out.setdefault(base_name(source.name), set())
        for name in move_targets(attrs.get("targets", "") or ""):
            targets.add(base_name(name))
    return out


def resp_fault_worlds(program, pool, positions=(0, 1, 2),
                      max_worlds: int = 120) -> list:
    """Worlds where one EXEC operation answers one of its own codes once.

    ``sequences.fault_worlds`` walks the fault axis for operations a
    ``SELECT ... FILE STATUS`` speaks for; a CICS screen program has none,
    so its RESP dispatch arms - ``WHEN DFHRESP(NOTFND)``, ``WHEN OTHER``,
    per file paragraph - had no world that could take them. Same design,
    other channel: the operation succeeds ``position`` times, answers the
    code once, and succeeds after, so the paragraphs downstream of an
    earlier success stay reachable. Which operations have a status channel
    comes from the ``RESP(...)`` operand (`conformance_defaults.
    exec_channels`, evidence not naming), and the codes are the ones the
    program compares that field against.
    """
    from .conformance_defaults import _CHANNEL_OK, exec_channels
    by_base: dict = {}
    for name, values in (pool or {}).items():
        by_base.setdefault(base_name(name), list(values))
    out: list = []
    for key, channels in sorted(exec_channels(program).items()):
        for var, channel in sorted(channels.items()):
            ok = _CHANNEL_OK.get(channel, 0)
            codes = [v for v in by_base.get(base_name(var), ())
                     if isinstance(v, (int, float))
                     and not isinstance(v, bool) and v != ok]
            for code in codes[:6]:
                for position in positions:
                    entries = [{"when": {}, "set": {var: ok}, "seq": i}
                               for i in range(position)]
                    entries.append({"when": {}, "set": {var: code},
                                    "seq": position})
                    out.append({"name": "%s@%d:%s=%r" % (key, position,
                                                         var, code),
                                "world": "populated",
                                "stubs": {key: entries},
                                "terminals": {key: {var: ok}}})
                    if len(out) >= max_worlds:
                        return out
    return out


def _entry_conditions(program, entry: str = ""):
    """Conditions stated by the entry paragraph itself - the dispatch."""
    wanted = (entry or (program.paragraphs[0]["name"]
                        if program.paragraphs else "")).upper()
    for para in program.paragraphs:
        if para["name"].upper() != wanted:
            continue
        for stmt in para.get("statements", []):
            def walk(node):
                kind = node.get("type", "")
                attrs = node.get("attributes", {}) or {}
                if kind == "IF" and attrs.get("condition"):
                    yield attrs["condition"]
                elif kind == "EVALUATE":
                    subject = attrs.get("subject", "") or ""
                    for arm in node.get("children") or []:
                        if arm.get("type") != "WHEN":
                            continue
                        value = arm.get("attributes", {}).get("value", "") or ""
                        if value and norm(value).upper() != "OTHER":
                            yield when_condition(subject, value)
                for child in node.get("children") or []:
                    yield from walk(child)
            yield from walk(stmt)


def _mode_field(program, fields: dict, exclude) -> str:
    """The one field whose value the entry paragraph dispatches on.

    A pseudo-conversational program keeps a state machine in its commarea
    - which screen was shown, whether details were fetched, whether the
    user confirmed - and the entry paragraph's own conditions name the
    field that holds it. Evidence, not naming: the field must be one the
    battery already fills, tested by the dispatch itself, with the most
    distinct values, because more values means more of the program hangs
    off it.
    """
    condition_names = getattr(program.model, "condition_names", {}) or {}
    tested: set = set()
    for condition in _entry_conditions(program):
        try:
            alternatives = condition_atoms(condition)
        except Exception:                                    # noqa: BLE001
            continue
        for alt in alternatives:
            for atom in alt:
                for side in (atom.lhs, atom.rhs):
                    if side.kind != "var":
                        continue
                    name = base_name(side.name)
                    # An entry dispatch written over 88-level names tests
                    # the *parent* - `WHEN ACUP-SHOW-DETAILS` is a value
                    # of ACUP-CHANGE-ACTION.
                    entry = condition_names.get(name) \
                        or condition_names.get(side.name.upper())
                    if entry:
                        name = base_name(entry[0])
                    tested.add(name)
    tested &= set(fields)
    tested -= set(exclude)
    if not tested:
        return ""
    return max(sorted(tested), key=lambda name: len(fields[name]))


def _commarea_width(program, areas) -> int:
    """EIBCALEN for a task that arrived holding a commarea.

    The honest value is the width of the area the program itself returns,
    because that is what the next task's EIBCALEN would be - and it is what
    the interpreter hands re-entered tasks. 100 only when no layout says.
    """
    from .storage import layout_of
    try:
        layout = layout_of(program.model)
    except Exception:                                        # noqa: BLE001
        return 0
    for area in areas:
        if not area:
            continue
        slot = layout.slot_for(area)
        if slot is not None and getattr(slot, "length", 0):
            return slot.length
    return 0


def _field_values(program, pool, areas) -> dict:
    """Candidate values for the fields a re-entered task arrives holding.

    Two families, both evidenced: fields of the terminal-input areas (what
    the user typed) and fields of the saved commarea (what the first caller
    handed over). A field earns a place only when the program compares it
    against something (it is in the literal pool) or class-tests it - a
    field with no evidence gets no invented value.
    """
    from .heuristics import conforming_value
    by_base: dict = {}
    for name, values in (pool or {}).items():
        by_base.setdefault(base_name(name), list(values))
    digits = numeric_tested(program)
    boundaries = _boundary_values(program)
    moved_to = _move_targets_of(program)

    templates = _refmod_templates(program)

    def candidates(base: str) -> list:
        """Everything the program's own text says this field could hold:
        the shape its byte-range tests assemble, the literals it is
        compared against, digits (and a value that fails the digits test
        without being blank) when it is class-tested, one step past any
        ordering bound - and the same, one MOVE hop downstream."""
        values = list(by_base.get(base, ()))
        reached = [base] + sorted(moved_to.get(base, ()))
        for name in reached:
            if name in digits:
                value = conforming_value(program.model.pic_of(base), "NUMERIC")
                if value is not None and value not in values:
                    values.insert(0, value)
                # The class test has three outcomes worth a witness: digits,
                # blank (the pool has it), and a non-blank value that fails
                # - which no literal evidences, so it is constructed the
                # way `conforming_value` constructs the passing one.
                spoiler = conforming_value(program.model.pic_of(base),
                                           "ALPHABETIC")
                if spoiler is not None and spoiler not in values:
                    values.append(spoiler)
                break
        for name in reached:
            if name in templates and templates[name] not in values:
                values.insert(0, templates[name])
                break
        for name in reached[1:]:
            for value in by_base.get(name, ()):
                if value not in values:
                    values.append(value)
        for name in reached:
            for value in boundaries.get(name, ()):
                if value not in values:
                    values.append(value)
        return values

    out: dict = {}
    for area in list(stub_areas(program)) + list(areas):
        for name in [area] + list(program.model.descendants(area)):
            base = base_name(name)
            if "#" in base or base in out:                   # FILLER
                continue
            values = candidates(base)
            if values:
                out[base] = values
    return out


def _filled(values) -> object:
    """The value most likely to *be* input: the first that is not blank.

    A re-entered task exists because the user typed something; every screen
    program's first test on a received field is `NOT = SPACES AND
    LOW-VALUES`. The blank members of the pool stay available to the drawn
    states - this is only the deterministic fill.
    """
    for value in values:
        text = str(value)
        if text.strip() and "\x00" not in text and "\xff" not in text:
            return value
    return values[0]


def reentry_states(program, pool, draws: int = 2, budget: int = 900) -> list:
    """Entry states shaped so a run completes cycle 1 and re-enters.

    Returns ``[(name, state), ...]``. Each state carries: a non-zero
    EIBCALEN sized to the commarea the program itself returns (so the run
    enters the with-commarea half on its very first task, saves its own
    state and re-enters); one attention-key byte the source compares
    against (constant across the pseudo-conversation, which is one recipe);
    and the evidenced input fields, either deterministically filled or
    drawn from the program's own literal pool.

    The re-enter flag itself is never named here: cycle 1 writes it into
    the commarea and the interpreter carries it, which is the whole point -
    the second cycle earns its state from the first.
    """
    areas = return_commareas(program)
    if not areas:
        return []
    calen = _commarea_width(program, areas) or 100
    fields = _field_values(program, pool,
                           [a for a in areas if a] + commarea_targets(program))
    filled = {name: _filled(values) for name, values in fields.items()}

    pairs = [(var, value) for var, values in sorted(aid_comparisons(program).items())
             for value in values] or [(None, None)]

    def shaped(tag: str, extra: dict, var, value) -> tuple:
        state = {"EIBCALEN": calen}
        state.update(extra)
        if var:
            state[var] = value
        return ("reenter:%s:%s" % ("%s=%r" % (var, value) if var else "no-aid",
                                   tag), state)

    # Three families, in the order they earn their keep, cut off at
    # `budget` states. *Filled* per key: every evidenced field holds its
    # most input-like value - one state per attention key, so every key's
    # dispatch runs against a completed screen. *Bases*: the filled state
    # rotated through each field's other non-blank candidates, wrapping -
    # 'Y' and 'N' are both confirmations and only one of them pays the
    # bill, and no generic rule can say which, so both get to be the
    # background. *Solo* per key: the first base with exactly one field
    # moved to one of its other candidates. Validation is written as a
    # first-match chain - each arm needs *this* field wrong while
    # everything before it passed - so varying one field at a time against
    # a passing background is the shape of the residual, and the budget
    # lesson in AGENTS.md applies: breadth per slot, never depth on one.
    out: list = []
    for var, value in pairs:
        out.append(shaped("filled", filled, var, value))
    nonblank = {name: ([v for v in values
                        if str(v).strip() and "\x00" not in str(v)
                        and "\xff" not in str(v)] or values)
                for name, values in fields.items()}
    rounds = max(max(0, draws),
                 min(6, max((len(v) for v in nonblank.values()), default=0)))
    # Bases beyond the first few attention keys pay almost nothing - most
    # keys share the invalid-key arm - while every base spent there is a
    # solo not spent on a field. Three keeps ENTER plus the first two
    # keys the program actually dispatches on.
    for index in range(rounds):
        for var, value in pairs[:3]:
            extra = {name: nonblank[name][index % len(nonblank[name])]
                     for name in sorted(fields)}
            if extra == filled:
                continue
            out.append(shaped("base%d" % index, extra, var, value))
    # The mode family: the entry dispatch names one field whose value
    # decides which half of the program a task runs - a state machine the
    # commarea carries. A solo against a single background can spoil a
    # field or set the mode, never both, and the validation-attribute arms
    # need exactly both: mode in the state that runs the edits, one field
    # failing them. So the solo family repeats under each mode value, two
    # variants per field - one blank, one non-blank-but-wrong - which is
    # the pairwise cross budgeted down to what the arms actually ask.
    mode = _mode_field(program, fields,
                       exclude={var for var, _ in pairs if var}
                       | {"EIBCALEN"})
    modes: list = []
    if mode:
        var, value = pairs[0]
        for m_index, candidate in enumerate(nonblank[mode]):
            if candidate == filled.get(mode):
                continue
            background = dict(filled)
            background[mode] = candidate
            modes.append(shaped("mode:%d" % m_index, background, var, value))
            for name in sorted(fields):
                if name == mode:
                    continue
                blank = next((v for v in fields[name]
                              if not str(v).strip()), None)
                wrong = next((v for v in fields[name]
                              if str(v).strip() and v != filled.get(name)),
                             None)
                for v_index, spoiled in enumerate((blank, wrong)):
                    if spoiled is None:
                        continue
                    extra = dict(background)
                    extra[name] = spoiled
                    modes.append(shaped("mode:%d:solo:%s:%d"
                                        % (m_index, name, v_index), extra,
                                        var, value))
    solos: list = []
    for var, value in pairs:
        for name in sorted(fields):
            for index, candidate in enumerate(fields[name]):
                if candidate == filled.get(name):
                    continue
                extra = dict(filled)
                extra[name] = candidate
                solos.append(shaped("solo:%s:%d" % (name, index), extra,
                                    var, value))
    out.extend(modes)
    out.extend(solos)
    return out[:max(len(pairs), budget)]
