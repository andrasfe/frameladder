"""Goal-directed backward chaining, with concrete local witnesses.

One missing direction in, one from-entry recipe out - or a *named* refusal.
The battery sprays recipes forward and keeps what lands; this module starts
from the direction and works backward, but unlike the ladder's symbolic
derivation every step here is settled by *running code*: the goal's
paragraph is executed in isolation until the direction demonstrably fires,
the values that made it fire are minimised to the essential few, and each
essential value is then either pinned at entry, staged on a stub, based on
a re-entry state, or - when some paragraph on the route overwrites it -
chased into that producer, which is solved the same way under an *output*
constraint: micro-execute it until it demonstrably writes what the goal
needs.

The distinction from the ladder (`ladder.plan_for_branch`) is where truth
lives. The ladder lifts obligations symbolically and finds out at
verification whether they compose; here nothing is ever believed about a
paragraph except what an interpreter run of that paragraph just showed,
so the composition inherits concreteness instead of hoping for it. The
distinction from the battery's phases is directionality: no phase starts
from the direction; this never starts from anywhere else.

Refusals are first-class results, not absences. Every goal ends in exactly
one of::

    witnessed             the composed recipe took the goal from entry
    local-unsolvable      the direction does not fire even in isolation
    no-producer           an essential value has no writer and no channel
    producer-unsolvable   no input makes the producing paragraph write it
    stub-terminal-unsolved  the stub route exists but no staged code lands
    depth-exhausted       the producer chain outran the depth cap
    budget-exhausted      the run budget died first
    validation-diverged   everything composed, and the from-entry replay
                          still missed the goal - reported, never absorbed

Everything staged obeys the evidence rule: values come from the goal
paragraph's own comparisons, the producer's own text, the data division's
88-levels, or a platform status vocabulary (`faults.py`) offered only to a
field the source itself put in that channel.
"""

from __future__ import annotations

import copy
import re

from .cobol import Program
from .conditions import condition_atoms
from .conformance_defaults import WORLDS, io_defaults
from .coverage import branches_of
from .interpreter import Interpreter
from .ledger import Ledger, _freeze
from .liveness import live_in

MAX_DEPTH = 6           # producer hops per goal
MAX_LOCAL_RUNS = 420    # interpreter runs per local solve
MAX_PRODUCER_RUNS = 220 # interpreter runs per output-constrained solve
MAX_VALUES = 8          # candidate values per variable
MAX_VARIABLES = 24      # variables swept per closure
MAX_SPOILS = 40         # mixed-construction variants per closure
STUB_SERIES = 6         # deliveries staged per operation, one per call
MAX_CANDIDATES = 3      # local witnesses composed and replayed per goal
MAX_FACTS = 4           # donated fact states consulted per closure
MAX_FACT_VARS = 20      # variables kept per donated fact projection

_KIND = {"PERFORM_UNTIL": "LOOP", "PERFORM_VARYING": "LOOP",
         "PERFORM_TIMES": "LOOP"}
_THRU = re.compile(r"\s+(?:THRU|THROUGH)\s+", re.I)
_CLASS = re.compile(r"([A-Z0-9][A-Z0-9-]*(?:\s+OF\s+[A-Z0-9-]+)?)"
                    r"\s+(?:IS\s+)?(?:NOT\s+)?NUMERIC\b", re.I)
_FIGURATIVE = {
    "LOW-VALUES": "\x00", "LOW-VALUE": "\x00", "SPACES": " ", "SPACE": " ",
    "ZEROS": "0", "ZEROES": "0", "ZERO": "0",
    "HIGH-VALUES": "\xff", "HIGH-VALUE": "\xff",
}


def _walk(stmt):
    yield stmt
    for child in stmt.get("children") or []:
        yield from _walk(child)


def _statements(para):
    for stmt in para.get("statements", []):
        yield from _walk(stmt)


def _direction_key(guard):
    return (guard.paragraph, guard.ordinal,
            _KIND.get(guard.kind, guard.kind), bool(guard.result))


class _Index:
    """Everything about one program this module reads more than once."""

    def __init__(self, program):
        self.program = program
        self.model = program.model
        self.names = [name.upper() for name in program.paragraph_names]
        self.paragraphs = {para["name"].upper(): para
                           for para in program.paragraphs}
        self._live: dict = {}
        self._width: dict = {}
        self._closure: dict = {}

    def width(self, name: str) -> int:
        key = str(name).upper()
        if key not in self._width:
            try:
                from .lift import _width
                self._width[key] = int(_width(self.model, key) or 0)
            except Exception:                                # noqa: BLE001
                self._width[key] = 0
        return self._width[key]

    def live_in(self, para: str) -> set:
        if para not in self._live:
            try:
                self._live[para] = {name.upper()
                                    for name in live_in(self.program, para)}
            except Exception:                                # noqa: BLE001
                self._live[para] = set()
        return self._live[para]

    def members(self, raw) -> tuple:
        """`PERFORM A THRU B` enters at A and runs the range."""
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

    def closure(self, root: str, depth: int = 6) -> tuple:
        """The paragraph and everything it PERFORMs, source order."""
        if root in self._closure:
            return self._closure[root]
        out, frontier = set(), {root}
        for _hop in range(depth):
            fresh: set = set()
            for para in frontier:
                for stmt in _statements(self.paragraphs.get(para, {})):
                    if stmt.get("type") != "PERFORM":
                        continue
                    target = (stmt.get("attributes") or {}).get("target")
                    for member in self.members(target):
                        if member not in out and member not in frontier:
                            fresh.add(member)
            out |= frontier
            frontier = fresh
            if not frontier:
                break
        members = tuple(name for name in self.names if name in out | frontier)
        self._closure[root] = members
        return members

    def sub_program(self, members):
        paragraphs = [copy.deepcopy(self.paragraphs[member])
                      for member in members if member in self.paragraphs]
        return Program(self.program.name, paragraphs, self.model,
                       getattr(self.program, "source_path", None))


# ---------------------------------------------------------------------------
# Candidate values - the program's own words
# ---------------------------------------------------------------------------

def _guard_evidence(index, members) -> dict:
    """``{var: [values]}`` from every comparison the closure makes.

    The paragraph's own text is the value inference: what it compares a
    field against is what it distinguishes, and both sides of every
    comparison it could ever take are in that set. 88-level names bring
    their VALUE lists and, through the complement, one value that is none
    of them.
    """
    values: dict = {}
    slices: dict = {}
    names = frozenset(index.model.condition_names or ())

    def note(name, value):
        name = str(name).upper()
        if value is None:
            return
        bucket = values.setdefault(name, [])
        if value not in bucket:
            bucket.append(value)

    def harvest(cond):
        try:
            groups = condition_atoms(str(cond or ""), names=names)
        except Exception:                                    # noqa: BLE001
            return
        for group in groups:
            for atom in group:
                for term, other in ((atom.lhs, atom.rhs),
                                    (atom.rhs, atom.lhs)):
                    if getattr(term, "kind", "") != "var":
                        continue
                    name = str(term.name).upper()
                    refmod = getattr(term, "refmod", None)
                    if refmod:
                        # A slice comparison constrains bytes at an offset,
                        # not the field: collected for composition below.
                        rhs = getattr(other, "value", None)
                        try:
                            start = int(str(refmod[0]))
                            length = int(str(refmod[1]))
                        except (TypeError, ValueError):
                            continue
                        if isinstance(rhs, str) and rhs.upper() != "NUMERIC":
                            slices.setdefault(name, []).append(
                                (start, length, rhs))
                        continue
                    entry = (index.model.condition_names or {}).get(name)
                    if entry:
                        parent = str(entry[0]).upper()
                        for raw in list(entry[1] or [])[:4]:
                            note(parent, _literal(raw))
                        continue
                    if not index.width(name):
                        continue
                    rhs = getattr(other, "value", None)
                    if rhs is not None and not isinstance(rhs, bool):
                        note(name, rhs)

    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            attributes = stmt.get("attributes") or {}
            for field in ("condition", "value"):
                if attributes.get(field):
                    harvest(attributes[field])
            # An EVALUATE arm's condition is just the compared value; the
            # variable it is compared against is the EVALUATE's subject.
            # Recombine them or the subject is never valued at all.
            if stmt.get("type") == "EVALUATE":
                subject = str(attributes.get("subject") or "").strip()
                subject = subject.split(" OF ")[0].split(" of ")[0].upper()
                if subject and index.model.knows(subject):
                    for arm in stmt.get("children") or []:
                        if arm.get("type") != "WHEN":
                            continue
                        raw = (arm.get("attributes") or {}).get("value")
                        value = _literal(raw)
                        if value is None:
                            continue
                        if isinstance(value, str) and value.upper() in (
                                "OTHER", "ANY", "TRUE", "FALSE"):
                            continue
                        note(subject, value)
    # One value outside every tested set, so negative directions of a
    # field's only comparison are reachable at all.
    from .heuristics import complement_value
    for name in list(values):
        extra = complement_value(name, index.model.pic_of(name), values[name])
        if extra is not None and extra not in values[name]:
            values[name].append(extra)
    # Class conditions constrain the *shape* of the value, not its
    # identity: `IS NUMERIC` is passed by digits and failed by letters,
    # and no comparison literal or complement says so. The digits value
    # goes last on purpose - the all-valid joint base is built from each
    # variable's final candidate, and a field that must survive both a
    # not-blank gate and a numeric gate needs the digits there.
    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            attributes = stmt.get("attributes") or {}
            for field in ("condition", "value"):
                text = str(attributes.get(field) or "")
                for match in _CLASS.finditer(text):
                    name = match.group(1).strip().upper()
                    head = name.split(" OF ")[0].strip()
                    if not index.model.knows(head):
                        continue
                    width = index.width(head) or 4
                    bucket = values.setdefault(name, [])
                    for shaped in ("A" * width, "9" * width):
                        if shaped in bucket:
                            bucket.remove(shaped)
                        bucket.append(shaped)
    # Slice comparisons compose into whole-field candidates: a digits
    # buffer with each compared literal placed at its own offset. This is
    # what passes a format edit - `X(1:1) = '-'` and `X(2:8) NUMERIC`
    # jointly ask for '-00000000' - and no whole-field literal can. The
    # composed value goes last: it is the pass shape the all-valid joint
    # picks up.
    for name, constraints in slices.items():
        head = name.split(" OF ")[0].strip()
        width = index.width(head) or max(start + length - 1
                                         for start, length, _v in constraints)
        by_start: dict = {}
        for start, length, literal in constraints:
            by_start.setdefault((start, length), [])
            if literal not in by_start[(start, length)]:
                by_start[(start, length)].append(literal)
        variants = []
        for pick in range(2):
            buffer = ["0"] * width
            for (start, length), literals in sorted(by_start.items()):
                literal = literals[min(pick, len(literals) - 1)]
                for position in range(length):
                    if 0 <= start - 1 + position < width:
                        char = literal[position] if position < len(literal)                             else " "
                        buffer[start - 1 + position] = char
            variants.append("".join(buffer))
        bucket = values.setdefault(name, [])
        for variant in variants:
            if variant in bucket:
                bucket.remove(variant)
            bucket.append(variant)
    return {name: vals[-MAX_VALUES:] for name, vals in values.items()}


def _literal(raw):
    if raw is None or isinstance(raw, bool):
        return None
    text = str(raw).strip()
    if text.upper() in _FIGURATIVE:
        return _FIGURATIVE[text.upper()]
    # The platform's own reader resolves what a bare strip cannot:
    # DFHRESP(NORMAL) is the integer 0, not a fifteen-byte string.
    try:
        from .ir import parse_term
        term = parse_term(text)
        if term.kind == "const" and not isinstance(term.value, bool):
            return term.value
    except Exception:                                        # noqa: BLE001
        pass
    return text.strip("'\"")


def _pool_from_literals(index, prov) -> dict:
    """The program-wide literal pool, for variables the closure never
    compares but still reads."""
    out: dict = {}
    for name, literals in (getattr(prov, "literals", None) or {}).items():
        vals = [v for v in literals if v is not None
                and not isinstance(v, bool)]
        if vals:
            out[str(name).upper()] = sorted(vals, key=repr)[:MAX_VALUES]
    return out


# ---------------------------------------------------------------------------
# Local solve: make the direction fire in isolation
# ---------------------------------------------------------------------------

def _first_match_chains(index, members) -> list:
    """First-match chains in the closure: EVALUATE arms in source order.

    Each entry is ``[(parent_var, spoil_values)]`` in arm order - the raw
    material of the mixed construction: all fields valid, one spoiled.
    """
    names = frozenset(index.model.condition_names or ())
    chains = []
    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            if stmt.get("type") != "EVALUATE":
                continue
            arms = [c for c in (stmt.get("children") or [])
                    if c.get("type") == "WHEN"]
            if len(arms) < 3:
                continue
            rows = []
            for arm in arms:
                cond = (arm.get("attributes") or {}).get("value", "") or ""
                if cond.strip().upper() in ("OTHER", "ANY"):
                    continue
                try:
                    groups = condition_atoms(cond, names=names)
                except Exception:                            # noqa: BLE001
                    continue
                for group in groups:
                    for atom in group:
                        for term in (atom.lhs, atom.rhs):
                            if getattr(term, "kind", "") != "var":
                                continue
                            entry = (index.model.condition_names or {}).get(
                                str(term.name).upper())
                            if not entry:
                                continue
                            parent = str(entry[0]).upper()
                            spoils = [_literal(v) for v in (entry[1] or [])]
                            spoils = [v for v in spoils if v is not None]
                            if spoils:
                                rows.append((parent, spoils))
            if rows:
                chains.append(rows)
    return chains


def _mixed_states(index, members) -> list:
    """All-valid-plus-one-spoiled states for every first-match chain.

    The valid value per field is one that satisfies none of the chain's
    arms over that field - the complement of every spoil. Reaching arm N
    of a first-match chain needs exactly this shape, and neither
    one-at-a-time sweeps nor rotating joint bases can produce it.
    """
    from .heuristics import complement_value
    out = []
    for chain in _first_match_chains(index, members):
        tested: dict = {}
        for parent, spoils in chain:
            tested.setdefault(parent, []).extend(spoils)
        valid: dict = {}
        for parent, spoils in tested.items():
            value = complement_value(parent, index.model.pic_of(parent),
                                     spoils)
            if value is None:
                width = index.width(parent) or 1
                for candidate in (" " * width, "0" * width, "~" * width):
                    if candidate not in spoils:
                        value = candidate
                        break
            if value is not None:
                valid[parent] = value
        if not valid:
            continue
        out.append(dict(valid))                       # the all-valid state
        for parent, spoils in chain[:MAX_SPOILS]:
            for spoil in spoils[:2]:
                state = dict(valid)
                state[parent] = spoil
                out.append(state)
    return out


def _stub_channels(index, prov, names, members=()) -> dict:
    """``{var: (op_key, [values])}`` for guard variables an operation
    rebuilds before the guard can see an entry value.

    A field the program rebuilds from an external operation on every call
    cannot be pinned at entry - the write lands between entry and the
    guard, whatever the entry said. The only legal handle is the
    operation itself, staged as a repeated stub series so every call in
    the run returns the same code (a terminal only fires after a matched
    entry, so with no entries it never fires at all). Values: what the closure's own guards compare
    the field against, then the platform family when the source put the
    field in a status channel (`faults.channel_of` - a SELECT's FILE
    STATUS, SQLCODE, a RESP operand; never a naming guess).
    """
    from .faults import _FAMILIES, channel_of
    out: dict = {}
    members = set(members)
    for name in names:
        head = str(name).upper().split(" OF ")[0].strip()
        writers = [w for w in _writers(prov, head)
                   if w.kind == "STUB" and w.op_key]
        if not writers:
            continue
        # The operation whose write actually reaches the closure's guard
        # is the one performed *in* the closure; program-wide, the first
        # writer of a shared RESP field is whatever operation happens to
        # come first in the source.
        local = [w for w in writers if w.para in members]
        chosen = (local or writers)[0]
        family = None
        try:
            family = channel_of(head, index.model, chosen.op_key)
        except Exception:                                    # noqa: BLE001
            family = None
        called = chosen.op_key.upper().startswith("CALL:")
        if not family and not called:
            # A map or record fill: the entry state still owns the bytes
            # in the worlds these runs use. Terminal-staging it would take
            # the field out of the entry sweep for nothing.
            continue
        extra = list(_FAMILIES.get(family, ()))[:4] if family else []
        out[str(name).upper()] = (chosen.op_key, extra)
    return out


def _mirror_pairs(index, prov, members) -> list:
    """``[(stub_head, op_key, other_name)]`` from var-vs-var comparisons.

    A guard like ``record-key = screen-key`` where one side arrives from
    an external operation is a *consistency* constraint: no literal in
    the program says what either side holds, only that they must agree.
    The staging that satisfies it is the mirror - deliver into the
    stub-written side whatever value the attempt already chose for the
    other side. Measured on iteration 1, every such gate refused; the
    program's own text names no value because the value is "whatever the
    user typed".
    """
    names = frozenset(index.model.condition_names or ())
    out, marks = [], set()
    for member in members:
        for stmt in _statements(index.paragraphs.get(member, {})):
            attributes = stmt.get("attributes") or {}
            for field in ("condition", "value"):
                cond = attributes.get(field)
                if not cond:
                    continue
                try:
                    groups = condition_atoms(str(cond), names=names)
                except Exception:                            # noqa: BLE001
                    continue
                for group in groups:
                    for atom in group:
                        lhs, rhs = atom.lhs, atom.rhs
                        if getattr(lhs, "kind", "") != "var"                                 or getattr(rhs, "kind", "") != "var":
                            continue
                        for one, other in ((lhs, rhs), (rhs, lhs)):
                            head = str(one.name).upper().split(" OF ")[0]
                            writers = [w for w in _writers(prov, head)
                                       if w.kind == "STUB" and w.op_key]
                            if not writers:
                                continue
                            other_name = str(other.name).upper()
                            if not index.model.knows(
                                    other_name.split(" OF ")[0]):
                                continue
                            local = [w for w in writers
                                     if w.para in members]
                            op = (local or writers)[0].op_key
                            mark = (head, op, other_name)
                            if mark not in marks:
                                marks.add(mark)
                                out.append(mark)
    return out


def _from_state(state, name):
    """A value for ``name`` out of an attempt state, qualified or not."""
    if name in state:
        return state[name]
    head = name.split(" OF ")[0]
    if head in state:
        return state[head]
    for key, value in state.items():
        if str(key).split(" OF ")[0] == head:
            return value
    return None


def _attempts_for(index, prov, members, facts=()) -> list:
    """The sweep, cheapest shape first: the bare state, donated fact
    states from earlier from-entry replays, guard-evidence values one at
    a time, staged stub codes one at a time, the mixed all-valid-plus-
    one-spoiled construction, joint bases rotating through the candidate
    lists, and the all-valid joint base with one variable (or one stub
    code) varied. Every attempt is ``(state, stub_plan)``; var-vs-var
    consistency gates get their stub side mirrored from whatever the
    attempt chose for the entry side.
    """
    evidence = _guard_evidence(index, members)
    pool = _pool_from_literals(index, prov)
    variables = sorted(set(evidence) | (
        {v for m in members for v in index.live_in(m) if v in pool}
    ))[:MAX_VARIABLES]

    def candidates(name):
        merged = list(evidence.get(name, []))
        for value in pool.get(name, []):
            if value not in merged:
                merged.append(value)
        return merged[:MAX_VALUES]

    channels = _stub_channels(index, prov, variables, members)

    def stub_values(name):
        op, extra = channels[name]
        merged = list(candidates(name))
        for value in extra:
            if value not in merged:
                merged.append(value)
        return merged[:MAX_VALUES + 2]

    mirrors = _mirror_pairs(index, prov, members)

    raw = [({}, {})]                       # (state, {op: {field: value}})
    for fact in list(facts)[:MAX_FACTS]:
        raw.append((dict(fact), {}))
    for name in variables:
        if name in channels:
            op, _extra = channels[name]
            head = name.split(" OF ")[0]
            for value in stub_values(name):
                raw.append(({}, {op: {head: value}}))
            continue
        for value in candidates(name):
            raw.append(({name: value}, {}))
    raw.extend((state, {}) for state in _mixed_states(index, members))
    # Joint bases. The all-complements joint comes first and serves as the
    # varied-sweep base: a variable's complement (or digits, under a class
    # condition) is the one value outside everything the closure tests it
    # against, so the joint of last candidates is the state that passes
    # every not-blank / not-numeric / not-error gate at once - the
    # closure-wide all-valid screen. Stub-written variables join through
    # their operation's terminal, first value the guards compare against.
    # Varying one variable over the joint is the all-valid-plus-one-
    # spoiled construction generalised past EVALUATE chains to any gate
    # sequence. Measured before this ordering, the varied sweep sat on a
    # base that failed the first gate and every variation died there.
    joint_terms: dict = {}
    for name, (op, _extra) in channels.items():
        options = stub_values(name)
        if options:
            joint_terms.setdefault(op, {})[name.split(" OF ")[0]] = options[0]
    joints = []
    for pick in (-1, 0, 1):
        joint = {}
        for name in variables:
            if name in channels:
                continue
            options = candidates(name)
            if not options:
                continue
            if pick == -1:
                # The pass-shaped value is the *evidence* tail - the
                # complement of the tested set, or the digits a class
                # condition demands - not the tail of the merged list,
                # where a program-wide literal can shadow it.
                options = evidence.get(name) or options
            joint[name] = options[pick if -len(options) <= pick
                                  < len(options) else 0]
        if joint and joint not in joints:
            joints.append(joint)
    for joint in joints:
        raw.append((joint, {}))
        if joint_terms:
            raw.append((joint, {k: dict(v) for k, v in joint_terms.items()}))
    base = joints[0] if joints else {}
    for fact in list(facts)[:MAX_FACTS]:
        merged = dict(base)
        merged.update(fact)
        raw.append((merged, {k: dict(v) for k, v in joint_terms.items()}))
    for name in variables:
        if name in channels:
            op, _extra = channels[name]
            head = name.split(" OF ")[0]
            for value in stub_values(name):
                varied_terms = {k: dict(v) for k, v in joint_terms.items()}
                varied_terms.setdefault(op, {})[head] = value
                raw.append((dict(base), varied_terms))
            continue
        for value in candidates(name):
            if base.get(name) != value:
                varied = dict(base)
                varied[name] = value
                raw.append((varied, {}))
                if joint_terms:
                    raw.append((varied,
                                {k: dict(v) for k, v in joint_terms.items()}))

    def materialise(fields):
        return {op: [{"set": dict(vals)} for _n in range(STUB_SERIES)]
                for op, vals in fields.items()}

    attempts = []
    for state, fields in raw:
        # The mirror: any var-vs-var consistency gate whose entry side
        # this attempt values gets the stub side delivered to match.
        mirrored = {k: dict(v) for k, v in fields.items()}
        hit = False
        for stub_head, op, other_name in mirrors:
            value = _from_state(state, other_name)
            if value is None:
                continue
            mirrored.setdefault(op, {})[stub_head] = value
            hit = True
        attempts.append((state, materialise(fields)))
        if hit and mirrored != fields:
            attempts.append((state, materialise(mirrored)))
    return attempts


def local_solve(index, prov, goal, budget, sweep_cache, facts=()) -> tuple:
    """``(assignment, runs)`` firing the goal in the closure, or
    ``(None, runs)``.

    The sweep is *shared per closure*: every state run during any goal's
    sweep records the full set of direction keys it fired, so the second
    goal in the same paragraph is usually answered from the cache without
    spending a single run. Measured before the cache, re-sweeping the same
    dispatcher paragraph for each of its arms was where the whole budget
    went.
    """
    paragraph = goal[0]
    if paragraph not in index.paragraphs:
        return [], 0
    members = index.closure(paragraph)
    sub = index.sub_program(members)
    runs = [0]

    def observe(state, staged):
        """Run one attempt, record every direction it fires."""
        if runs[0] >= MAX_LOCAL_RUNS or budget.left() <= 0:
            return None
        runs[0] += 1
        budget.spend()
        try:
            interp = Interpreter(sub, dict(state), stubs=staged or None,
                                 defaults=io_defaults(index.program,
                                                      "populated"))
            trace = interp.run(members[0])
        except Exception:                                    # noqa: BLE001
            return frozenset()
        return frozenset(_direction_key(g) for g in trace.guards)

    cached = sweep_cache.get(paragraph)
    if cached is None:
        cached = {"states": [], "done": False}
        sweep_cache[paragraph] = cached

    def finish():
        """Every cached firing state, richest first.

        Fall-through in a sub-program makes some local firings spurious -
        a first-match arm's False direction fires under a garbage subject
        the real route would never deliver. Which local witness survives
        the route from entry cannot be judged here, so the candidates go
        back richest-first (the state that set the most variables carried
        the most deliberate construction) and the caller lets the
        from-entry replay decide.
        """
        firing = [(state, staged, fired) for state, staged, fired
                  in cached["states"] if goal in fired]
        # Deepest-first: the state whose run fired the most *distinct*
        # directions got past the most gates - an error loop fires the
        # same few guards over and over, however big its state was. The
        # first cut of this used richest-state-first and reliably chose
        # a donated failure state whose screen bytes poisoned the recipe.
        firing.sort(key=lambda row: (-len(row[2]),
                                     -(len(row[0]) + len(row[1]))))
        out = []
        for state, staged, fired_set in firing[:MAX_CANDIDATES]:
            def fires(trimmed, _staged=staged):
                fired = observe(trimmed, _staged)
                if fired is None:
                    return None
                return goal in fired
            out.append((_shrink(fires, state), staged, dict(state),
                        fired_set))
        return out

    if not cached["done"]:
        attempts = _attempts_for(index, prov, members, facts=facts)
        position = len(cached["states"])
        for state, staged in attempts[position:]:
            fired = observe(state, staged)
            if fired is None:
                break
            cached["states"].append((dict(state), staged, fired))
        else:
            cached["done"] = True
    return finish(), runs[0]


def _shrink(fires, assignment) -> dict:
    """Greedy ddmin: drop every pair the firing does not need."""
    essential = dict(assignment)
    for name in sorted(assignment):
        trimmed = {k: v for k, v in essential.items() if k != name}
        verdict = fires(trimmed)
        if verdict is None:
            break
        if verdict:
            essential = trimmed
    return essential


# ---------------------------------------------------------------------------
# Output-constrained solve: make a producer write what the goal needs
# ---------------------------------------------------------------------------

def _satisfied(state, required) -> bool:
    for name, value in required.items():
        try:
            current = state.get(str(name).upper())
        except Exception:                                    # noqa: BLE001
            return False
        if current is None:
            return False
        if str(current).rstrip() != str(value).rstrip():
            return False
    return True


def producer_solve(index, prov, producer, required, budget, memo) -> tuple:
    """``(assignment, runs)`` making ``producer`` write every pair in
    ``required``, judged on the post-state - or ``(None, runs)``.

    The conjunction case is first-class: ``required`` is a dict and every
    pair must hold at once, because a dispatcher paragraph typically needs
    several flags together before it routes anywhere interesting.
    """
    key = (producer, tuple(sorted((k, repr(v)) for k, v in required.items())))
    if key in memo:
        return memo[key], 0
    members = index.closure(producer)
    if producer not in index.paragraphs:
        memo[key] = None
        return None, 0
    sub = index.sub_program(members)
    runs = [0]

    def produces(state):
        if runs[0] >= min(budget.left(), MAX_PRODUCER_RUNS):
            return None
        runs[0] += 1
        budget.spend()
        try:
            interp = Interpreter(sub, dict(state),
                                 defaults=io_defaults(index.program,
                                                      "populated"))
            interp.run(members[0])
        except Exception:                                    # noqa: BLE001
            return False
        return _satisfied(interp.state, required)

    for state, _terminals in _attempts_for(index, prov, members):
        verdict = produces(state)
        if verdict is None:
            break
        if verdict:
            answer = _shrink(produces, state)
            memo[key] = answer
            return answer, runs[0]
    memo[key] = None
    return None, runs[0]


# ---------------------------------------------------------------------------
# Classification: where each essential value can come from
# ---------------------------------------------------------------------------

def _stub_writers(prov, name) -> list:
    return [w for w in _writers(prov, name) if w.kind == "STUB" and w.op_key]


def _writers(prov, name) -> list:
    try:
        return list(prov.writes_to(str(name).upper()))
    except Exception:                                        # noqa: BLE001
        return []


def _program_writers(prov, name, exclude) -> list:
    """Writers that overwrite ``name`` outside the goal's own closure."""
    return [w for w in _writers(prov, name)
            if w.kind in ("MOVE", "SET") and w.para not in exclude]


def classify(index, prov, name, value, goal_members) -> tuple:
    """``(kind, detail)`` for one essential (variable, value) pair.

    ``entry``     nothing on the route overwrites it: pin it.
    ``stub``      a stub writes it: stage the value on that operation.
    ``produced``  a paragraph writes it before the goal: recurse there.

    A variable both stub- and MOVE-written classifies as produced first -
    the MOVE is the program's own way of putting a value there, and a
    producer solve stays within entry-state vocabulary; the stub is the
    fallback when no input drives the MOVE.
    """
    writers = _program_writers(prov, name, exclude=set(goal_members))
    if not writers:
        stubs = _stub_writers(prov, name)
        if stubs:
            return "stub", stubs[0]
        return "entry", None
    producers = sorted({w.para for w in writers})
    return "produced", producers


# ---------------------------------------------------------------------------
# The chaining solver
# ---------------------------------------------------------------------------

class _Budget:
    def __init__(self, total):
        self.total = total
        self.spent = 0

    def spend(self, n=1):
        self.spent += n

    def left(self):
        return max(0, self.total - self.spent)


def _stage_stub(stub_fields, writer, name, value):
    """One operation is one delivery: a RECEIVE fills the whole screen in
    one call, so every staged field of an op belongs to *every* entry of
    its series, not to an entry of its own. Fields accumulate here and
    materialise once, together.

    First write wins. The frontier is walked goal-level first, producer
    recursion after, and a producer's own sweep state is incidental - it
    said what fires the *producer*, not what the goal's screen holds.
    Letting depth 2 overwrite depth 1 measurably replaced a valid screen
    byte with a producer's LOW-VALUE and failed the very edit the goal
    state had passed."""
    stub_fields.setdefault(writer.op_key, {}).setdefault(
        str(name).upper(), value)


def _materialise(stub_fields) -> dict:
    return {op: [{"set": dict(fields)} for _n in range(STUB_SERIES)]
            for op, fields in stub_fields.items()}


def solve(index, prov, goal, budget, memo, reentry_bases,
          sweep_cache, facts=()) -> dict:
    """One goal in, ``{"recipe": ...}`` or ``{"refusal": ...}`` out.

    The recipe is not yet validated - validation is the caller's replay,
    because crediting must go through the same deduplicating run every
    mechanism uses.
    """
    candidates, _runs = local_solve(index, prov, goal, budget, sweep_cache,
                                    facts=facts)
    if not candidates:
        if budget.left() <= 0:
            return {"refusal": "budget-exhausted"}
        return {"refusal": "local-unsolvable"}

    goal_members = index.closure(goal[0])
    bases = [({}, world) for world in WORLDS]
    bases += [(dict(state), "populated") for _name, state in reentry_bases]
    recipes, refusal = [], None
    local_fired: set = set()
    for assignment, staged_stubs, full_state, fired_set in candidates:
        local_fired |= set(fired_set)
        entry_pins: dict = {}
        stub_fields: dict = {}
        for key, entries in (staged_stubs or {}).items():
            for entry in entries:
                stub_fields.setdefault(key, {}).update(entry.get("set") or {})
        frontier = list((full_state or assignment).items())
        essential = {str(name).upper() for name in assignment}
        depth = 0
        seen: set = set()
        failed = None
        while frontier and failed is None:
            if depth > MAX_DEPTH:
                failed = "depth-exhausted"
                break
            if budget.left() <= 0:
                failed = "budget-exhausted"
                break
            depth += 1
            next_frontier: list = []
            # Group the produced pairs by producer so a paragraph that
            # must write three flags is solved once for the conjunction,
            # not three times for fragments that undo each other.
            produced: dict = {}
            for name, value in frontier:
                mark = (str(name).upper(), repr(value))
                if mark in seen:
                    continue
                seen.add(mark)
                kind, detail = classify(index, prov, name, value,
                                        goal_members)
                if kind == "entry":
                    # First write wins here too, same depth argument.
                    entry_pins.setdefault(str(name).upper(), value)
                elif kind == "stub":
                    _stage_stub(stub_fields, detail, name, value)
                else:
                    # Program-written, so the producer chase may apply -
                    # but when an operation also delivers the field (a
                    # screen fill, a record read), stage that delivery
                    # too: on the route that matters the producer
                    # paragraph may never run, and the operation is what
                    # actually hands the value over. Measured without
                    # this, the replay diverged at the unstaged field's
                    # own not-blank gate every time.
                    stub_writers = _stub_writers(prov, name)
                    if stub_writers:
                        _stage_stub(stub_fields, stub_writers[0], name,
                                    value)
                    if str(name).upper() in essential:
                        producer = detail[0]
                        produced.setdefault(producer, {})[
                            str(name).upper()] = value
            if failed is not None:
                break
            for producer, required in produced.items():
                answer, _n = producer_solve(index, prov, producer, required,
                                            budget, memo)
                if answer is None:
                    if budget.left() <= 0:
                        failed = "budget-exhausted"
                        break
                    # The producer would not write it from any swept
                    # input; a stub that writes the field directly is the
                    # remaining legal source.
                    for name, value in required.items():
                        stub_writers = _stub_writers(prov, name)
                        if stub_writers:
                            _stage_stub(stub_fields, stub_writers[0], name,
                                        value)
                        else:
                            # Last resort: pin at entry and let the replay
                            # judge. The classification said a paragraph
                            # overwrites it, but on the route that matters
                            # the read may come first - and the exact
                            # value the producer refused to write is often
                            # over-specific anyway (a 'non-blank message'
                            # obligation surfaces here as one arbitrary
                            # byte string). A wrong pin costs one replay;
                            # a refusal costs the direction.
                            entry_pins.setdefault(str(name).upper(), value)
                    continue
                next_frontier.extend(answer.items())
            frontier = next_frontier
        if failed is not None:
            refusal = refusal or failed
            continue
        recipes.append({"pins": entry_pins,
                        "stubs": _materialise(stub_fields), "bases": bases})
    if not recipes:
        return {"refusal": refusal or "producer-unsolvable"}
    return {"recipes": recipes, "local_fired": local_fired}


# ---------------------------------------------------------------------------
# The driver: solve every goal, validate from entry, account for everything
# ---------------------------------------------------------------------------
def _project(index, state_view, paragraph, para_vars_cache) -> dict:
    """The replay's state, projected onto one paragraph's variables.

    ``state_view`` is a live interpreter FieldMap; only the variables the
    paragraph's own guards and live-in set name are read, so a fact stays
    a paragraph-sized statement rather than a core dump.
    """
    names = para_vars_cache.get(paragraph)
    if names is None:
        members = index.closure(paragraph)
        names = set()
        for member in members:
            names |= index.live_in(member)
        try:
            from .ladder import analyse            # noqa: F401  (no re-run)
        except Exception:                          # noqa: BLE001
            pass
        names = sorted(name for name in names
                       if index.model.knows(str(name).split(" OF ")[0]))
        names = names[:MAX_FACT_VARS]
        para_vars_cache[paragraph] = names
    out = {}
    for name in names:
        try:
            value = state_view.get(str(name).split(" OF ")[0])
        except Exception:                          # noqa: BLE001
            continue
        if value is not None:
            out[name] = value
    return out


def _flip(key):
    return (key[0], key[1], key[2], not key[3])


def _first_divergence(trace, local_fired) -> tuple:
    """The first guard the replay took the other way from the local
    witness: ``(subgoal_key, observed_values)`` or ``(None, None)``.

    The local witness fired the goal after its closure took a specific
    set of directions; the from-entry run diverged where it took a
    direction whose *flip* the local run took and whose own key the
    local run never did. The flip is exactly the direction the route
    needs - a concrete, smaller goal - and the guard's observed operand
    values say what the state held at the moment it went wrong.
    """
    for guard in trace.guards:
        key = _direction_key(guard)
        if _flip(key) in local_fired and key not in local_fired:
            return _flip(key), dict(guard.values or {})
    return None, None


def _load_facts(path):
    import json as _json
    import os as _os
    if not path or not _os.path.exists(path):
        return {}
    try:
        raw = _json.load(open(path))
        return {para: [dict(fact) for fact in facts_list]
                for para, facts_list in raw.items()}
    except Exception:                              # noqa: BLE001
        return {}


def _save_facts(path, facts):
    import json as _json
    if not path:
        return
    try:
        with open(path, "w") as handle:
            _json.dump(facts, handle, indent=1, default=str)
    except Exception:                              # noqa: BLE001
        pass


def run_chain(program, goals=None, budget=8000, baseline=None,
              epochs=3, facts_path=None) -> dict:
    """Chain every goal, in epochs that learn from their own replays.

    One epoch solves every pending goal (default: every direction the
    baseline lacks). Each from-entry replay - success or failure -
    donates facts: the replay's state projected onto the paragraphs it
    entered, keyed per paragraph, consulted by the next epoch's local
    sweeps before anything is invented. A composed recipe whose replay
    diverges contributes its first divergent guard as a *subgoal* for
    the next epoch - the route's actual gap, with the operand values the
    replay observed. The loop stops early when an epoch adds no witness,
    no fact and no subgoal.

    Crediting is generous - a run is a witness for every direction its
    trace took - deduplicated by full recipe, and only ever through a
    fresh from-entry interpreter; nothing enters the ledger on a solver's
    say-so. ``report["ledger"]`` holds every credited witness.
    """
    from .ladder import analyse
    index = _Index(program)
    _graph, prov = analyse(program)
    entry = index.names[0]
    ledger = Ledger()
    seen_runs: set = set()
    the_budget = _Budget(budget)
    facts = _load_facts(facts_path)
    facts_seen = {para: {repr(sorted(fact.items())) for fact in facts_list}
                  for para, facts_list in facts.items()}
    para_vars_cache: dict = {}
    fact_watch: set = set()        # paragraphs whose facts are worth keeping
    new_fact_count = [0]

    def donate(fact_paragraphs, interp):
        for paragraph in fact_paragraphs:
            fact = _project(index, interp.state, paragraph, para_vars_cache)
            if not fact:
                continue
            mark = repr(sorted(fact.items()))
            seen = facts_seen.setdefault(paragraph, set())
            if mark in seen:
                continue
            seen.add(mark)
            facts.setdefault(paragraph, []).append(fact)
            new_fact_count[0] += 1

    def run(state, world, stub_plan, terminals, source):
        key = (_freeze(state or {}), world, _freeze(stub_plan or {}),
               _freeze(terminals or {}))
        if key in seen_runs:
            return None
        seen_runs.add(key)
        the_budget.spend()
        try:
            interp = Interpreter(program, dict(state or {}), stubs=stub_plan,
                                 terminals=terminals,
                                 defaults=io_defaults(program, world))
            trace = interp.run(entry)
        except Exception:                          # noqa: BLE001
            return None
        ledger.credit(trace, state or {}, world, stub_plan, terminals, source)
        donate(set(trace.entered) & fact_watch, interp)
        return trace

    have = set(baseline or ())
    if goals is None:
        goals = []
        for branch in branches_of(program):
            for direction in (True, False):
                key = (branch.paragraph, branch.ordinal, branch.kind,
                       direction)
                if key not in have:
                    goals.append(key)
    original = list(goals)

    try:
        from .reentry import reentry_states
        pool = _pool_from_literals(index, prov)
        # One base per distinct shape (the name encodes the AID key and
        # fill mode); the first carries the attention key the program
        # compares against first.
        reentry_bases, seen_names = [], set()
        for name, state in reentry_states(program, pool):
            mark = name.split(":filled")[0].split(":drawn")[0]
            if mark in seen_names:
                continue
            seen_names.add(mark)
            reentry_bases.append((name, state))
            if len(reentry_bases) >= 4:
                break
    except Exception:                              # noqa: BLE001
        reentry_bases = []

    memo: dict = {}
    last_outcome: dict = {}
    pending = list(original)
    fact_watch.update(goal[0] for goal in pending)
    per_epoch = []
    for epoch in range(max(1, epochs)):
        sweep_cache: dict = {}    # facts changed; sweeps must re-run
        epoch_subgoals: list = []
        witnessed_before = sum(1 for g in original if g in ledger.witnesses)
        credited_before = len(ledger.witnesses)
        facts_before = new_fact_count[0]
        runs_before = the_budget.spent
        for goal in pending:
            if the_budget.left() <= 0:
                last_outcome.setdefault(goal, "budget-exhausted")
                continue
            if goal in ledger.witnesses:
                last_outcome[goal] = "witnessed"
                continue
            answer = solve(index, prov, goal, the_budget, memo,
                           reentry_bases, sweep_cache,
                           facts=facts.get(goal[0], ()))
            if "refusal" in answer:
                last_outcome[goal] = answer["refusal"]
                continue
            landed = False
            any_stubs = False
            diverged_trace = None
            for recipe in answer["recipes"]:
                any_stubs = any_stubs or bool(recipe["stubs"])
                for base_state, world in recipe["bases"]:
                    state = dict(base_state)
                    state.update(recipe["pins"])
                    trace = run(state, world, recipe["stubs"] or None, None,
                                "chain:%s:%s:%s" % (goal[0], goal[1],
                                                    goal[3]))
                    if trace is not None:
                        diverged_trace = trace
                    if goal in ledger.witnesses:
                        landed = True
                        break
                if landed:
                    break
            if landed:
                last_outcome[goal] = "witnessed"
                continue
            last_outcome[goal] = "stub-terminal-unsolved" if any_stubs \
                else "validation-diverged"
            if diverged_trace is not None:
                subgoal, observed = _first_divergence(
                    diverged_trace, answer.get("local_fired", set()))
                if subgoal is not None \
                        and subgoal not in ledger.witnesses \
                        and subgoal not in pending \
                        and subgoal not in epoch_subgoals:
                    epoch_subgoals.append(subgoal)
                    fact_watch.add(subgoal[0])
                    if observed:
                        donatable = {name: value for name, value
                                     in observed.items()
                                     if index.model.knows(
                                         str(name).split(" OF ")[0])}
                        if donatable:
                            mark = repr(sorted(donatable.items()))
                            seen = facts_seen.setdefault(subgoal[0], set())
                            if mark not in seen:
                                seen.add(mark)
                                facts.setdefault(subgoal[0], []).append(
                                    donatable)
                                new_fact_count[0] += 1
        witnessed_after = sum(1 for g in original if g in ledger.witnesses)
        per_epoch.append({
            "epoch": epoch + 1,
            "witnessed_original": witnessed_after,
            "witnessed_delta": witnessed_after - witnessed_before,
            "credited_delta": len(ledger.witnesses) - credited_before,
            "new_facts": new_fact_count[0] - facts_before,
            "new_subgoals": len(epoch_subgoals),
            "runs": the_budget.spent - runs_before,
        })
        still = [g for g in pending if g not in ledger.witnesses]
        pending = still + epoch_subgoals
        if per_epoch[-1]["witnessed_delta"] == 0 \
                and per_epoch[-1]["new_facts"] == 0 \
                and not epoch_subgoals:
            break
        if the_budget.left() <= 0:
            break
    _save_facts(facts_path, facts)

    refusals: dict = {}
    for goal in original:
        outcome = last_outcome.get(goal, "budget-exhausted")
        if outcome == "witnessed" or goal in ledger.witnesses:
            continue
        refusals[outcome] = refusals.get(outcome, 0) + 1
    witnessed = sum(1 for g in original if g in ledger.witnesses)
    report = {"goals": len(original), "witnessed": witnessed,
              "credited_directions": len(ledger.witnesses),
              "runs": the_budget.spent, "budget": budget,
              "epochs": per_epoch,
              "refusals": refusals, "ledger": ledger}
    return report
