"""Solve for the *next* decision, from the state the program actually had.

The ladder derives a plan for a target and runs it from the entry point. On a
short chain that works. On a long one it mostly does not, and the reason is
structural rather than a missing case: the obligation is at the target, the
plan is placed at entry, and every statement in between may overwrite the
field the obligation names. COACTUPC destroys its whole input area in the
first twenty lines - `INITIALIZE CARDDEMO-COMMAREA` on one arm and
`MOVE DFHCOMMAREA (1:200) TO CARDDEMO-COMMAREA` on the other - so a plan that
pins `CDEMO-FROM-TRANID` is a plan about a field that no longer holds what it
was given by the time anything reads it.

This module takes the other route. It never asks what the entry state must be
for a target three hundred statements away; it asks what the entry state must
be to send *the next decision* the other way, and it asks it of a run that has
already got there. The answer is read off :mod:`frameladder.origins`, which
tracks which entry bytes each stored value is still a copy of, so lifting
through the commarea move is arithmetic on a byte range instead of a guess.
Then the candidate is *re-run from the entry point* and measured. That is what
keeps it honest: every direction counted here was reached by a whole run of
the program from its first statement, with one input state and no
intervention, which is the same bar the rest of the tool is held to.

Three consequences worth stating, because they are what make it work:

**Depth stops mattering.** Each step is one decision away from a state that
is already reachable, so an n-deep target is n local problems rather than one
n-times-harder one. The frontier extends itself: solving a guard yields a
state that reaches further, which exposes the next guard, and so on.

**"No entry state can do this" becomes an answer.** A guard whose operands
are all opaque - a counter, a `STRING` result, a stub return - cannot be
flipped by any input, and the search says so instead of spending its budget
proving it once per route. That number is reported, because a residual made
of genuinely input-independent decisions is a different finding from a
residual made of ones the solver could not lift.

**Nothing is pinned.** The candidate changes the *initial* value of a field
and the program owns it from then on, exactly as before. If the program
overwrites it anyway the re-run scores nothing and the candidate dies, which
is the correct outcome and costs one run to discover.
"""

from __future__ import annotations

import heapq

from .conditions import condition_atoms
from .heuristics import complement_value
from .interpreter import Interpreter
from .ir import flip, holds, parse_term
from .origins import splice

# The interpreter names a loop by the verb it saw and `coverage` names it by
# what it is; the two have to agree or a solved loop looks unsolved and is
# proposed again on every pass.
_KIND = {"PERFORM_UNTIL": "LOOP", "PERFORM_VARYING": "LOOP"}

# A group this wide is a table, not a record, and laying it out field by
# field costs more than the consistency it buys.
_MAX_LAYOUT = 4096


def direction_key(guard, result=None):
    return (guard.paragraph, guard.ordinal, _KIND.get(guard.kind, guard.kind),
            bool(guard.result if result is None else result))


# --------------------------------------------------------------------------
# Placing a value in the entry state
# --------------------------------------------------------------------------

def _elementary(model, name: str, cache: dict) -> list:
    if name in cache:
        return cache[name]
    fields: list = []
    if model.descendants(name):
        from .layout import record_layout
        try:
            laid = record_layout(model, name)
            if len(laid) <= _MAX_LAYOUT:
                fields = [(f.name, f.offset, f.length) for f in laid
                          if f.length and not model.descendants(f.name)]
        except Exception:                                        # noqa: BLE001
            fields = []
    cache[name] = fields
    return fields


def _is_numeric_pic(spec: str) -> bool:
    spec = (spec or "").upper()
    return bool(spec) and "9" in spec and "X" not in spec and "A" not in spec


def render(model, field_name: str, value, width: int | None):
    """The bytes a field of this shape holds when it holds this value.

    Numeric fields are right-justified and zero-filled and alphanumeric ones
    left-justified and space-filled, which is what a group move will hand
    back when it splits the bytes up again. Getting this backwards puts the
    digits of an account number in the wrong half of the field and the guard
    goes the way it already went.
    """
    if width is None:
        return value
    if _is_numeric_pic(model.pic_of(field_name)):
        try:
            number = int(float(str(value).strip() or 0))
        except (TypeError, ValueError):
            number = 0
        return str(abs(number)).rjust(width, "0")[-width:]
    text = "" if value is None else str(value)
    if isinstance(value, bool):
        text = "1" if value else "0"
    return text.ljust(width)[:width]


def place(model, state: dict, delta: dict, origin, field_name: str,
          value) -> None:
    """Record, in ``delta``, the entry-state edit that puts ``value`` where
    ``origin`` says this field's bytes come from."""
    if origin.whole:
        delta[origin.name] = value
        return
    base = delta.get(origin.name, state.get(origin.name, ""))
    delta[origin.name] = splice(base, origin.lo, origin.hi,
                                render(model, field_name, value, origin.width)
                                if origin.width is not None else str(value))


def apply_delta(model, state: dict, delta: dict, cache: dict) -> dict:
    """A new entry state, with the edits in place and groups kept consistent.

    A group written as bytes has to reach its children too: a later guard may
    read `CDEMO-ACCT-ID` directly rather than through the move, and a state
    where the group and its fields disagree is a state the program can never
    have been handed.
    """
    fresh = dict(state)
    for name, value in delta.items():
        fresh[name] = value
        if not isinstance(value, str):
            continue
        for child, offset, length in _elementary(model, name, cache):
            piece = value[offset:offset + length]
            if len(piece) < length:
                continue
            if _is_numeric_pic(model.pic_of(child)):
                try:
                    fresh[child] = int(piece)
                except (TypeError, ValueError):
                    fresh[child] = piece
            else:
                fresh[child] = piece
    return fresh


# --------------------------------------------------------------------------
# What one atom needs
# --------------------------------------------------------------------------

_SHAPES = {
    "NUMERIC": ("0", "A"), "ALPHABETIC": ("A", "1"),
    "ALPHABETIC-UPPER": ("A", "1"), "ALPHABETIC-LOWER": ("a", "1"),
}


def _wanted(model, name: str, op: str, const):
    """The value ``name`` must hold for ``name op const`` to be true."""
    pic = model.pic_of(name)
    if op in ("IS", "IS-NOT"):
        klass = str(const).upper()
        if klass in _SHAPES:
            hit, miss = _SHAPES[klass]
            return (hit if op == "IS" else miss) * max(1, _width(model, name))
        wanted = {"POSITIVE": (1, 0), "NEGATIVE": (-1, 0), "ZERO": (0, 1)}
        return wanted[klass][0 if op == "IS" else 1] if klass in wanted else None
    if op == "=":
        return const
    if op == "!=":
        return complement_value(name, pic, [const])
    if isinstance(const, bool) or not isinstance(const, (int, float)):
        try:
            const = float(str(const).strip())
        except (TypeError, ValueError):
            return None
    step = 1 if float(const) == int(const) else 0.01
    return {">": const + step, ">=": const, "<": const - step,
            "<=": const}.get(op)


def _width(model, name: str) -> int:
    from .layout import byte_length
    pic = model.pic_of(name)
    if not pic:
        return 0
    try:
        return byte_length(pic, model.usage_of(name),
                           model.look(model.sign, name, "") or "")
    except Exception:                                            # noqa: BLE001
        return 0


def _sides(model, atom, values: dict):
    """(field, operator, wanted-constant) for an atom, or None.

    Handles the three shapes a comparison arrives in: against a literal,
    against another field - whose *current* value stands in for the literal,
    which is the only reading available and is the one the run just used -
    and a bare level-88, whose obligation belongs to its parent.
    """
    lhs, rhs, op = atom.lhs, atom.rhs, atom.op
    if lhs.kind == "var" and rhs.kind == "const" and rhs.value is True:
        entry = model.condition_names.get(lhs.name)
        if entry:
            parent, raw = entry
            consts = [parse_term(v).value for v in raw]
            consts = [c for c in consts if not isinstance(c, bool)]
            if not consts:
                return None
            if op == "=":
                return parent, parent, "=", consts[0]
            other = complement_value(parent, model.pic_of(parent), consts)
            return None if other is None else (parent, parent, "=", other)
    if lhs.kind == "var" and rhs.kind == "const":
        return lhs.name, lhs.key, op, rhs.value
    if rhs.kind == "var" and lhs.kind == "const":
        return rhs.name, rhs.key, flip(op), lhs.value
    if lhs.kind == "var" and rhs.kind == "var":
        # `IF A = B`: B holds something, and that something is a value A can
        # be made to hold. Reading it off the run rather than inventing one
        # keeps this evidence-based - the program itself put it there.
        for field, key, other in ((lhs, lhs.key, rhs.key), (rhs, rhs.key, lhs.key)):
            if other in values:
                sense = op if field is lhs else flip(op)
                return field.name, key, sense, values[other]
    return None


def deltas_for(model, guard, want: bool, state: dict, cache: dict,
               limit: int = 2) -> tuple:
    """Entry-state edits that would send this guard the other way.

    Returns ``(deltas, liftable)``. ``liftable`` is false when every way of
    satisfying the condition needs a field whose value the entry state no
    longer decides - a genuinely input-independent decision, which is worth
    distinguishing from one the solver merely failed on.
    """
    out, liftable = [], False
    for alternative in condition_atoms(guard.condition, negate=not want):
        if not alternative:
            continue
        delta: dict = {}
        ok = True
        for atom in alternative:
            found = _sides(model, atom, guard.values)
            if found is None:
                ok = False
                break
            field, key, op, const = found
            # A conjunct the run already satisfies needs nothing done to it,
            # and that includes one the entry state could not have set. `IF
            # A AND B` with A a program-computed flag that happens to be true
            # is solved by setting B alone; failing the whole alternative
            # because one atom is opaque throws away the case where the
            # opaque half is already going the right way, which on a screen
            # program is most of them.
            if key in guard.values and holds(guard.values[key], op, const):
                continue
            origin = guard.origins.get(key)
            if origin is None:
                ok = False
                break
            liftable = True
            value = _wanted(model, field, op, const)
            if value is None:
                ok = False
                break
            place(model, state, delta, origin, field, value)
        if ok and delta:
            out.append(delta)
            if len(out) >= limit:
                break
    return out, liftable


# --------------------------------------------------------------------------
# The search
# --------------------------------------------------------------------------

def _signature(state: dict) -> tuple:
    return tuple(sorted((k, repr(v)) for k, v in state.items()))


def _seed(item) -> tuple:
    """A seed is a state and a world, and optionally the outside world a
    derived plan arranged around it. Carrying the plan's stubs is what lets
    the frontier start where derivation finished rather than at the entry
    point: a state that needs a file to have returned end-of-file cannot be
    expressed as an input at all, and without the stubs every seed of that
    kind collapses back to the same shallow run."""
    if len(item) == 2:
        return item[0], item[1], None, None
    return item


def lift(program, entry: str, *, seeds, defaults_for, budget: int = 600,
         fanout: int = 2, attempts: int = 4, on_trace=None,
         should_stop=None) -> dict:
    """Extend the reached frontier one decision at a time.

    ``seeds`` are ``(state, world)`` pairs to start from and ``defaults_for``
    maps a world name to the I/O defaults for it.

    The queue is deepest-first and that is the whole search strategy. A state
    reached by solving six guards in a row is worth more than the seventh
    seed, because it is the only one standing anywhere near the code that is
    still dark - breadth-first spends its entire budget re-confirming the
    first twenty lines from two thousand starting points. Ties break on
    discovery order, so the same command gives the same runs every time and
    nothing here is sampled.

    A direction may be attempted more than once. The same guard reached from
    a different state has different origins - the field that was opaque on
    one path is an input on another - so refusing a second attempt throws
    away the thing that makes this work. It is bounded, because retrying
    forever on an unsatisfiable guard is how a budget disappears.
    """
    model = program.model
    cache: dict = {}
    covered: set = set()
    traces: list = []
    seen: set = set()
    tried: set = set()
    spent: dict = {}
    queue: list = []
    order = [0]
    stats = {"runs": 0, "proposed": 0, "accepted": 0, "opaque": 0,
             "unliftable": set(), "max_depth": 0}

    outside: list = [(None, None)]

    def push(state, world, depth, world_index):
        signature = (_signature(state), world, world_index)
        if signature in seen:
            return False
        seen.add(signature)
        order[0] += 1
        heapq.heappush(queue, (-depth, order[0], state, world, world_index))
        return True

    for item in seeds:
        state, world, stubs, terminals = _seed(item)
        index = 0
        if stubs or terminals:
            outside.append((stubs, terminals))
            index = len(outside) - 1
        push(state, world, 0, index)

    while queue and stats["runs"] < budget:
        # A run budget bounds the search but says nothing about how long a
        # run takes, and on a large program that is the whole difference
        # between a bounded command and an open-ended one.
        if should_stop is not None and should_stop():
            stats["stopped_early"] = True
            break
        negative, _seq, state, world, world_index = heapq.heappop(queue)
        depth = -negative
        stubs, terminals = outside[world_index]
        interp = Interpreter(program, state, defaults=defaults_for(world),
                             stubs=stubs, terminals=terminals,
                             track_origins=True)
        try:
            trace = interp.run(entry)
        except Exception:                                        # noqa: BLE001
            continue
        stats["runs"] += 1
        stats["max_depth"] = max(stats["max_depth"], depth)
        traces.append(trace)
        if on_trace is not None:
            on_trace(trace)
        covered |= {direction_key(g) for g in trace.guards}

        for guard in trace.guards:
            want = not bool(guard.result)
            key = direction_key(guard, want)
            if key in covered or spent.get(key, 0) >= attempts:
                continue
            found, liftable = deltas_for(model, guard, want, state, cache,
                                         limit=fanout)
            if not liftable:
                # Opaque *from here*. The same guard reached along another
                # path may read a field the entry state still owns, so this
                # is a fact about one state and not about the program, and
                # retiring the direction on it would throw the retry away.
                if key not in stats["unliftable"]:
                    stats["opaque"] += 1
                stats["unliftable"].add(key)
                continue
            stats["unliftable"].discard(key)
            for delta in found:
                signature = (key, tuple(sorted((n, repr(v))
                                               for n, v in delta.items())))
                if signature in tried:
                    continue
                tried.add(signature)
                stats["proposed"] += 1
                spent[key] = spent.get(key, 0) + 1
                if push(apply_delta(model, state, delta, cache), world,
                        depth + 1, world_index):
                    stats["accepted"] += 1

    stats["unliftable"] = len(stats["unliftable"])
    stats["queue_left"] = len(queue)
    return {"traces": traces, "stats": stats, "covered": covered}
