"""One field repaired per run, judged by the interpreter: cascade repair.

The residual on validation-heavy screen programs has one dominant shape,
measured before this was built: a first-match ``EVALUATE TRUE`` whose arms
test per-field validation flags, dozens of them, in screen order. Arm *k*
is only evaluated after arms 1..k-1 missed, so its True direction needs a
run where every earlier field passed its edit and field *k* alone failed -
an almost-all-valid screen. On the program that motivated this, one such
cascade held 84 of the 235 missing directions, and every other phase had a
structural reason to stop short:

* the frontier search (:mod:`frameladder.lift`) reads a flag that holds a
  program-written sentinel (``SET FLG-X-NOT-OK TO TRUE``) and correctly
  reports it opaque - no entry byte decides it *on that run*;
* the staged stub search proposes one action set per run, and the arm needs
  ~k fields repaired at once - beyond any bounded fan-out;
* the re-entry battery's one-field-spoiled states vary a *failing*
  background, which the first arm of the cascade catches every time.

So this phase is greedy and iterative where those are combinatorial: run
the best recipe the ledger already holds, read the trace to see which arm
fired - the guard events name the flag that went invalid - repair *that*
field, rerun, repeat. Each iteration is one local problem: find the input
bytes that make one edit pass. When no arm fires anywhere in the run, the
all-valid recipe witnesses every arm's False direction, and one-field
-spoiled variants of it fell the True directions one arm per run.

The repair primitive chases evidence, never names. A flag's sentinel is
established by a conditional write (`provenance.establishing_writes`); the
write's guard was evaluated by the run on live copies of the input
(`GuardEvent.origins`), so `lift.deltas_for` can place the flipping edit at
entry bytes. Where the tested value travelled through copies, group moves
or a REDEFINES, the goal recurses through the writers (`prov.visible`),
decomposes across the layout (`lift._elementary`) and slices the wanted
value by byte offset. And where the chase bottoms out at an external
operation - the record a ``READ`` delivered, the map a ``RECEIVE`` filled -
the repair is a *staged stub field* merged over the base recipe's own
staging (`stubsearch.staged_recipes`), because no entry byte survives to a
field the program rebuilds from a record on every cycle. The interpreter
is the sole judge: a candidate that does not move the firing frontier is
discarded, and a direction is only ever credited through the battery's
deduplicating replay - the same bar every other phase meets.

Negatives are first-class: every arm the loop cannot repair or spoil is
reported with the reason (``no_base`` - nothing in the ledger evaluates the
cascade; ``no_actions`` - no evidence chain reaches an input; ``exhausted``
- candidates existed and none advanced; ``not_evaluated`` - the passing run
never reached the arm), because a residual this mechanism cannot speak to
is a different finding from one it merely ran out of budget for.
"""

from __future__ import annotations

from .conditions import condition_atoms
from .heuristics import complement_value
from .interpreter import Interpreter
from .ir import flip, parse_term
from .lift import _elementary, apply_delta, deltas_for, render
from .stubsearch import (_TERMINATING, _atom_options, _const_options,
                         _site_when, staged_recipes)

# Bounded fan-out, everywhere - the same discipline stubsearch documents.
MIN_ARMS = 6            # a first-match chain this long is a cascade
MAX_PROPOSALS = 10      # candidate action sets per goal
MAX_DEPTH = 6           # hops of writer / group chasing per goal
MAX_BASES = 3           # base recipes tried per cascade
SPOIL_TRIES = 8         # candidate spoils per missing arm
REPAIR_TRIES = 14       # candidate repairs per firing arm


# --------------------------------------------------------------------------
# Cascades: first-match WHEN chains, indexed once
# --------------------------------------------------------------------------

def cascades(program) -> list:
    """Every EVALUATE with at least ``MIN_ARMS`` arms, as
    ``{"para", "line", "arms": [{ordinal, line, value, index}], "order"}``.

    ``order`` maps arm ordinal to its position in the chain; the OTHER arm
    is included (it is the pass arm - the direction the all-valid run
    takes) and carries ``value`` "OTHER".
    """
    out: list = []

    def walk(stmt, para):
        if stmt.get("type") == "EVALUATE":
            arms = [c for c in stmt.get("children") or []
                    if c.get("type") == "WHEN"]
            if len(arms) >= MIN_ARMS:
                rows = [{"ordinal": a.get("ordinal", -1),
                         "line": a.get("line_start", 0),
                         "value": (a.get("attributes", {}).get("value", "")
                                   or "").strip(),
                         "index": i} for i, a in enumerate(arms)]
                out.append({"para": para, "line": stmt.get("line_start", 0),
                            "arms": rows,
                            "order": {r["ordinal"]: r["index"]
                                      for r in rows}})
        for child in stmt.get("children") or []:
            walk(child, para)

    for para in program.paragraphs:
        for stmt in para.get("statements", []):
            walk(stmt, para["name"])
    return out


def _is_other(value: str) -> bool:
    return (value or "").strip().upper() in ("OTHER", "ANY")


def cascade_keys(cascade) -> list:
    """Every ledger key this cascade owns, both directions."""
    return [(cascade["para"], arm["ordinal"], "WHEN", direction)
            for arm in cascade["arms"] for direction in (True, False)]


# --------------------------------------------------------------------------
# Reading a trace: what fired, and where
# --------------------------------------------------------------------------

def firing_arms(trace, cascade) -> list:
    """Every ``(index, event)`` where a real arm of the cascade fired."""
    order, para = cascade["order"], cascade["para"]
    out = []
    for event in trace.guards:
        if event.paragraph != para or event.ordinal not in order \
                or not event.result or event.condition == "OTHER":
            continue
        out.append((order[event.ordinal], event))
    return out


def firing_progress(trace, cascade, benign=frozenset()):
    """``(depth, firing_event)`` for the deepest firing arm worth chasing.

    ``benign`` holds the arm indices that already fired in the base run
    *below* its frontier - an earlier task's traversal failing its own
    shallow check, present in every run of this pseudo-conversation and
    not something a repair of the deep traversal can or should remove.
    Excluding them is what lets the loop see its own success: when the
    repaired region finally passes, the only firings left are the benign
    ones, and the frontier reads ``(None, None)`` - the goal state -
    instead of appearing to regress onto noise that was always there.
    """
    best = (None, None)
    for depth, event in firing_arms(trace, cascade):
        if depth in benign:
            continue
        if best[0] is None or depth > best[0]:
            best = (depth, event)
    return best


def _edit_paras(model, prov, guard) -> set:
    """The paragraphs that write the flags this arm tests.

    A pass is only the goal state when the run still *executes* the edits:
    a candidate that diverts the task past the validation path also
    extinguishes every firing arm, and by arm events alone that is
    indistinguishable from the all-valid screen - the flag-clearing
    shortcut evaluates the whole chain over LOW-VALUES too. The writers of
    the tested flag name the paragraphs that must still be entered.
    """
    out: set = set()
    try:
        alternatives = condition_atoms(
            guard.condition, names=frozenset(model.condition_names))
    except Exception:                                        # noqa: BLE001
        return out
    for alternative in alternatives:
        for atom in alternative:
            for side in (atom.lhs, atom.rhs):
                if side.kind != "var":
                    continue
                entry = model.condition_names.get(side.name)
                parent = entry[0] if entry else side.name
                for writer in prov.writes_to(parent):
                    if writer.kind in ("MOVE", "SET"):
                        out.add(writer.para)
    return out


def _line_events(trace) -> dict:
    out: dict = {}
    for g in trace.guards:
        out.setdefault((g.paragraph, g.line), []).append(g)
    return out


# --------------------------------------------------------------------------
# Candidate values: the program's own vocabulary, producible first
# --------------------------------------------------------------------------

def _siblings(model, parent: str) -> list:
    """Every 88-level of ``parent``, with its raw VALUE list."""
    out = []
    for name, entry in (model.condition_names or {}).items():
        if entry and entry[0].upper() == parent.upper():
            out.append((name, entry[1]))
    return out


def _atom_values(model, prov, atom) -> list:
    """``[(field, value)]`` choices satisfying one atom, producible first.

    The distinction that makes the chase land: a validation flag can only
    ever hold what the program *writes* into it - its 88 family names that
    vocabulary exactly - so an invented complement satisfies the atom on
    paper and is unproducible at every write site. Values with an
    establishing write come first; the invented complement is last, kept
    for the field the entry state still owns.
    """
    lhs, rhs, op = atom.lhs, atom.rhs, atom.op
    if rhs.kind == "var" and lhs.kind == "const":
        lhs, rhs, op = rhs, lhs, flip(op)
    if lhs.kind != "var" or rhs.kind != "const":
        return []
    name = lhs.name
    if isinstance(rhs.value, bool):
        entry = model.condition_names.get(name)
        if not entry:
            return []
        parent, raw = entry
        own = [parse_term(v).value for v in raw]
        own = [v for v in own if not isinstance(v, bool)]
        hold = (op == "=") == bool(rhs.value)
        pool = list(own) if hold else []
        for _sibling, values in _siblings(model, parent):
            for v in (parse_term(x).value for x in values):
                if isinstance(v, bool) or v in pool:
                    continue
                if (v in own) == hold:
                    pool.append(v)
        for v in sorted(prov.literals.get(parent, ()), key=repr):
            if isinstance(v, bool) or v in pool:
                continue
            if (v in own) == hold:
                pool.append(v)
        if not hold:
            extra = complement_value(parent, model.pic_of(parent), own)
            if extra is not None and extra not in pool:
                pool.append(extra)
        producible = [v for v in pool
                      if prov.establishing_writes(parent, "=", v)]
        rest = [v for v in pool if v not in producible]
        return [(parent, v) for v in producible + rest][:4]
    literals = sorted(prov.literals.get(name, ()), key=repr)
    return [(name, v) for v in
            _const_options(model, name, op, rhs.value, extra=literals)]


# --------------------------------------------------------------------------
# The goal solver: actions that make `name` hold `value` at `at`
# --------------------------------------------------------------------------
#
# An action is ("entry", field, value) or
# ("stub", op_key, when, field, value, site) - the same shapes
# `stubsearch.staged_recipes` already realizes over a base recipe.
# A proposal is a list of actions applied together.

def _entry_actions(delta: dict) -> list:
    return [("entry", name, value) for name, value in delta.items()]


def goal_actions(model, prov, trace_lines, state, name, value, at, cache,
                 depth=0, seen=frozenset()) -> list:
    """Proposals that plausibly put ``value`` in ``name`` at ``at``.

    Evidence chains, cheapest-first, every one verified by a rerun rather
    than trusted:

    * a conditional write establishes the value; its guard was evaluated
      by the run, so flipping the guard through its recorded origins is an
      entry edit (`deltas_for` on the guard's event);
    * the guarded writes that would *violate* the goal are steered around,
      one negated guard each (`_avoidance`);
    * the value arrives by MOVE from another field - a rename - so the
      goal transfers to the source at the move site;
    * the value arrives from an external operation, so the repair is a
      staged stub field over the base recipe's own staging;
    * the field is a group (or is re-described by one) whose *parts* are
      written individually; the goal decomposes across the layout, one
      byte-slice per part;
    * nothing but stubs ever writes the field, in which case the entry
      state still owns it in the worlds the battery runs and the direct
      edit is offered last.
    """
    key = (name.upper(), repr(value))
    if depth > MAX_DEPTH or key in seen:
        return []
    if not model.knows(name):
        # An intrinsic mis-parsed as a variable ("FUNCTION", a NUMVAL
        # argument list) is not a goal: nothing can hold the value, and the
        # phantom action it would emit overrides real candidates when
        # proposals merge. The declared set is the authority.
        return []
    seen = seen | {key}
    # A numeric goal is rendered to its field's bytes at the moment it is
    # stated: the range complement of a ``PIC 9(3)`` re-description is the
    # integer 1, and every hop from here - the X-typed twin, the screen
    # field that fills it - needs the *bytes* '001'. Handing the bare
    # integer down the chain plants '1  ' in an X field and fails the very
    # numeric test being repaired.
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        from .lift import _is_numeric_pic, _width
        width = _width(model, name)
        if width and _is_numeric_pic(model.pic_of(name)):
            value = render(model, name, value, width)
    out: list = []

    for writer in prov.establishing_writes(name, "=", value)[:3]:
        for atom in list(reversed(list(writer.guards or ())))[:2]:
            for event in _atom_events(trace_lines, atom)[-2:]:
                found, _liftable = deltas_for(model, event, not event.result,
                                              state, cache, limit=2)
                out.extend(_entry_actions(d) for d in found)

    # The value-carrying chases come before pure steering: a MOVE chain
    # that lands the wanted bytes at a screen field usually satisfies the
    # guards being steered around as a side effect, while a steering value
    # picked per-guard satisfies one check and fails its neighbours.
    # Writers take turns - round-robin, not sequential - because `visible`
    # ranks an unconditional writer above a conditional one, and on a
    # shared work variable the write that actually reaches this read is
    # often the conditional sibling; letting the first writer's chase fill
    # the proposal cap starves the one that lands.
    chases: list = []
    for writer in _writers_at(prov, name, at)[:4]:
        if writer.kind == "STUB" and writer.op_key not in _TERMINATING:
            out.append([("stub", writer.op_key, _site_when(prov, writer),
                         name, value, writer.para)])
        if writer.kind != "MOVE":
            continue
        source = parse_term(writer.source)
        if source.kind != "var" or source.name.upper() == name.upper():
            continue
        if source.refmod:
            # A sliced source relocates the goal onto a byte range of a
            # larger area; the static chase has no way to place it and a
            # whole-field edit lands the value at the wrong offset. The
            # origin-tracking flips already handle exactly this case.
            continue
        # A group move recorded against a child target names the whole
        # source group; the value belongs to the byte *twin* inside it,
        # not to the group.
        twins = _source_twins(model, cache, name, source.name)
        targets = twins[:2] if twins else [source.name]
        for target in targets:
            chases.append(goal_actions(model, prov, trace_lines, state,
                                       target, value,
                                       (writer.para, writer.line), cache,
                                       depth + 1, seen))
    for rank in range(max((len(c) for c in chases), default=0)):
        for chase in chases:
            if rank < len(chase):
                out.append(chase[rank])

    # Provocation, the mirror of avoidance: when an establishing write's
    # guard event is opaque - the tested bytes came from a record, not the
    # entry state - plant a value that makes the innermost guard *hold*,
    # so the write runs. This is what fires a validation sentinel on
    # demand: the failure write's guard is the failure condition, and
    # satisfying it is a value chase like any other. After the direct
    # chases on purpose - a carried value beats a provoked one when both
    # exist.
    for writer in prov.establishing_writes(name, "=", value)[:3]:
        for atom in list(reversed(list(writer.guards or ())))[:1]:
            choices = _atom_values(model, prov, atom) \
                or [(n, v) for n, _op, v
                    in (_atom_options(model, prov, atom) or [])]
            for field, wanted in choices[:2]:
                if field.upper() == name.upper():
                    continue
                out.extend(goal_actions(model, prov, trace_lines, state,
                                        field, wanted, at, cache,
                                        depth + 1, seen))

    out.extend(_avoidance(model, prov, trace_lines, state, name, value, at,
                          cache, depth, seen))

    out.extend(_decomposed(model, prov, trace_lines, state, name, value, at,
                           cache, depth, seen))
    out.extend(_twin_hop(model, prov, trace_lines, state, name, value,
                         cache, depth, seen))
    # The direct entry edit, only for a field the program itself never
    # writes: anything MOVE/SET-written is overwritten before the read -
    # nothing is pinned - and offering the edit anyway starves the chase
    # (every goal "succeeds" with a delta that cannot land). A field whose
    # only writers are stubs still arrives from the entry state in the
    # worlds the battery runs, so it keeps the edit.
    if not any(w.kind in ("MOVE", "SET") for w in prov.writes_to(name)):
        out.append([("entry", name, value)])

    unique, marks = [], set()
    for proposal in out:
        if not proposal:
            continue
        mark = tuple(sorted(repr(a) for a in proposal))
        if mark not in marks:
            marks.add(mark)
            unique.append(proposal)
    return unique[:MAX_PROPOSALS]


def _overlay_parts(model, cache, name) -> list:
    """Leaf fields covering ``name``'s bytes, REDEFINES overlays included.

    ``ACUP-NEW-OPEN-DATE PIC X(8)`` has no children of its own; the parts
    live under ``ACUP-NEW-OPEN-DATE-PARTS REDEFINES`` it, and `descendants`
    knows nothing about the overlay. Offsets are relative to the same first
    byte on both sides, so the overlay's layout speaks for the field.
    """
    parts = list(_elementary(model, name, cache))
    upper = name.upper()
    for overlay, base in (model.redefines or {}).items():
        if (base or "").upper() == upper:
            parts += [p for p in _elementary(model, overlay, cache)
                      if p[0] != overlay]
    seen: set = set()
    unique = []
    for part in parts:
        if part[0] not in seen:
            seen.add(part[0])
            unique.append(part)
    return unique


def _source_twins(model, cache, name, source_group) -> list:
    """Descendants of ``source_group`` covering the same bytes ``name``
    covers in the ancestor the group was moved onto. A group move is a
    byte copy, so the offsets correspond side to side; the ancestor whose
    width matches the source group is the one the MOVE actually wrote."""
    from .lift import _width
    span = _width(model, source_group)
    if not span:
        laid = _elementary(model, source_group, cache)
        span = max((o + l for _n, o, l in laid), default=0)
    parents = model.parent or {}
    child = name.upper()
    ancestor = parents.get(child)
    while ancestor:
        laid = {n: (o, l) for n, o, l in _elementary(model, ancestor, cache)}
        width = max((o + l for o, l in laid.values()), default=0)
        if child in laid and width == span:
            offset, length = laid[child]
            return [n for n, o, l
                    in _overlay_parts(model, cache, source_group)
                    if o == offset and l == length]
        ancestor = parents.get(ancestor.upper())
    return []


def _writers_at(prov, name, at) -> list:
    """Writers of ``name``, nearest preceding line first at the read site.

    `prov.visible` prefers an unconditional writer over a conditional one
    at the same distance - the sound order for a planner that cannot know
    whether the guard held. This chase runs against a concrete trace, and
    the shared-work-variable idiom (``MOVE <field-k> TO WS-EDIT-X`` /
    ``PERFORM edit`` / ``MOVE flags TO <flag-k>``) means the fill that
    belongs to this read is the nearest preceding one, guarded or not:
    preferring the unconditional sibling chases field k-1's input for
    field k's flag, forever.
    """
    writers = prov.visible(name, at)
    if not at:
        return writers
    para, line = at

    def key(writer):
        if writer.para == para and writer.line < line:
            return (0, -writer.line)
        return (1, 0)

    return sorted(writers, key=key)


def _atom_events(trace_lines, atom) -> list:
    origin = getattr(atom, "origin", "") or ""
    para, _sep, line = origin.rpartition(":")
    try:
        return trace_lines.get((para, int(line)), [])
    except ValueError:
        return []


def _blocking(prov, name, value) -> list:
    """Guarded writes that would violate ``name = value``.

    `provenance.blocking_writes` counts only MOVEs, but a validation flag's
    whole vocabulary arrives by ``SET`` and skipping those hides every
    sentinel this phase exists to steer around. Unguarded violators are
    ignored rather than fatal - the paragraph-top ``SET FLG-X-NOT-OK``
    default is one, and it is overridden by exactly the guarded writes
    being steered.
    """
    from .ir import holds
    out = []
    for writer in prov.writes_to(name):
        if writer.kind not in ("MOVE", "SET") or not writer.guards:
            continue
        source = parse_term(writer.source)
        if source.kind != "const" or holds(source.value, "=", value):
            continue
        out.append(writer)
    return out


def _avoidance(model, prov, trace_lines, state, name, value, at, cache,
               depth, seen) -> list:
    """Steer around the guarded writes that would violate the goal.

    The validation-flag shape: an unguarded ``SET FLG-X-ISVALID`` opens the
    edit and guarded failure writes override it - blank check, class test,
    range test, one field each. Holding the valid value means *none* of
    them ran, so each blocking write's innermost guard is negated and
    resolved back to the field it tests; the merged proposal - satisfying
    every check at once - is offered first, because a value chosen per
    check satisfies one while failing its neighbours (the lesson
    `derail_groups` already records). Sub-goals resolve at the *goal's*
    site, not the blocker's: a shared work variable is filled by the
    nearest preceding MOVE of whichever caller staged it, and `visible`
    can only see that from the frame the goal came down through.
    """
    from .ir import negate_atom
    blockers = _blocking(prov, name, value)
    if len(blockers) > 6:
        return []                 # a field everything writes is not a flag
    per_writer: list = []
    for writer in blockers:
        found: list = []
        for negated in negate_atom(writer.guards[-1]):
            for atom in [negated] + list(negated.alternatives or ()):
                for event in _atom_events(trace_lines, atom)[-1:]:
                    flips, _lift = deltas_for(model, event,
                                              not event.result, state,
                                              cache, limit=1)
                    found.extend(_entry_actions(d) for d in flips)
                choices = _atom_values(model, prov, atom) \
                    or [(n, v) for n, _op, v
                        in (_atom_options(model, prov, atom) or [])]
                for field, wanted in choices[:2]:
                    if field.upper() == name.upper():
                        continue
                    found.extend(goal_actions(
                        model, prov, trace_lines, state, field, wanted,
                        at, cache, depth + 1, seen))
                if found:
                    break
            if found:
                break
        per_writer.append(found)
    solved = [found for found in per_writer if found]
    if not solved:
        return []

    def coverage(found):
        return sum(len(str(a[2] if a[0] == "entry" else a[4]).strip("\x00 "))
                   for a in found[0])

    # Broad values first, narrow positional pieces last: the overlay in
    # `realized` lets a later piece override only the bytes it actually
    # states, so '0000' then '20  ' composes '2000' - every check's
    # constraint kept - while the reverse order buries the '20' under the
    # digits and the century test fails again.
    solved.sort(key=coverage, reverse=True)
    merged: list = []
    for found in solved:
        merged.extend(found[0])
    out = [merged] if len(solved) > 1 else []
    for found in solved:
        out.extend(found[:2])
    return out


def _decomposed(model, prov, trace_lines, state, name, value, at, cache,
                depth, seen) -> list:
    """The goal split across the parts a group's bytes are written through.

    An eight-byte date field has no writer of its own; the REDEFINES parts
    year / month / day do, each filled from its own screen field. The
    wanted value is rendered to the group's bytes and sliced by each
    written part's offset, and the per-part proposals merge into one.
    """
    if not isinstance(value, (str, int, float)) or isinstance(value, bool):
        return []
    parts = [p for p in _overlay_parts(model, cache, name)
             if prov.writes_to(p[0])]
    if not parts:
        return []
    width = max(offset + length for _n, offset, length in parts)
    text = render(model, name, value, max(width, len(str(value))))
    merged: list = []
    solved = 0
    for part, offset, length in parts[:8]:
        piece = text[offset:offset + length]
        found = goal_actions(model, prov, trace_lines, state, part, piece,
                             at, cache, depth + 1, seen)
        if found:
            solved += 1
            merged.extend(found[0])
    return [merged] if solved and merged else []


def _twin_hop(model, prov, trace_lines, state, name, value, cache, depth,
              seen) -> list:
    """The value arrives via a group move over an ancestor: find the byte
    twin on the source side and chase it there. A whole-flags-area MOVE
    writes the per-field year flag without ever naming it; the twin at the
    same offset of the source group is the field the edit paragraph
    actually sets."""
    if prov.writes_to(name):
        return []
    out: list = []
    parents = model.parent or {}
    child = name.upper()
    ancestor = parents.get(child)
    while ancestor:
        laid = {n: (o, l) for n, o, l in _elementary(model, ancestor, cache)}
        if child not in laid:
            break
        offset, length = laid[child]
        # A REDEFINES sibling covering the same bytes *is* this field under
        # another name: a range test on the numeric re-description of a
        # PIC X part has no writer of its own, and the MOVE that fills the
        # bytes names the alphanumeric twin.
        for twin, o, l in _elementary(model, ancestor, cache):
            if o == offset and l == length and twin != child \
                    and prov.writes_to(twin):
                out.extend(goal_actions(model, prov, trace_lines, state,
                                        twin, value, None, cache,
                                        depth + 1, seen))
        for writer in prov.writes_to(ancestor)[:4]:
            if writer.kind != "MOVE":
                continue
            source = parse_term(writer.source)
            if source.kind != "var":
                continue
            twins = [n for n, o, l in _elementary(model, source.name, cache)
                     if o == offset and l == length]
            for twin in twins[:2]:
                out.extend(goal_actions(model, prov, trace_lines, state,
                                        twin, value,
                                        (writer.para, writer.line), cache,
                                        depth + 1, seen))
        if prov.writes_to(ancestor):
            break
        ancestor = parents.get(ancestor.upper())
    return out


def arm_proposals(model, prov, trace, state, guard, want, cache) -> list:
    """Action sets that would send one cascade arm ``want``-ward.

    Origins first - when the run's own bookkeeping says which entry bytes
    decide the arm, that answer is exact - then the evidence chase through
    the flag's writers for the sentinel case origins cannot see.
    """
    trace_lines = _line_events(trace)
    found, _liftable = deltas_for(model, guard, want, state, cache, limit=2)
    out = [_entry_actions(d) for d in found]
    for alternative in condition_atoms(
            guard.condition, negate=not want,
            names=frozenset(model.condition_names))[:3]:
        merged: list = []
        for atom in alternative:
            choices = _atom_values(model, prov, atom) \
                or [(n, v) for n, _op, v
                    in (_atom_options(model, prov, atom) or [])]
            first = None
            for name, value in choices[:3]:
                proposals = goal_actions(model, prov, trace_lines, state,
                                         name, value,
                                         (guard.paragraph, guard.line),
                                         cache)
                out.extend(proposals[:3])
                if proposals and first is None:
                    first = proposals[0]
            if first:
                merged.extend(first)
        if len(alternative) > 1 and merged:
            out.append(merged)
    unique, marks = [], set()
    for proposal in out:
        if not proposal:
            continue
        mark = tuple(sorted(repr(a) for a in proposal))
        if mark not in marks:
            marks.add(mark)
            unique.append(proposal)
    return unique


def realized(model, base, proposal, cache) -> list:
    """Concrete recipes for one proposal over one base run.

    Entry actions go through `apply_delta`, which keeps a group and its
    children byte-consistent; stub actions are merged over the base's own
    staging by `stubsearch.staged_recipes`. A repaired record field wants
    to arrive on *every* matching call - a valid value is a property of
    the record, not a one-shot fault - so the persistent form is tried
    first, the reverse of the fault search's ordering.
    """
    from .lift import _width

    def shaped(field, value):
        # A value is delivered in the field's own bytes: a composed
        # candidate wider than the field would otherwise splice past it
        # and clobber the neighbours this loop just repaired. A number is
        # rendered as zero-filled digits even into an X field - it exists
        # because some class or range test wants digits, and space padding
        # fails the very NUMERIC test it was derived from.
        width = _width(model, field)
        if not width:
            return value
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            return str(abs(int(value))).rjust(width, "0")[-width:]
        return render(model, field, value, width)

    def overlay(previous, value):
        # Two actions on one field are two *constraints* on it, usually
        # from different checks: the numeric chase says '0000', the
        # century chase says '20  '. Overlaying the later value's
        # non-blank bytes composes '2000' - both satisfied - while a
        # full-width later value keeps plain last-wins semantics.
        if not isinstance(previous, str) or not isinstance(value, str) \
                or len(previous) != len(value):
            return value
        return "".join(p if v in (" ", "\x00") else v
                       for p, v in zip(previous, value))

    entry_delta: dict = {}
    for action in proposal:
        if action[0] != "entry":
            continue
        field, value = action[1], shaped(action[1], action[2])
        entry_delta[field] = overlay(entry_delta[field], value) \
            if field in entry_delta else value
    merged_stub: dict = {}
    stubs = []
    for action in proposal:
        if action[0] != "stub":
            continue
        slot = (action[1], tuple(sorted(action[2].items())), action[3])
        value = shaped(action[3], action[4])
        if slot in merged_stub:
            merged_stub[slot] = overlay(merged_stub[slot], value)
        else:
            merged_stub[slot] = value
    for (op_key, when_items, field), value in merged_stub.items():
        stubs.append(("stub", op_key, dict(when_items), field, value, ""))
    state = apply_delta(model, base[0] or {}, entry_delta, cache) \
        if entry_delta else dict(base[0] or {})
    staged_base = (state, base[1], base[2], base[3])
    if not stubs:
        return [staged_base]
    variants = list(staged_recipes(model, staged_base, stubs))
    return list(reversed(variants))


# --------------------------------------------------------------------------
# The loop
# --------------------------------------------------------------------------

def _base_recipes(ledger, cascade) -> list:
    """Base recipes for one cascade, most cascade-progress first.

    A True witness of a deep non-OTHER arm demonstrably ran the validation
    gauntlet to that arm with everything before it passing - the furthest
    along any recorded run got. The OTHER witness may have passed the
    whole chain (or reached it by a flag-clearing shortcut; one probe run
    tells which). An empty state under ``populated`` is the last resort so
    a program with no cascade witness at all still gets a probe.
    """
    order = cascade["order"]
    ranked: list = []
    for arm in cascade["arms"]:
        key = (cascade["para"], arm["ordinal"], "WHEN", True)
        recipe = ledger.witnesses.get(key)
        if recipe is None:
            continue
        rank = -1 if _is_other(arm["value"]) else order[arm["ordinal"]]
        ranked.append((rank, recipe))
    ranked.sort(key=lambda item: -item[0])
    out, marks = [], set()
    for _rank, recipe in ranked:
        if recipe in marks:
            continue
        marks.add(recipe)
        payload = recipe.payload()
        out.append((payload["input_state"], payload["world"],
                    payload["stubs"], payload["terminals"]))
        if len(out) >= MAX_BASES:
            break
    out.append(({}, "populated", None, None))
    return out


def repair(program, prov, ledger, run, *, entry: str, defaults_for,
           budget: int = 200, on_witness=None, verbose=False) -> dict:
    """Greedy repair over every cascade with missing directions.

    ``run`` is the battery's crediting closure - a fresh interpreter per
    recipe, deduplicated, folding the trace into the ledger - so nothing
    is credited here except through the same replay every other phase
    uses. Probe runs (which need origin tracking and are not credited)
    and crediting replays both count against ``budget``.
    """
    model = program.model
    cache: dict = {}
    stats = {"budget": budget, "runs": 0, "cascades": 0, "passed": 0,
             "repaired_arms": 0, "spoiled": 0, "stalled": []}
    spent = [0]

    def say(*parts):
        if verbose:
            print("[repair]", *parts)

    def probe(recipe, cascade, benign=frozenset()):
        spent[0] += 1
        state, world, stubs, terminals = recipe
        interp = Interpreter(program, dict(state or {}), stubs=stubs,
                             terminals=terminals,
                             defaults=defaults_for(world),
                             track_origins=True)
        try:
            trace = interp.run(entry)
        except Exception:                                    # noqa: BLE001
            return (None, None), None
        return firing_progress(trace, cascade, benign), trace

    def credit(recipe, tag):
        outcome = run(*recipe, "repair:%s" % tag)
        if outcome is not None:
            spent[0] += 1
        return outcome

    todo = []
    covered = ledger.covered()
    for cascade in cascades(program):
        gap = [k for k in cascade_keys(cascade) if k not in covered]
        if gap:
            todo.append((len(gap), cascade))
    todo.sort(key=lambda item: -item[0])

    for _gap, cascade in todo:
        if spent[0] >= budget:
            break
        stats["cascades"] += 1
        para, order = cascade["para"], cascade["order"]
        reasons: dict = {}
        passed_here = False

        def missing_arms():
            return [arm for arm in cascade["arms"]
                    if not _is_other(arm["value"])
                    and (para, arm["ordinal"], "WHEN", True)
                    not in ledger.witnesses]

        # Every base gets its ascent and its spoils. Different bases reach
        # the cascade in different program modes - one shows fetched
        # details and clears the validation flags before the send, another
        # arrives mid-update and keeps them - and an arm unspoilable from
        # the first mode falls in the second. Stopping at the first
        # passing base measured 73 arms unfelled that a later base fells.
        for base in _base_recipes(ledger, cascade):
            if spent[0] >= budget or (passed_here and not missing_arms()):
                break
            recipe = base
            # Candidate dedup is per base on purpose: the same proposal
            # over a different base is a different run, and the base that
            # arrives in the right program mode must not be starved by a
            # sibling having spent the idea in the wrong one.
            tried = set()
            best, trace = probe(recipe, cascade)
            if trace is None:
                continue
            # The arms already firing below this base's frontier are an
            # earlier task's own shallow failures - present in every run,
            # not repairable from here, and already witnessed. They are
            # excluded from the metric so a pass of the deep traversal
            # reads as the goal state rather than a regression onto them.
            benign = frozenset(i for i, _e in firing_arms(trace, cascade)) \
                - {best[0]}
            best = firing_progress(trace, cascade, benign)
            # The greedy ascent. Repair the deepest firing arm; accept only
            # a candidate that moves the frontier strictly deeper (the next
            # field is now the failure) or extinguishes it (no non-benign
            # arm fires anywhere: the goal state). Lateral moves - the same
            # field's BLANK arm trading places with its NOT-OK arm - looked
            # like motion under a weaker rule and oscillated the loop.
            while best[1] is not None and spent[0] < budget:
                guard = best[1]
                proposals = arm_proposals(model, prov, trace, recipe[0],
                                          guard, False, cache)
                advanced = False
                for proposal in proposals[:REPAIR_TRIES]:
                    mark = (guard.ordinal,
                            tuple(sorted(repr(a) for a in proposal)))
                    if mark in tried:
                        continue
                    tried.add(mark)
                    for candidate in realized(model, recipe, proposal,
                                              cache):
                        found, next_trace = probe(candidate, cascade,
                                                  benign)
                        accept = next_trace is not None and (
                            found[0] is None or found[0] > best[0])
                        if accept and found[0] is None:
                            # A pass that stopped running the edits is a
                            # diversion, not a repair: the arm went quiet
                            # because nothing computed its flag.
                            edits = _edit_paras(model, prov, guard)
                            accept = not edits or \
                                edits & next_trace.entered_set
                        if accept:
                            say("accept", para, "arm", guard.ordinal,
                                "->", found[0],
                                [(a[0], a[1] if a[0] == "entry" else a[3],
                                  repr(a[2] if a[0] == "entry"
                                       else a[4])[:16])
                                 for a in proposal][:3])
                            recipe, best, trace = candidate, found, \
                                next_trace
                            stats["repaired_arms"] += 1
                            credit(recipe, "%s:repair" % para)
                            advanced = True
                        if advanced or spent[0] >= budget:
                            break
                    if advanced or spent[0] >= budget:
                        break
                if not advanced and best[1] is not None:
                    say("stall", para, "arm", guard.ordinal,
                        guard.condition[:40], "with",
                        [[(a[0], a[1] if a[0] == "entry" else a[3],
                           repr(a[2] if a[0] == "entry" else a[4])[:14])
                          for a in pr] for pr in proposals[:5]])
                    if spent[0] < budget:
                        reasons.setdefault(
                            guard.ordinal,
                            "exhausted" if proposals else "no_actions")
                    break
            if best[1] is not None:
                continue                    # this base stalled; try the next
            say("PASS", para, "benign", sorted(benign))
            if not passed_here:
                stats["passed"] += 1
                passed_here = True
            credit(recipe, "%s:pass" % para)
            if on_witness is not None:
                on_witness(recipe)
            for arm in missing_arms():
                if spent[0] >= budget:
                    break
                key = (para, arm["ordinal"], "WHEN", True)
                event = next((g for g in reversed(trace.guards)
                              if g.paragraph == para
                              and g.ordinal == arm["ordinal"]), None)
                if event is None:
                    reasons.setdefault(arm["ordinal"], "not_evaluated")
                    continue
                proposals = arm_proposals(model, prov, trace, recipe[0],
                                          event, True, cache)
                felled = False
                for proposal in proposals[:SPOIL_TRIES]:
                    for candidate in realized(model, recipe, proposal,
                                              cache):
                        credit(candidate, "%s:spoil@%d"
                               % (para, order[arm["ordinal"]]))
                        if key in ledger.witnesses:
                            stats["spoiled"] += 1
                            felled = True
                            if on_witness is not None:
                                on_witness(candidate)
                            break
                        if spent[0] >= budget:
                            break
                    if felled or spent[0] >= budget:
                        break
                if not felled and spent[0] < budget:
                    say("spoil failed", para, arm["ordinal"],
                        arm["value"][:40], len(proposals), "proposals")
                    reasons.setdefault(
                        arm["ordinal"],
                        "exhausted" if proposals else "no_actions")
        for arm in missing_arms():
            reason = reasons.get(arm["ordinal"])
            if reason is None and spent[0] >= budget:
                continue
            stats["stalled"].append(
                {"paragraph": para, "ordinal": arm["ordinal"],
                 "condition": arm["value"][:80],
                 "reason": reason or ("no_base" if not passed_here
                                      else "not_evaluated")})
    stats["runs"] = spent[0]
    return stats
