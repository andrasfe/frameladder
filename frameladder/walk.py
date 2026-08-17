"""One upstream-walking loop: the frontier's position is the induction variable.

`chain.solve` is goal-directed but it *jumps*. It takes the goal's essential
values, asks `provenance` who writes each one, and recurses straight into that
writer - skipping every paragraph in between. Skipping them is why it needed
patching three times: a paragraph on the route that overwrites a requirement is
invisible to a solver that never meets it, so each discovered clobber was
answered with another special case (stage the stub delivery too, pin at entry
as a last resort, chase MOVEs three hops).

This module replaces the jump with a walk. The state is a *requirement set*

    R = {variable: frozenset(satisfying values)}

attached to a frontier paragraph P, and the loop's single induction step moves
P one hop upstream along the route from entry. At every hop the requirements
are reconciled against the paragraph actually standing there:

* requirements it **writes** are solved demand-first (find inputs making it
  emit a satisfying value) and offer-second (intersect what it demonstrably
  *can* emit with what is wanted). An empty intersection is a named refusal
  carrying the hop address, not a silent absence.
* requirements it **does not touch** pass through - and because the walk meets
  every intervening paragraph, a clobber is detected here *by construction*
  rather than by a special case bolted on after the fact.
* its own preconditions **join** R, so the set transforms as the frontier
  moves: a concrete weakest precondition, computed by micro-execution rather
  than symbolically. (Symbolic derivation already measured zero here.)

Sets rather than exact values are the point of the reconciliation. `chain`
carried one byte string per variable and refused whenever a producer would not
write that exact byte, even when the requirement was really "anything not
blank" and the producer emitted a perfectly good non-blank. The satisfying set
is measured, never assumed: it is the set of values that were *observed* to
fire the direction during the local sweep.

At the top of the route the surviving requirements must name only variables the
entry state controls (pin them), a stub controls (stage them), or the previous
cycle's state - and that last case recurses the *same* loop into cycle k-1,
which is what makes the cycle probe a case of the loop rather than a special
beside it. Then one forward run from entry, credited through the deduplicating
replay, which takes everything the trace touches.

There are no epochs. Four separate measurements found epoch 2 contributing
exactly nothing, so the machinery is absent rather than ported.
"""

from __future__ import annotations

from .chain import (_attempts_for, _materialise, _program_writers,
                    _stage_stub, _stub_writers, _writers, local_solve,
                    producer_solve)
from .conformance_defaults import WORLDS, io_defaults
from .graph import execution_order, shortest_chain
from .interpreter import Interpreter

MAX_HOPS = 24            # route hops walked per goal; a route cap, not a depth cap
MAX_SET = 12             # satisfying values kept per requirement
MAX_DEMANDS = 3          # exact demands tried per requirement before offers
MAX_OFFER_RUNS = 160     # micro-executions per paragraph, cached and reused
OFFER_RESERVE = 0.25     # fraction of budget kept back for forward validation
MAX_REQUIREMENTS = 32    # requirements carried across a hop


# ---------------------------------------------------------------------------
# Requirement sets
# ---------------------------------------------------------------------------
def _norm(name) -> str:
    return str(name).upper()


def _same(a, b) -> bool:
    """Field equality the way the interpreter's padding makes it true."""
    if a is None or b is None:
        return a is b
    return str(a).rstrip() == str(b).rstrip()


def _satisfies(value, wanted) -> bool:
    return any(_same(value, want) for want in wanted)


def _canonical(value):
    """The same recipe with every mapping in sorted key order.

    Order is not cosmetic in a COBOL recipe: staged names that overlap in
    storage take effect in the order they are applied, so a plan and its
    sorted twin can be two different runs. The ledger stores sorted (that is
    what `_freeze` does), so the run has to be sorted too or the witness is
    not replayable - which is the whole promise of a witness.
    """
    if isinstance(value, dict):
        return {k: _canonical(value[k]) for k in sorted(value)}
    if isinstance(value, (list, tuple)):
        return [_canonical(v) for v in value]
    return value


def requirements_at_goal(index, prov, goal, budget, sweep_cache,
                         facts=(), pools=None) -> tuple:
    """``([(R, background, staged)], local_fired)`` for the goal's paragraph.

    One entry per local witness, kept apart. Merging them was measured as a
    defect: three candidates blended field-by-field is a background that is
    none of the three, and a state no run ever demonstrated.

    The direction is fired in isolation first - P plus its PERFORM closure run
    as a sub-program - and the requirement set is read off *what actually
    fired*: for every variable the shrunk assignments called essential, the
    satisfying set is the set of values that were observed to fire the goal
    across the whole sweep. Nothing is assumed to satisfy; membership is a
    measurement.
    """
    candidates, _runs = local_solve(index, prov, goal, budget, sweep_cache,
                                    facts=facts, pools=pools)
    if not candidates:
        return None, frozenset()


    fired_all: set = set()
    for _a, _s, _f, fired in candidates:
        fired_all |= set(fired)

    cached = sweep_cache.get(goal[0]) or {}
    # The satisfying set of a variable is every value that was *observed* to
    # fire the goal, pooled across the whole sweep. This is the one place the
    # walk is wider than the jump solver by construction: `chain` carried the
    # single byte its candidate happened to hold and refused any producer that
    # would not write exactly that.
    witnessed_values: dict = {}
    for state, _stubs, fired in cached.get("states", []):
        if goal not in fired:
            continue
        for name, value in (state or {}).items():
            bucket = witnessed_values.setdefault(_norm(name), [])
            if not any(_same(value, held) for held in bucket):
                bucket.append(value)

    # Requirements and background are different things and conflating them
    # breaks the walk in both directions, which was measured both ways:
    #
    # * carrying only the shrunk essential set diverged on every one of one
    #   program's 23 reachable goals - from entry the dropped pairs are
    #   background the route really reads, not slack the sub-program tolerated;
    # * promoting the whole witness state to requirements then refused 30 times
    #   at hops for bytes nobody wanted, because an evidence *complement* (the
    #   one value outside everything a field is tested against) is an arbitrary
    #   placeholder and demanding it of a producer is a demand for noise.
    #
    # So: the essential variables are the requirement set, carrying the
    # measured satisfying sets that shrinking actually buys, and are what the
    # hops reconcile. Everything else in the live witness state is background -
    # staged into the recipe at the top, never demanded of a producer, never a
    # source of refusal.
    out = []
    for assignment, stubs, full_state, _fired in candidates:
        essential = {_norm(n) for n in assignment}
        state = {_norm(n): v for n, v in (full_state or {}).items()}
        R = {}
        for name in sorted(essential):
            values = witnessed_values.get(name) or (
                [state[name]] if name in state else [])
            if values:
                R[name] = tuple(values[:MAX_SET])
        background = {name: value for name, value in state.items()
                      if name not in R}
        staged: dict = {}
        for key, entries in (stubs or {}).items():
            for entry in entries:
                staged.setdefault(key, {}).update(entry.get("set") or {})
        out.append((R, background, staged))
    return out, frozenset(fired_all)


# ---------------------------------------------------------------------------
# What a paragraph can emit: the offer table
# ---------------------------------------------------------------------------
class _Offers:
    """Per-paragraph achievable outputs, measured once and reused.

    The offer table is the walk's answer to an over-specific demand. `chain`
    asked a producer for one exact byte string and recorded `producer-
    unsolvable` when it would not write it; most of those refusals were the
    demand's fault, not the producer's. Here the producer is run over its own
    evidence sweep and every value it *did* write is kept, so the requirement
    can be met by intersection instead of by luck.
    """

    def __init__(self, index, prov, budget, pools=None):
        self.index = index
        self.prov = prov
        self.budget = budget
        # A walk that spends its whole budget measuring what paragraphs can
        # emit and none of it running the program from entry witnesses
        # nothing. Offers are the cheap half of the answer only while the
        # expensive half still has runs left.
        self.reserve = int(getattr(budget, "total", 0) * OFFER_RESERVE)
        self.pools = pools
        self._table: dict = {}
        self._written_cache: dict = {}

    def of(self, paragraph: str) -> dict:
        """``{variable: [(value, input_state, stub_plan)]}`` for one paragraph."""
        key = _norm(paragraph)
        if key in self._table:
            return self._table[key]
        if self.budget.left() <= self.reserve:
            return {}          # not cached: the refusal is the budget's, not
                               # this paragraph's, and must not become a fact
        table: dict = {}
        self._table[key] = table
        if key not in self.index.paragraphs:
            return table
        members = self.index.closure(key)
        sub = self.index.sub_program(members)
        runs = 0
        for state, staged in _attempts_for(self.index, self.prov, members,
                                           pools=self.pools):
            if runs >= MAX_OFFER_RUNS or self.budget.left() <= 0:
                break
            runs += 1
            self.budget.spend()
            try:
                interp = Interpreter(sub, dict(state), stubs=staged or None,
                                     defaults=io_defaults(self.index.program,
                                                          "populated"))
                interp.run(members[0])
            except Exception:                                # noqa: BLE001
                continue
            post = interp.state
            for name in self._written(members):
                try:
                    value = post.get(name)
                except Exception:                            # noqa: BLE001
                    continue
                if value is None:
                    continue
                bucket = table.setdefault(name, [])
                if len(bucket) >= MAX_SET:
                    continue
                if not any(_same(value, held) for held, _s, _t in bucket):
                    bucket.append((value, dict(state), staged))
        return table

    def _written(self, members) -> list:
        """Every variable some member of the closure writes.

        Resolved through `writes_to`, never through the raw `writers` dict:
        the same bytes arrive under two keys (the qualified reference and the
        declared name), and reading one half is what made a screen field's
        producer come back as a file READ instead of the RECEIVE that fills
        it. The alias fold is the whole reason that accessor exists.
        """
        key = tuple(sorted(_norm(m) for m in members))
        if key in self._written_cache:
            return self._written_cache[key]
        scope = set(key)
        out = sorted(name for name in (self.prov.writers or {})
                     if any(_norm(w.para) in scope
                            for w in _writers(self.prov, name)))
        self._written_cache[key] = out
        return out


def _writes_here(prov, scope, name) -> bool:
    return any(_norm(w.para) in scope for w in _writers(prov, name))


# ---------------------------------------------------------------------------
# The route
# ---------------------------------------------------------------------------
def route_to(graph, entry: str, target: str) -> list:
    """The paragraphs that run before ``target``, nearest hop first.

    `shortest_chain` answers with call sites; the walk wants the paragraphs
    standing between entry and the goal, ordered so the induction step is
    "move one hop upstream". The graph carries fall-through edges as well as
    PERFORM and GO TO, so this really is the execution route and not just the
    call tree - which is what makes a clobber by a sibling paragraph visible.
    """
    target = _norm(target)
    entry = _norm(entry)
    if target == entry:
        return []
    # Execution order, not call ancestry. "The paragraph that runs before P" is
    # not the same as "the paragraph that called P": a sibling PERFORMed by the
    # same parent one statement earlier runs before P and is not on its call
    # chain at all, and on this corpus that sibling is usually the writer that
    # matters. Measured with call ancestry alone the walk met 10 of one
    # program's 23 reachable goals, because the paragraph actually setting the
    # field was never a hop.
    order = execution_order(graph, entry)
    if target not in order:
        chain = shortest_chain(graph, entry, target)
        if chain is None:
            return []
        hops = []
        for site in chain:
            caller = _norm(site.caller)
            if caller not in hops:
                hops.append(caller)
        hops.reverse()
        return hops[:MAX_HOPS]
    cut = order[target]
    hops = sorted((name for name, position in order.items()
                   if position < cut), key=lambda n: -order[n])
    return hops[:MAX_HOPS]


# ---------------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------------
def walk(index, prov, graph, goal, budget, memo, offers, sweep_cache,
         facts=(), pools=None, cycle_fields=frozenset(), cycle_bases=(),
         reentry_bases=(), success_world=None, valid_screen=None) -> dict:
    """One goal in; a recipe set or a named refusal out.

    The loop below is the whole module. Everything before it initialises the
    requirement set at the goal, everything after it turns the surviving
    requirements into a recipe; in between, `while frontier is not entry` runs
    exactly once per hop and does the same three things at every one.
    """
    entry = index.names[0]
    starts, local_fired = requirements_at_goal(
        index, prov, goal, budget, sweep_cache, facts=facts, pools=pools)
    if starts is None:
        if budget.left() <= 0:
            return {"refusal": "budget-exhausted", "hops": []}
        return {"refusal": "local-unsolvable", "hops": []}

    goal_members = {_norm(m) for m in index.closure(goal[0])}
    hops = route_to(graph, entry, goal[0])
    recipes: list = []
    refusals: list = []
    position = 0

    for R, background, staged in starts:
        recipe, walked, hop_refusals = _walk_one(
            index, prov, goal, R, background, staged, hops, goal_members,
            budget, memo, offers, pools, cycle_fields, cycle_bases,
            reentry_bases, success_world, valid_screen)
        recipes.append(recipe)
        refusals.extend(hop_refusals)
        position = max(position, walked)

    return {"recipes": recipes, "local_fired": local_fired,
            "refusals": refusals, "hops_walked": position,
            "route_length": len(hops)}


def _walk_one(index, prov, goal, R, background, staged, hops, goal_members,
              budget, memo, offers, pools, cycle_fields, cycle_bases,
              reentry_bases, success_world, valid_screen) -> tuple:
    """The loop itself: one requirement set carried from the goal to entry."""
    stub_fields: dict = {}
    for key, fields in (staged or {}).items():
        stub_fields.setdefault(key, {}).update(fields)
    entry_pins: dict = {}
    refusals: list = []
    settled: dict = {}
    position = 0
    # Everything the frontier and the hops already met can do. A paragraph's
    # PERFORM closure runs *through* the frontier - MAIN-PARA's closure
    # contains the very paragraph the goal lives in - so asking the raw
    # closure what a hop writes reads the frontier's own writes back as an
    # upstream clobber. Measured: that alone produced 30 false clobbers on one
    # program and refused every goal on it. Upstream means strictly upstream.
    downstream = set(goal_members)
    for hop_index, Q in enumerate(hops):
        if budget.left() <= 0:
            refusals.append({"hop": hop_index, "paragraph": Q,
                             "variable": None, "reason": "cap",
                             "detail": "budget-exhausted"})
            break
        position = hop_index + 1
        if not R:
            break
        members = index.closure(Q)
        scope = {_norm(m) for m in members} - downstream
        downstream |= {_norm(m) for m in members}
        if not scope:
            continue                    # nothing here that is not downstream
        joined: dict = {}
        resolved: list = []
        for name, wanted in list(R.items()):
            if not _writes_here(prov, scope, name):
                continue                        # (b) pass through, untouched
            # (a) demand-driven first.
            landed = None
            for value in list(wanted)[:MAX_DEMANDS]:
                if budget.left() <= 0:
                    break
                answer, _n = producer_solve(index, prov, Q, {name: value},
                                            budget, memo, pools=pools)
                if answer is not None:
                    landed = (value, answer)
                    break
            if landed is None:
                # (a) offer-driven fallback: what CAN it emit?
                table = offers.of(Q)
                achievable = table.get(_norm(name), [])
                hit = None
                for value, state, _staged in achievable:
                    if _satisfies(value, wanted):
                        hit = (value, state)
                        break
                if hit is None:
                    kind = "clobber" if achievable else "empty-intersection"
                    refusals.append({
                        "hop": hop_index, "paragraph": Q,
                        "variable": name, "reason": kind,
                        "wanted": [repr(v)[:20] for v in list(wanted)[:4]],
                        "achievable": [repr(v)[:20]
                                       for v, _s, _t in achievable[:4]]})
                    continue
                landed = hit
            # (c) the precondition that achieved it joins R.
            _value, achieving = landed
            for var, val in (achieving or {}).items():
                key = _norm(var)
                if key in R:
                    continue
                bucket = joined.setdefault(key, [])
                if not any(_same(val, held) for held in bucket):
                    bucket.append(val)
            resolved.append(name)
        for name in resolved:
            # Resolved, but not forgotten. A requirement met by a producer is
            # met only if the route actually runs that producer; the walk
            # settles the value so the top still stages it, which costs one
            # pin and covers the case where control reaches the frontier by a
            # path the producer is not on.
            settled.setdefault(name, R[name][0])
            R.pop(name, None)
        for name, values in joined.items():
            if len(R) >= MAX_REQUIREMENTS:
                break
            R.setdefault(name, tuple(values[:MAX_SET]))

    # ---------------------------------------------------------------- at top
    # Requirements first, so a deliberately demanded byte wins over the
    # background it sits on; `_stage_stub` and `setdefault` are both
    # first-write-wins.
    for name, wanted in (list(R.items())
                        + [(n, (v,)) for n, v in settled.items()]
                        + [(n, (v,)) for n, v in background.items()]):
        value = wanted[0]
        writers = _program_writers(prov, name, exclude=goal_members)
        stubs = _stub_writers(prov, name)
        if stubs:
            _stage_stub(stub_fields, stubs[0], name, value)
            if writers:
                # Both a paragraph and an operation put bytes here. The
                # operation is what actually hands the value over on the route
                # that matters, and the pin is free insurance if the read
                # comes first.
                entry_pins.setdefault(_norm(name), value)
        else:
            entry_pins.setdefault(_norm(name), value)

    bases = [({}, world) for world in WORLDS]
    bases += [(dict(state), "populated") for _name, state in reentry_bases]
    cycle_needs = sorted(name for name in R
                         if name in cycle_fields
                         or name.split(" OF ")[0] in cycle_fields)
    if (cycle_needs or not R) and cycle_bases:
        # Prior-cycle state: the same loop, one cycle earlier. The program
        # writes these fields itself before RETURN TRANSID, so no entry pin
        # survives to them on a re-entered task; what does is a run whose
        # FIRST task earns the state. The background is the program-wide
        # all-valid screen, laid in *under* the requirement's own staging
        # (both are first-write-wins), so a deliberately demanded byte stays
        # and everything around it passes.
        #
        # MEASURED, and negative: offering the cycle bases to *every* goal
        # rather than only to goals whose requirements name commarea state
        # moved one program's gate from 40 to 41 of 81 while dropping total
        # credited directions from 493 to 365. The extra full-program runs
        # displaced cheaper ones that were crediting more. The gate is on
        # `cycle_needs` because that is where it pays.
        for world_map in (success_world or {}, valid_screen or {}):
            for op, fields in world_map.items():
                for field, value in fields.items():
                    stub_fields.setdefault(op, {}).setdefault(field, value)
        bases = list(cycle_bases) + bases

    return ({"pins": entry_pins, "stubs": _materialise(stub_fields),
             "bases": bases, "cycle_needs": cycle_needs},
            position, refusals)


# ---------------------------------------------------------------------------
# The driver: walk every goal, validate once from entry, account for it all
# ---------------------------------------------------------------------------
def run_walk(program, goals=None, budget=8000, baseline=None,
             facts_path=None, pools_path=None) -> dict:
    """Walk every goal once. No epochs.

    `chain.run_chain` re-solved the pending set up to three times, feeding each
    epoch the previous one's replay facts and divergence subgoals. Four
    separate measurements put epoch 2's contribution at exactly zero new
    witnesses, so there is one pass here and the machinery that would have
    supported a second is absent rather than disabled.

    Crediting is unchanged and deliberately generous: a run witnesses every
    direction its trace took, deduplicated by full recipe, and only ever
    through a fresh from-entry interpreter.
    """
    from .chain import (_Budget, _cycle_bases, _cycle_fields, _donate_values,
                        _load_facts, _pool_from_literals, _project, _save_facts,
                        _screen_variants, _success_world, _Index)
    from .coverage import branches_of
    from .graph import build_graph
    from .ladder import analyse
    from .ledger import Ledger, _freeze

    index = _Index(program)
    _graph_unused, prov = analyse(program)
    graph = build_graph(program)
    entry = index.names[0]
    ledger = Ledger()
    seen_runs: set = set()
    the_budget = _Budget(budget)
    facts = _load_facts(facts_path)
    pools: dict = {}
    if pools_path:
        import json as _json
        import os as _os
        if _os.path.exists(pools_path):
            try:
                pools = {str(k).upper(): list(v)[:12]
                         for k, v in _json.load(open(pools_path)).items()}
            except Exception:                                # noqa: BLE001
                pools = {}

    cycle_fields = _cycle_fields(program, index)
    cycle_bases = _cycle_bases(program, index)
    success_world = _success_world(index, prov)
    screen_variants = _screen_variants(index, prov)
    valid_screen = screen_variants[1] if len(screen_variants) > 1 \
        else (screen_variants[0] if screen_variants else {})

    para_vars_cache: dict = {}
    facts_seen = {para: {repr(sorted(fact.items())) for fact in rows}
                  for para, rows in facts.items()}
    fact_watch: set = set()

    def donate(entered, interp):
        """Fold a replay's own state back into the sweeps that follow.

        This is *not* an epoch. An epoch re-solves goals already answered, and
        four measurements put its yield at zero. This is the single pass
        learning as it goes: a from-entry replay - landed or diverged - is the
        only source of the bytes a program computes for itself, and a later
        goal's local sweep that cannot see them invents a one-variable state
        where the route needs thirty-five. Measured without it, one program's
        recipes carried a single pin against the jump solver's full screen and
        13 reachable directions diverged.
        """
        for paragraph in entered & fact_watch:
            fact = _project(index, interp.state, paragraph, para_vars_cache)
            if not fact:
                continue
            mark = repr(sorted(fact.items()))
            seen = facts_seen.setdefault(paragraph, set())
            if mark in seen:
                continue
            seen.add(mark)
            facts.setdefault(paragraph, []).append(fact)

    def run(state, world, stub_plan, terminals, source):
        # Canonical key order, applied to the *live* recipe and not just to the
        # stored one. `_freeze` sorts every mapping it touches, so a ledger
        # recipe is always replayed in sorted order - while the run that
        # earned it applied its fields in insertion order. That is a different
        # run whenever two staged names share bytes, which in COBOL is the
        # normal case: a group item and its children occupy the same storage
        # and the last write wins. Here the commarea's own fields, delivered
        # by one staged RETURN, landed in one order live and the other on
        # replay.
        #
        # Measured: one recipe of 84 was credited from a run the ledger could
        # not restate, and from-disk reproduction read 98.8% where the gate is
        # 100%. Canonicalising the state alone did not fix it - the stub
        # payloads are mappings too. Everything the recipe carries is ordered
        # here, so what is credited is exactly what was run.
        state = _canonical(state)
        stub_plan = _canonical(stub_plan)
        terminals = _canonical(terminals)
        key = (_freeze(state), world, _freeze(stub_plan or {}),
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
        except Exception:                                    # noqa: BLE001
            return None
        ledger.credit(trace, state or {}, world, stub_plan, terminals, source)
        donate(set(trace.entered), interp)
        _donate_values(pools, trace)
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
        reentry_bases, seen_names = [], set()
        for name, state in reentry_states(program, pool):
            mark = name.split(":filled")[0].split(":drawn")[0]
            if mark in seen_names:
                continue
            seen_names.add(mark)
            reentry_bases.append((name, state))
            if len(reentry_bases) >= 4:
                break
    except Exception:                                        # noqa: BLE001
        reentry_bases = []

    memo: dict = {}
    sweep_cache: dict = {}
    fact_watch.update(goal[0] for goal in original)

    offers = _OffersFactory(index, prov, the_budget, pools)

    # The degenerate case of the loop, run first: a walk whose requirement set
    # is empty has no hops to reconcile and arrives at the top immediately, so
    # `_walk_one` returns the pure at-top construction - the program's own
    # all-valid screen and success world over the cycle bases. That is exactly
    # what the old Phase 0 "cycle probe" built by hand, reached here as a case
    # of the walk rather than as a special beside it, and it earns its place
    # twice over: it credits every direction the pseudo-conversation takes, and
    # it is the only thing that seeds the value pools and paragraph facts
    # before the first goal's local sweep runs. Measured without it, the sweeps
    # invented one-variable states and the recipes carried one pin.
    if cycle_bases:
        opening, _walked, _refused = _walk_one(
            index, prov, (entry, 0, "IF", True), {}, {}, {}, [], set(),
            the_budget, memo, offers, pools, cycle_fields, cycle_bases,
            reentry_bases, success_world, valid_screen)
        for base_state, world in opening["bases"]:
            if the_budget.left() <= 0:
                break
            run(dict(base_state), world, opening["stubs"] or None, None,
                "walk:opening")
    outcomes: dict = {}
    refusal_log: list = []

    for goal in original:
        if the_budget.left() <= 0:
            outcomes.setdefault(goal, "budget-exhausted")
            continue
        if goal in ledger.witnesses:
            outcomes[goal] = "witnessed"
            continue
        answer = walk(index, prov, graph, goal, the_budget, memo, offers,
                      sweep_cache, facts=facts.get(goal[0], ()), pools=pools,
                      cycle_fields=cycle_fields, cycle_bases=cycle_bases,
                      reentry_bases=reentry_bases,
                      success_world=success_world, valid_screen=valid_screen)
        for record in answer.get("refusals", ()):
            record = dict(record)
            record["goal"] = "%s/%s/%s" % (goal[0], goal[1], goal[3])
            refusal_log.append(record)
        if "refusal" in answer:
            outcomes[goal] = answer["refusal"]
            continue
        landed = False
        for recipe in answer["recipes"]:
            for base_state, world in recipe["bases"]:
                if the_budget.left() <= 0:
                    break
                state = dict(base_state)
                state.update(recipe["pins"])
                run(state, world, recipe["stubs"] or None, None,
                    "walk:%s:%s:%s" % (goal[0], goal[1], goal[3]))
                if goal in ledger.witnesses:
                    landed = True
                    break
            if landed:
                break
        if landed:
            outcomes[goal] = "witnessed"
        elif answer.get("refusals"):
            outcomes[goal] = "hop-refused"
        else:
            outcomes[goal] = "validation-diverged"

    _save_facts(facts_path, facts)
    if pools_path:
        try:
            import json as _json
            with open(pools_path, "w") as handle:
                _json.dump(pools, handle, indent=1, default=str)
        except Exception:                                    # noqa: BLE001
            pass

    refusals: dict = {}
    for goal in original:
        outcome = outcomes.get(goal, "budget-exhausted")
        if outcome == "witnessed" or goal in ledger.witnesses:
            continue
        refusals[outcome] = refusals.get(outcome, 0) + 1
    taxonomy: dict = {}
    for record in refusal_log:
        taxonomy[record["reason"]] = taxonomy.get(record["reason"], 0) + 1
    witnessed = sum(1 for g in original if g in ledger.witnesses)
    return {"goals": len(original), "witnessed": witnessed,
            "credited_directions": len(ledger.witnesses),
            "runs": the_budget.spent, "budget": budget,
            "refusals": refusals, "hop_refusals": taxonomy,
            "refusal_log": refusal_log[:400], "ledger": ledger}


class _OffersFactory(_Offers):
    """`_Offers` under the name the driver builds it by."""
