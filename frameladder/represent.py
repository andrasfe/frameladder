"""Which plans a harness could actually run, and why the rest could not.

A plan is derived against this repository's own interpreter, where every
variable is settable and every operation is replayable.  A real harness is
narrower, and the expensive part is that the narrowing is silent: the value it
cannot inject is dropped in projection, the run proceeds, and the case reports
a status that means nothing.

So this module answers one question for a whole program at once - *of the
plans the tool would emit, how many can be replayed, and for the rest, what
exactly is in the way* - in the harness's own vocabulary, so an answer is
either a profile to widen or a route to avoid.

## The profile is a proxy here, and that is a limitation, not a detail

`Capability` is meant to be *stated* by the harness.  Nothing states one yet,
so `proxy_profile` constructs one from the source using the rule a real
harness uses, transcribed:

* **a variable is injectable when the program compares it against a literal,
  or it has an 88-level with a VALUE.**  That is the load-bearing half of
  Specter's `_is_safe_to_inject` (`has_signal = bool(dom.condition_literals or
  dom.valid_88_values)`), and it is evidence about this source rather than a
  guess about the name.
* **an operation is replayable when the source puts one of its outputs in a
  status channel, and it can set exactly those status fields.**  A mock record
  in that harness carries an operation key and a status, so a record *payload*
  is not something it can hand back.  Which fields are status fields comes
  from `faults.channel_of`, which reads the `FILE STATUS IS` clause, the
  `RESP` operand and `SQLCODE` - never a name.

What this does **not** prove, stated plainly:

1. It is not the harness's answer.  A real profile will differ in both
   directions, and every number below moves with it.
2. Specter's real rule has clauses this deliberately omits - it excludes
   stub-set variables unless their *name* contains RETURN/STATUS/RC and
   admits alphanumeric inputs with no literals at all.  Both decide from a
   name, which this repository does not do, so copying them would make the
   proxy less honest rather than more faithful.
3. Injectability here is a property of the variable, not of the variable *at
   the entry state*: a field the harness can set at the start is not
   necessarily one it can still control at the moment the target reads it.
   Every figure is therefore an upper bound on what would really replay.
4. `uncovered_directions` is empty in the proxy, because inventing a coverage
   state would be fabrication.  The work-list narrowing that a real profile
   enables is exercised by unit tests and is not measured here.
5. A program in which *no* operation has a status channel gets no operation
   table at all - the section is *omitted*, not emptied.  The contract
   distinguishes the two: an absent section states no constraint, an empty one
   states the harness can replay nothing.  The proxy has nothing to say about
   such a program, which is the first of those and not the second, so its
   figures there are an over-estimate.  Saying "nothing works" would be a
   claim the proxy has not earned.  Which programs those are is countable,
   and counted.
"""

from __future__ import annotations

from .capability import Capability, Operation, unrepresentable
from .ir import base_name

PROXY_CAVEAT = (
    "synthetic profile: injectable = compared against a literal or carries an "
    "88-level VALUE; replayable = the source puts one of the operation's "
    "outputs in a status channel, and only those status fields can be set. "
    "This is a proxy for a harness that has not stated its capabilities, an "
    "upper bound on what would really replay, and not a measurement of any "
    "harness."
)

# What the operation is allowed to hand back.
STATUS_FIELDS = "status"       # the status channel only, as a mock record is
DECLARED_OUTPUTS = "outputs"   # everything the source records it as writing


def stub_outputs_by_operation(prov) -> dict:
    """``op key -> {variables the source records that operation as writing}``.

    Read off the writer index rather than re-parsing the statements, so it
    agrees by construction with the producer walk the ladder binds through.
    """
    out: dict = {}
    for var, writers in prov.writers.items():
        for w in writers:
            if w.kind == "STUB" and w.op_key:
                out.setdefault(w.op_key.upper(), set()).add(var.upper())
    return out


def injectable_variables(program, prov) -> set:
    """Every field the program itself gives a value to compare against.

    Both halves of the rule are evidence: a literal in a condition is the
    program naming a value it distinguishes, and an 88-level VALUE is the
    program naming one in the data division.
    """
    out = {base_name(name) for name, values in prov.literals.items() if values}
    for _name, (parent, values) in program.model.condition_names.items():
        if values:
            out.add(base_name(parent))
    return {n for n in out if n}


def proxy_profile(program, prov=None, *, fields: str = STATUS_FIELDS,
                  max_outcomes: int = 0) -> Capability:
    """A capability profile derived from the source. See the module docstring.

    ``fields`` picks how much an operation is assumed to be able to hand back:
    `STATUS_FIELDS` models a mock record carrying a status, `DECLARED_OUTPUTS`
    models one that can also fill a record area. The two bracket the answer,
    which is why both are measurable rather than one being hard-coded.
    """
    from .faults import channel_of
    from .ladder import analyse

    if prov is None:
        _graph, prov = analyse(program)

    operations: dict = {}
    for key, variables in stub_outputs_by_operation(prov).items():
        if fields == DECLARED_OUTPUTS:
            settable = set(variables)
        else:
            settable = {v for v in variables
                        if channel_of(v, program.model, key) is not None}
        if not settable:
            # Nothing about the outcome is under the harness's control, so it
            # is not an operation it can replay. Registering it with an empty
            # field set would mean the opposite - `Operation.accepts` reads an
            # empty set as "any field" - and would quietly turn the strictest
            # case into the most permissive one.
            continue
        operations[key] = Operation(key, frozenset(settable), max_outcomes)

    return Capability(program=program.name,
                      injectable=frozenset(injectable_variables(program, prov)),
                      # Omitted rather than emptied when the proxy found
                      # nothing: see note 5 in the module docstring.
                      operations=operations or None,
                      stated=True)


# --------------------------------------------------------------------------
# the report
# --------------------------------------------------------------------------

def category_of(reason: str) -> str:
    """The harness's own words, bucketed for counting."""
    if reason.startswith("cannot inject"):
        return "cannot inject a variable"
    if reason.startswith("cannot replay"):
        return "cannot replay an operation"
    if "accepts at most" in reason:
        return "outcome series too long"
    if "cannot set" in reason:
        return "operation cannot set that field"
    return "other"


def capability_needed(reason: str) -> str:
    """The unit of harness work a refusal names.

    A refusal sentence is built for a human; a work list needs the *thing to
    build*. "cannot replay READ:F (needed to set CUST-ID)" and "READ:F cannot
    set CUST-ID" both mention one operation and one field, but the first is a
    missing mock and the second is a missing field on a mock that exists.
    The sentences come from `capability.unrepresentable`, so this reads them
    back rather than re-deriving anything.
    """
    from .capability import refusal_kind
    kind = refusal_kind(reason)
    if kind == "unsupported_operation":
        return "replay %s" % reason[len("cannot replay "):].split(" (needed")[0]
    if kind == "unsupported_output_field" and " cannot set " in reason:
        op, var = reason.split(" cannot set ", 1)
        return "%s must set %s" % (op, var)
    if kind == "unrepresentable_input" and reason.startswith("cannot inject "):
        return "inject %s" % reason[len("cannot inject "):]
    return reason


def unlock(rows, limit: int = 8) -> dict:
    """Fewest capability additions that make the most refused plans replayable.

    The dual of the refusal report. A refused plan needs *every* one of its
    reasons cleared, so this is a maximum-coverage problem over the reason
    sets and not a count of the commonest reason - the two disagree, because
    the commonest reason is usually one of several a plan is waiting on, and
    widening it alone unlocks nothing. Greedy, which is within 1-1/e of
    optimal on maximum coverage, and the curve is the actionable part anyway:
    the useful sentence for a harness team is "these three and N plans become
    replayable", which needs the marginal figures rather than the ranking.

    Reports what a *widening* would be worth. It cannot promise the plan then
    passes, because a capability the planner no longer has to route around may
    let it choose a different route entirely - so the count is what stops
    being refused, which is the number the widening is responsible for.
    """
    blocked = [(r["target"], frozenset(capability_needed(x)
                                       for x in r.get("reasons") or ()))
               for r in rows if not r.get("representable")]
    blocked = [(t, needs) for t, needs in blocked if needs]

    granted: set = set()
    curve: list = []
    candidates = {c for _t, needs in blocked for c in needs}
    unlocked: set = set()
    for _step in range(max(0, limit)):
        best, gain = None, 0
        for cand in sorted(candidates - granted):
            trial = granted | {cand}
            marginal = sum(1 for t, needs in blocked
                           if t not in unlocked and needs <= trial)
            if marginal > gain:
                best, gain = cand, marginal
        if best is None:
            # Greedy stalls as soon as every remaining plan needs two or more
            # additions at once, which is the common case and not a failure:
            # the next thing to build is then the one the most plans are
            # waiting on, even though on its own it unlocks none of them.
            frequency: dict = {}
            for t, needs in blocked:
                if t in unlocked:
                    continue
                for cand in needs - granted:
                    frequency[cand] = frequency.get(cand, 0) + 1
            if not frequency:
                break
            best = max(sorted(frequency), key=lambda c: frequency[c])
            gain = 0
        granted.add(best)
        unlocked = {t for t, needs in blocked if needs <= granted}
        curve.append({"capability": best, "unlocks": gain,
                      "cumulative": len(unlocked)})

    sizes = sorted(len(needs) for _t, needs in blocked)
    return {
        "blocked": len(blocked),
        "unlocked": len(unlocked),
        "additions": curve,
        # How many capabilities a blocked plan is waiting on. A median above
        # one is the reason the ranking and the cover disagree.
        "needs_median": sizes[len(sizes) // 2] if sizes else 0,
        "needs_max": sizes[-1] if sizes else 0,
    }


def classify(program, capability, *, entry: str | None = None,
             profile_aware: bool = False, targets=None,
             max_routes: int = 4, measure_precheck: bool = False) -> dict:
    """Every plan the tool would emit, classified representable or not.

    The denominator is reported twice on purpose. `emitted` is every target
    with a call chain, which is what a sweep hands to a harness; `solved` is
    the subset with no open obligation, which is what "internally valid plan"
    means and the figure comparable to a harness integration's own count.
    """
    from .graph import shortest_chain
    from .ladder import analyse, build_plan, plan_representable, precheck
    from .replay import replay_script

    graph, _prov = analyse(program)
    entry = (entry or program.paragraph_names[0]).upper()
    names = list(targets or program.paragraph_names)

    rows, no_chain = [], []
    for name in names:
        name = name.upper()
        if name == entry:
            continue
        if shortest_chain(graph, entry, name) is None:
            no_chain.append(name)
            continue
        refused_early = (precheck(program, name, capability, entry=entry)
                         if measure_precheck else [])
        if profile_aware:
            plan = plan_representable(program, name, capability=capability,
                                      entry=entry, max_routes=max_routes)
        else:
            plan = build_plan(program, name, entry=entry)
        if not plan.chain and plan.open_obligations:
            # A route every option refused. It is still a plan the tool was
            # asked for, and its refusal is the answer.
            reasons = [why for _atom, why in plan.open_obligations]
            rows.append({"target": name, "solved": False,
                         "representable": False, "reasons": reasons,
                         "refused_before_solving": bool(refused_early),
                         "bindings": 0, "operations": 0})
            continue
        script = replay_script(plan, capability, program=program, entry=entry)
        rows.append({
            "target": name,
            "solved": plan.solved,
            "representable": script["representable"],
            "reasons": script["reasons"],
            "refused_before_solving": bool(refused_early),
            "bindings": len(plan.bindings),
            "operations": len(script["operations"]),
            "conditional_outcomes": script["conditional_outcomes"],
        })

    emitted = rows
    solved = [r for r in rows if r["solved"]]

    def share(subset) -> dict:
        bad = [r for r in subset if not r["representable"]]
        return {"plans": len(subset), "representable": len(subset) - len(bad),
                "unrepresentable": len(bad),
                "pct": round(100.0 * len(bad) / len(subset), 1) if subset else 0.0}

    counts: dict = {}
    for row in rows:
        for reason in row["reasons"]:
            key = category_of(reason)
            counts[key] = counts.get(key, 0) + 1

    # A precheck that refuses a route the full solve would have found
    # representable is a false refusal, and a filter that produces them cannot
    # be allowed to decide what gets tested. Counted rather than trusted -
    # and only where the count means anything: in profile-aware mode the
    # refused routes were never solved, so every one of them would score as a
    # true refusal by construction.
    false_refusals = (None if profile_aware else
                      [r["target"] for r in rows
                       if r["refused_before_solving"] and r["representable"]])

    return {
        "program": program.name,
        "entry": entry,
        "profile_aware": bool(profile_aware),
        "no_chain": len(no_chain),
        "emitted": share(emitted),
        "solved": share(solved),
        # The number a harness integration actually spends its budget on: a
        # plan that is both internally valid and replayable. It is the only
        # figure comparable across the two planning modes, because refusing a
        # route makes a plan unsolved and so changes the `solved` denominator.
        "runnable": sum(1 for r in rows
                        if r["solved"] and r["representable"]),
        # An outcome selected by a discriminator is one the profile cannot
        # speak about at all: `Capability` has no field for "can the harness
        # match on program state". A harness whose mock is a plain ordered
        # list will deliver it anyway and ignore the condition, so these are
        # counted where the contract cannot refuse them.
        "plans_with_conditional_outcomes": sum(
            1 for r in rows if r.get("conditional_outcomes")),
        "reason_categories": dict(sorted(counts.items(),
                                         key=lambda kv: (-kv[1], kv[0]))),
        "precheck_refusals": sum(1 for r in rows if r["refused_before_solving"]),
        "precheck_false_refusals": false_refusals,
        "rows": rows,
    }
