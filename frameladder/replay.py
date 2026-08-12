"""One export a harness can replay without interpreting anything.

`Plan.stub_plan()` already carries ordered outcomes and `Plan.terminals` says
what happens once they run out, so the *data* for a replay has been there
since the beginning.  What was missing is a single document that hands the
whole series over, and - the part that actually costs coverage - one that
never drops a value quietly.

The failure this exists to prevent, measured on one harness integration: the
harness projects a plan down to what it supports, so a value it cannot inject
is removed and the run proceeds without it.  The plan still executes, still
reports a status, and means nothing.  Nothing in the plan, the interpreter or
the harness log says which value went missing, so the budget is spent before
anyone can know it was wasted.

Three rules follow, and they are the whole module:

**Position is meaning.**  The interpreter delivers entry *i* on call *i*
(`interpreter._external` takes the first undelivered matching entry and
returns), so an outcome's index in the list is which call it answers.  An
outcome whose every field the harness refuses is therefore kept in place,
holding an empty payload, rather than removed - removing it would shift every
later outcome onto an earlier call and change what the plan says without
changing what it claims.

**A refusal is output.**  Every field, outcome and variable the profile will
not carry comes back in `refusals`, phrased the way the harness phrases it.
`representable` is false whenever there is one.  The caller can widen the
profile or plan another route; what it can no longer do is find out afterwards.

**The terminal is part of the series.**  A mock that returns one fixed status
describes a file that never ends.  Where the plan derived no terminal that is
said out loud in `notes` rather than left for the reader to notice.
"""

from __future__ import annotations

from .capability import Capability, unrepresentable

SCHEMA = "frameladder.replay.v1"


def _cap(capability) -> Capability:
    return capability if isinstance(capability, Capability) else Capability()


def _ordered(entries) -> list:
    """Outcomes in delivery order.

    `seq` is the position within one *slot*, so two fields of the same
    operation both carry `seq` 0 and are two consecutive calls rather than one
    call setting both - which is what the interpreter does with them, and the
    plan was verified under the interpreter.  Sorting must therefore be stable
    and must not merge.
    """
    return sorted(list(entries or ()), key=lambda e: e.get("seq", 0))


def operation_series(op_key: str, entries, terminal=None,
                     capability=None) -> dict:
    """The full ordered series for one operation, with every refusal named.

    ``max_outcomes`` from the profile is a hard stop: a series longer than the
    harness can hold is truncated *and* reported, because a silently shortened
    read sequence ends the file early and every guard after the loop is then
    reached for the wrong reason.
    """
    cap = _cap(capability)
    key = (op_key or "").upper()
    ordered = _ordered(entries)
    refusals: list = []
    notes: list = []

    if not cap.can_replay(key):
        return {"op_key": key, "outcomes": [], "terminal": None,
                "replayable": False,
                "refusals": ["cannot replay %s" % key],
                "notes": ["%d outcome(s) and the terminal are unreachable "
                          "without it" % len(ordered)],
                "planned_outcomes": len(ordered), "conditional_outcomes": 0}

    limit = cap.outcome_limit(key)
    kept = ordered
    if limit and len(ordered) > limit:
        kept = ordered[:limit]
        refusals.append("%s accepts at most %d outcome(s), the series needs %d"
                        % (key, limit, len(ordered)))

    outcomes, conditional = [], 0
    for index, entry in enumerate(kept):
        fields: dict = {}
        for name, value in (entry.get("set") or {}).items():
            if cap.can_set(key, name):
                fields[str(name).upper()] = value
            else:
                refusals.append("%s cannot set %s" % (key, str(name).upper()))
        when = {str(k).upper(): v for k, v in (entry.get("when") or {}).items()}
        if when:
            conditional += 1
        outcomes.append({"call": index + 1, "seq": index, "when": when,
                         "set": fields,
                         "inferred": bool(entry.get("inferred"))})
    if conditional:
        # A discriminator is a condition on program state, and the profile has
        # no way to say whether the harness can evaluate one. It is therefore
        # counted rather than refused: a harness whose mock is a plain ordered
        # list per operation will deliver these in order and ignore the
        # condition, which is a divergence nobody would otherwise see.
        notes.append("%s: %d outcome(s) are conditional on program state; a "
                     "positional replay delivers them in order regardless"
                     % (key, conditional))
    if any(not o["set"] for o in outcomes):
        notes.append("%s: an outcome with no deliverable field is kept in "
                     "place so later outcomes stay on the call they were "
                     "planned for" % key)

    final = None
    if terminal:
        final = {}
        for name, value in terminal.items():
            if cap.can_set(key, name):
                final[str(name).upper()] = value
            else:
                refusals.append("%s cannot set %s (terminal)"
                                % (key, str(name).upper()))
    if outcomes and not final:
        notes.append("%s: no terminal, so after %d outcome(s) the operation "
                     "has no stated ending and a loop over it does not finish"
                     % (key, len(outcomes)))

    return {"op_key": key, "outcomes": outcomes, "terminal": final,
            "replayable": True, "refusals": refusals, "notes": notes,
            "planned_outcomes": len(ordered),
            "conditional_outcomes": conditional}


def replay_script(plan, capability=None, *, program=None, entry: str = "",
                  world: dict | None = None, io_world: str = "",
                  io_defaults: dict | None = None,
                  entry_state: dict | None = None) -> dict:
    """Everything one test needs, and every reason it cannot be run.

    ``world`` accepts a sequence world from :mod:`frameladder.sequences` -
    "this operation fails on its second call and succeeds either side" is an
    outcome list and there is no other way to say it - and replaces the plan's
    own operation series with it.

    ``io_world`` and ``io_defaults`` say what the *unplanned* operations do:
    the plan pins the ones its obligations reached and every other one takes
    whatever the environment gives it. Leaving that implicit is the same class
    of silent loss this module exists to stop - a plan verified with the files
    present, replayed with them absent, abends at its first OPEN and reports
    covering nothing. ``entry_state`` likewise replaces the plan's own state
    when a free-slot overlay is what took the direction, so what is exported
    is the state that was actually run.
    """
    cap = _cap(capability)
    stubs = dict((world or {}).get("stubs") or plan.stub_plan())
    terminals = dict((world or {}).get("terminals") or plan.terminals or {})

    inputs, refused_inputs = {}, []
    for name, value in (entry_state if entry_state is not None
                        else plan.input_state()).items():
        if cap.can_inject(name):
            inputs[name] = value
        else:
            refused_inputs.append({"variable": name, "value": value,
                                   "why": "cannot inject %s" % name})

    operations = [operation_series(key, stubs.get(key), terminals.get(key), cap)
                  for key in sorted(stubs)]
    # A terminal for an operation with no planned outcome is still part of the
    # world - a file that is empty from the first call - and dropping it here
    # would be the same silent loss this module exists to stop.
    for key in sorted(set(terminals) - set(stubs)):
        operations.append(operation_series(key, (), terminals[key], cap))

    # The environment behind the operations the plan did not pin. Refused the
    # same way an outcome is: a harness that cannot drive an operation cannot
    # put it in this world either, and it should be told rather than left to
    # discover it.
    environment, refused_env = {}, []
    for key, values in sorted((io_defaults or {}).items()):
        if cap.can_replay(key):
            environment[key] = dict(values)
        else:
            refused_env.append("cannot replay %s, so the %s world cannot be "
                               "set up for it" % (key, io_world or "chosen"))

    reasons = list(unrepresentable(plan, cap))
    for reason in refused_env:
        if reason not in reasons:
            reasons.append(reason)
    for entry_ in refused_inputs:
        if entry_["why"] not in reasons:
            reasons.append(entry_["why"])
    for op in operations:
        for reason in op["refusals"]:
            if reason not in reasons:
                reasons.append(reason)

    notes: list = []
    for op in operations:
        for note in op["notes"]:
            if note not in notes:
                notes.append(note)
    if plan.open_obligations:
        notes.append("%d obligation(s) the planner could not settle; the case "
                     "is a lead, not a test" % len(plan.open_obligations))

    return {
        "schema": SCHEMA,
        "program": getattr(program, "name", program) or "",
        "target": plan.target,
        "entry": (entry or (plan.chain[0] if plan.chain else "")).upper(),
        "world": (world or {}).get("name", ""),
        "io_world": io_world,
        "io_defaults": environment,
        "overlaid": entry_state is not None,
        "solved": plan.solved,
        "representable": not reasons,
        "reasons": reasons,
        "input_state": inputs,
        "refused_inputs": refused_inputs,
        "conditional_outcomes": sum(op["conditional_outcomes"]
                                    for op in operations),
        "operations": [{k: v for k, v in op.items() if k != "notes"}
                       for op in operations],
        "notes": notes,
    }
