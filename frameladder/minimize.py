"""Shrink a witness recipe to its essential support.

A recipe pins every key its derivation happened to touch, not every key its
witnessed directions actually need - measured at a mean of 43 entry-state
keys per recipe on COCRDUPC, of which a mean of 1.5 mattered. That is the
"first, not best" trade `ledger.Ledger.credit` makes: the cheapest recipe
that took a direction, kept as-is. This module is the deferred second pass
`ledger`'s own docstring promises - "the recipe demanding the least of a
harness" - a one-pass delta-debug over `input_state`, then stub op-keys, then
terminals: drop a key, replay from the entry point with a fresh interpreter,
keep the drop iff every direction the recipe is credited with (`owns`) is
still taken. No new coverage is ever produced; a coverage change here is a
bug, not a feature.

CAUTION: judging "did the replay still take it" must use the *same* key join
`Ledger.credit` uses - same paragraph/ordinal/kind/result tuple, same
LOOP-kind folding table. `lift.direction_key` folds loop kinds through a
*different* table (missing PERFORM_TIMES), so borrowing it here would
silently misjudge a PERFORM_TIMES guard's replay as a miss-and-keep-anyway or
a hit-when-it-wasn't - the exact "0% dropped" trap that has already bitten
one probe. `taken_directions` below reuses `ledger._KIND`, not `lift`'s.
"""

from __future__ import annotations

from .interpreter import Interpreter
from .ledger import _KIND, Recipe, _freeze, _thaw


def taken_directions(trace) -> set:
    """The direction-key set a trace demonstrates, joined exactly as
    `Ledger.credit` joins it - the oracle every drop decision is judged by."""
    return {(g.paragraph, g.ordinal, _KIND.get(g.kind, g.kind), bool(g.result))
            for g in trace.guards}


def minimize(program, entry: str, recipe: Recipe, owns: set, defaults_for,
             *, budget: int | None = None, stats: dict | None = None) -> Recipe:
    """Return a recipe no larger than `recipe` that still takes every
    direction in `owns`.

    `stats["runs"]` (a fresh dict if none is passed) accumulates the
    interpreter-run count; callers minimizing many recipes under one shared
    run budget pass the same `stats` dict and the same `budget` to each call
    so the cap applies across the whole batch, not per recipe.
    """
    if stats is None:
        stats = {"runs": 0}
    owns = set(owns)

    def exhausted() -> bool:
        return budget is not None and stats["runs"] >= budget

    def still_taken(input_state: dict, stubs: dict, terminals: dict) -> bool:
        stats["runs"] += 1
        try:
            interp = Interpreter(program, dict(input_state), stubs=stubs,
                                 terminals=terminals,
                                 defaults=defaults_for(recipe.world))
            trace = interp.run(entry)
        except Exception:                                    # noqa: BLE001
            return False
        return owns <= taken_directions(trace)

    input_state = dict(recipe.input_state)
    stubs = _thaw(recipe.stubs) or {}
    terminals = _thaw(recipe.terminals) or {}

    # Sorted so the pass is deterministic - same drop order on every run,
    # same minimized recipe out, independent of dict iteration history.
    for key in sorted(input_state):
        if exhausted():
            break
        trial = {k: v for k, v in input_state.items() if k != key}
        if still_taken(trial, stubs, terminals):
            input_state = trial

    for key in sorted(stubs):
        if exhausted():
            break
        trial = {k: v for k, v in stubs.items() if k != key}
        if still_taken(input_state, trial, terminals):
            stubs = trial

    for key in sorted(terminals):
        if exhausted():
            break
        trial = {k: v for k, v in terminals.items() if k != key}
        if still_taken(input_state, stubs, trial):
            terminals = trial

    return Recipe(_freeze(input_state), recipe.world, _freeze(stubs),
                  _freeze(terminals), recipe.source)
