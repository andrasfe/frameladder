"""Every direction a run demonstrably took, credited as a witness.

The export path scores a run by one bit: did it take the single direction it
was built for. Measured over 3,288 corpus runs, the runs that produced 926
witnesses had already *covered* 1,971 directions between them - each covered
direction taken, in a real run, from a recorded entry state under a recorded
world. On the program most like a stuck estate the witness rate said 1.5%
while the same runs' traces said 69.2%.

A witness is not "the plan worked". A witness is a replayable recipe - entry
state, I/O world, stub outcomes, terminals - that demonstrably takes one
branch direction. Every run is such a recipe for *every* direction its trace
took. This module is the bookkeeping that stops those from being thrown away:
`credit()` folds a trace into a ledger keyed by direction, keeping the first
recipe that took each one.

First, not best: a deliberate choice. Runs arrive cheapest-first (the plan's
own state under `bare` before overlays before staged worlds), so the first
recipe is the one demanding the least of a harness. Replacing it with a later
"better" one would demand more staging for the same fact.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field

# The interpreter names loops by the verb; `branches_of` names them by what
# they are. Same join `coverage._KIND` makes.
_KIND = {"PERFORM_UNTIL": "LOOP", "PERFORM_VARYING": "LOOP",
         "PERFORM_TIMES": "LOOP"}


@dataclass(frozen=True)
class Recipe:
    """One replayable run: everything a harness needs to reproduce it."""

    input_state: tuple            # sorted (name, value) pairs
    world: str
    stubs: tuple = ()             # stub_plan, frozen
    terminals: tuple = ()
    source: str = ""              # which mechanism produced the run

    def payload(self) -> dict:
        return {"input_state": dict(self.input_state), "world": self.world,
                "stubs": _thaw(self.stubs), "terminals": _thaw(self.terminals),
                "source": self.source}


def _freeze(value):
    if isinstance(value, dict):
        return tuple(sorted((k, _freeze(v)) for k, v in value.items()))
    if isinstance(value, (list, tuple)):
        return tuple(_freeze(v) for v in value)
    return value


def _thaw(value):
    if isinstance(value, tuple) and value and all(
            isinstance(x, tuple) and len(x) == 2 and isinstance(x[0], str)
            for x in value):
        return {k: _thaw(v) for k, v in value}
    if isinstance(value, tuple):
        return [_thaw(v) for v in value]
    return value


@dataclass
class Ledger:
    """direction key -> the first recipe that took it."""

    witnesses: dict = field(default_factory=dict)
    runs: int = 0

    def credit(self, trace, state: dict, world: str, stubs: dict | None,
               terminals: dict | None, source: str) -> int:
        """Fold one run in. Returns how many directions it newly witnessed."""
        self.runs += 1
        recipe = None
        fresh = 0
        for event in trace.guards:
            key = (event.paragraph, event.ordinal,
                   _KIND.get(event.kind, event.kind), bool(event.result))
            if key in self.witnesses:
                continue
            if recipe is None:
                recipe = Recipe(_freeze(state or {}), world,
                                _freeze(stubs or {}), _freeze(terminals or {}),
                                source)
            self.witnesses[key] = recipe
            fresh += 1
        return fresh

    def covered(self) -> set:
        return set(self.witnesses)

    def coverage(self, total_directions: int) -> float:
        return 100.0 * len(self.witnesses) / max(1, total_directions)

    def write(self, path: str, program_name: str = "") -> int:
        """One JSON line per witnessed direction, harness-shaped."""
        with open(path, "w") as fh:
            for key in sorted(self.witnesses):
                paragraph, ordinal, kind, direction = key
                row = {"program": program_name, "paragraph": paragraph,
                       "ordinal": ordinal, "kind": kind,
                       "direction": direction}
                row.update(self.witnesses[key].payload())
                fh.write(json.dumps(row, default=str) + "\n")
        return len(self.witnesses)


def missing(program, ledger: Ledger) -> list:
    """Directions with no witness yet - the work list, most important first.

    Sorted so a residual report reads usefully: whole decisions neither way
    first, then single missing directions.
    """
    from .coverage import branches_of
    have = ledger.covered()
    out = []
    for branch in branches_of(program):
        for direction in (True, False):
            key = (branch.paragraph, branch.ordinal, branch.kind,
                   direction)
            if key not in have:
                out.append((branch, direction))
    both = {b.key for b, _d in out}
    return sorted(out, key=lambda item: (item[0].key not in both,
                                         item[0].paragraph, item[0].ordinal))
