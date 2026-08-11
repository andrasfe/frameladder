"""What the harness that will run these plans can actually do.

`frameladder` derives a plan against its own interpreter, where every variable
is settable and every operation is replayable. A real harness is narrower:
Specter can inject a particular set of entry variables and replay a particular
set of mock operations, and it *projects a plan down to what it supports* -
silently dropping the rest. A plan that depended on a dropped value still
runs; it just no longer means anything, and the failure surfaces as "reached
COBOL and covered nothing" long after the budget was spent.

Measured on one integration: of 45 internally valid plans, 35 could not be
represented, 4 reached COBOL, 3 succeeded, and all 3 landed on branches that
were already covered. Almost the entire budget went to work that could not
pay, and none of it was knowable from inside the interpreter.

So the harness states its capabilities up front and the planner treats them
as a constraint, not as a filter applied afterwards. Three consequences, in
increasing order of how much they save:

* a binding on a variable the harness cannot inject makes the plan
  unrepresentable, and saying so before solving costs nothing;
* the work list is the harness's *uncovered directions*, so a plan that
  succeeds cannot land on covered code;
* a failed attempt comes back with the frames the real program reached, and
  the first missing one is a better place to plan from than the entry.

The profile is evidence in exactly the sense the rest of this repository
means it: a variable is injectable because the harness says it is, never
because of how it is named.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field

SCHEMA_VERSION = "1.0"


@dataclass(frozen=True)
class Operation:
    """A mock the harness can replay, and how far it can be driven."""

    op_key: str
    fields: frozenset = frozenset()      # payload fields it can set, empty = any
    max_outcomes: int = 0                # 0 = no stated limit

    def accepts(self, name: str) -> bool:
        return not self.fields or name.upper() in self.fields


@dataclass(frozen=True)
class Direction:
    """One branch direction the harness still has not covered."""

    paragraph: str
    ordinal: int
    kind: str
    direction: bool

    @property
    def key(self) -> tuple:
        return (self.paragraph.upper(), self.ordinal, self.kind.upper(),
                bool(self.direction))


@dataclass(frozen=True)
class Attempt:
    """What actually happened when the harness ran a plan.

    `first_missing_frame` is the useful part: the real program got as far as
    the frame before it, so that frame is a state the harness can reproduce
    and a much better place to plan from than the entry paragraph.
    """

    target: str = ""
    reached_frames: tuple = ()
    first_missing_frame: str = ""
    note: str = ""


@dataclass
class Capability:
    program: str = ""
    # `None` means the section was absent, which states no constraint. An
    # empty collection means the harness stated it can do none of these -
    # a different claim, and one worth honouring, or a profile can never
    # express "I cannot inject anything, plan around it".
    injectable: frozenset | None = None
    operations: dict | None = None                      # op_key -> Operation
    uncovered: tuple = ()                               # Direction
    attempts: tuple = ()                                # Attempt
    # An empty profile must not silently forbid everything: a caller that
    # supplies no capabilities is saying "no constraints stated", which is
    # the behaviour every existing command already has.
    stated: bool = False

    # -- the questions the planner asks ------------------------------------
    def can_inject(self, name: str) -> bool:
        if not self.stated or self.injectable is None:
            return True
        return _base(name) in self.injectable

    def can_replay(self, op_key: str) -> bool:
        if not self.stated or self.operations is None:
            return True
        return (op_key or "").upper() in self.operations

    def can_set(self, op_key: str, name: str) -> bool:
        if not self.stated or self.operations is None:
            return True
        op = self.operations.get((op_key or "").upper())
        return bool(op) and op.accepts(_base(name))

    def outcome_limit(self, op_key: str) -> int:
        op = (self.operations or {}).get((op_key or "").upper())
        return op.max_outcomes if op else 0

    @property
    def wanted(self) -> set:
        return {d.key for d in self.uncovered}

    def resume_points(self) -> list:
        """Frames a previous attempt reached, best first.

        Ordered by how often the harness got there, because a frame reached
        repeatedly is one it can reproduce reliably.
        """
        counts: dict = {}
        for attempt in self.attempts:
            for frame in attempt.reached_frames:
                counts[frame.upper()] = counts.get(frame.upper(), 0) + 1
        return [name for name, _n in sorted(counts.items(),
                                            key=lambda kv: (-kv[1], kv[0]))]


def _base(name: str) -> str:
    from .ir import base_name
    return base_name(name or "")


def load(path_or_dict) -> Capability:
    """Read a capability profile, or an empty one for "nothing stated".

    Unknown keys are ignored rather than rejected: the harness is a separate
    program on its own release cycle, and a profile that mentions something
    this version does not understand is not an error - it is a newer harness
    talking to an older planner, which should degrade rather than refuse.
    """
    if path_or_dict is None:
        return Capability()
    if isinstance(path_or_dict, (str, bytes)):
        with open(path_or_dict, "r", errors="replace") as fh:
            raw = json.load(fh)
    else:
        raw = dict(path_or_dict or {})
    if not raw:
        return Capability()

    version = str(raw.get("schema_version", SCHEMA_VERSION))
    if version.split(".")[0] != SCHEMA_VERSION.split(".")[0]:
        raise ValueError("capability profile major version %s is not %s"
                         % (version, SCHEMA_VERSION))

    operations = None
    if raw.get("replayable_operations") is not None:
        operations = {}
    for entry in raw.get("replayable_operations") or ():
        if isinstance(entry, str):
            operations[entry.upper()] = Operation(entry.upper())
            continue
        key = str(entry.get("op_key", "")).upper()
        if not key:
            continue
        operations[key] = Operation(
            key,
            frozenset(str(f).upper() for f in entry.get("fields") or ()),
            int(entry.get("max_outcomes") or 0))

    uncovered = tuple(
        Direction(str(d.get("paragraph", "")).upper(),
                  int(d.get("ordinal", -1)),
                  str(d.get("kind", "IF")).upper(),
                  bool(d.get("direction", True)))
        for d in raw.get("uncovered_directions") or ()
        if isinstance(d, dict))

    attempts = tuple(
        Attempt(str(a.get("target", "")),
                tuple(str(f).upper() for f in a.get("reached_frames") or ()),
                str(a.get("first_missing_frame", "")).upper(),
                str(a.get("note", "")))
        for a in raw.get("attempts") or ()
        if isinstance(a, dict))

    return Capability(
        program=str(raw.get("program", "")),
        injectable=(None if raw.get("injectable_variables") is None
                    else frozenset(_base(v) for v in
                                   raw["injectable_variables"])),
        operations=operations,
        uncovered=uncovered,
        attempts=attempts,
        stated=True)


def unrepresentable(plan, capability: Capability) -> list:
    """Why this plan cannot be replayed by the harness, in its own terms.

    Empty means it can. The reasons name the binding and the capability it
    needs, so the harness can either widen the capability or the planner can
    pick a different route - both are better than the value being dropped in
    projection and the plan failing for no stated reason.
    """
    if not capability.stated:
        return []
    out: list = []
    for binding in getattr(plan, "bindings", ()) or ():
        producer = getattr(binding, "producer", None)
        if producer is None:
            continue
        kind = getattr(producer, "kind", "")
        var = getattr(producer, "var", "") or ""
        op_key = getattr(producer, "op_key", "") or ""
        if kind == "stub":
            if not capability.can_replay(op_key):
                out.append("cannot replay %s (needed to set %s)"
                           % (op_key or "an external operation", var))
            elif var and not capability.can_set(op_key, var):
                out.append("%s cannot set %s" % (op_key, var))
        elif var and not capability.can_inject(var):
            out.append("cannot inject %s" % var)
    seen, unique = set(), []
    for reason in out:
        if reason not in seen:
            seen.add(reason)
            unique.append(reason)
    return unique
