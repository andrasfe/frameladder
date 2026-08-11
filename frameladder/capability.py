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


def canonical_op(op_key: str) -> str:
    """One spelling for an operation both sides know by different names.

    The two programs key the same mock differently: a verb and a target
    joined by whatever separator each happened to pick, sometimes with the
    system in the middle (`EXEC:CICS:READ` against `EXEC CICS READ`). The
    parts are the identity; the punctuation between them is not. Hyphens are
    left alone because they are inside COBOL names, not between them.

    This only unifies punctuation and case. It will not connect two genuinely
    different names - that is what `aliases` is for, and a harness that needs
    one says so rather than having it guessed.
    """
    text = str(op_key or "").upper()
    for separator in (":", "/", ".", "|", ",", "\t"):
        text = text.replace(separator, " ")
    return ":".join(text.split())


@dataclass(frozen=True)
class Operation:
    """A mock the harness can replay, and how far it can be driven."""

    op_key: str
    fields: frozenset = frozenset()      # payload fields it can set, empty = any
    max_outcomes: int = 0                # 0 = no stated limit
    # Can the harness pick an outcome by looking at program state, or does it
    # only replay an ordered list? A plan tells two invocations of one verb
    # apart by a discriminator - "the READ whose key is X returns not-found" -
    # and a harness that cannot match on state will deliver those in order and
    # ignore the condition, which is a different test from the one planned.
    # `None` means the harness did not say; the planner reports such outcomes
    # rather than refusing them, because silence is not a no.
    matches_on_state: bool | None = None
    # Other names the harness answers to for this same operation. Punctuation
    # and case are handled by `canonical_op`; this is for the rest, where the
    # harness calls a file by a DD name, a DDL name or a handle the source
    # never mentions. Nothing can derive that mapping from the COBOL, so the
    # profile states it and the planner reports which alias it matched.
    #
    # Last on purpose. `represent.py` and the tests construct an Operation
    # positionally, so a field inserted above this line silently changes what
    # their fourth argument means - which is how this arrived, with
    # `matches_on_state` landing in `aliases` and every lookup raising.
    aliases: frozenset = frozenset()

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
    # The work list exactly as the harness wrote it. `uncovered` above is the
    # strict reading, which only works when both sides number decisions the
    # same way - and they do not. Resolution against a parsed program is the
    # supported path; see `directions.resolve`.
    raw_uncovered: tuple = ()
    # Set when the profile claims its ordinals came from this tool, which is
    # true of one `coverage --work-list` feeding the next run.
    trust_ordinals: bool = False
    # op_key (canonical) -> the Operation it names, including aliases.
    _op_index: dict | None = None
    # An empty profile must not silently forbid everything: a caller that
    # supplies no capabilities is saying "no constraints stated", which is
    # the behaviour every existing command already has.
    stated: bool = False

    # -- the questions the planner asks ------------------------------------
    def can_inject(self, name: str) -> bool:
        if not self.stated or self.injectable is None:
            return True
        return _base(name) in self.injectable

    def operation(self, op_key: str):
        """The Operation this key names, under any spelling the profile allows.

        Exact first, then punctuation-and-case, then declared aliases. The
        tiers are tried in decreasing order of confidence so that a profile
        which names an operation exactly is never overridden by a looser
        match on some other entry.
        """
        if self.operations is None:
            return None
        exact = self.operations.get((op_key or "").upper())
        if exact is not None:
            return exact
        return (self._index()).get(canonical_op(op_key))

    def _index(self) -> dict:
        if self._op_index is None:
            index: dict = {}
            for op in (self.operations or {}).values():
                index.setdefault(canonical_op(op.op_key), op)
            # Aliases go in second so a real op_key always wins a collision:
            # two operations claiming one alias is the harness's ambiguity,
            # not something to resolve by iteration order.
            for op in (self.operations or {}).values():
                for alias in op.aliases:
                    index.setdefault(canonical_op(alias), op)
            self._op_index = index
        return self._op_index

    def can_replay(self, op_key: str) -> bool:
        if not self.stated or self.operations is None:
            return True
        return self.operation(op_key) is not None

    def can_set(self, op_key: str, name: str) -> bool:
        if not self.stated or self.operations is None:
            return True
        op = self.operation(op_key)
        return bool(op) and op.accepts(_base(name))

    def resolve_uncovered(self, program):
        """The work list, matched against this program's own decisions.

        Returns a `directions.Resolution`, whose `wanted` is what a planner
        should use in place of `self.wanted`. Kept here rather than at the
        call site because every caller needs the same thing and the failure
        mode of getting it wrong is silent.
        """
        from .directions import resolve
        return resolve(self.raw_uncovered, program,
                       trust_ordinals=self.trust_ordinals)

    def discriminates(self, op_key: str) -> bool | None:
        """Whether the harness can select an outcome by program state.

        Three answers, not two. `None` is "the profile did not say", and a
        planner must not read it as a refusal - 188 of 819 plans measured on
        this corpus carry a discriminated outcome, and refusing them all on
        silence would throw away a quarter of the work for a claim nobody
        made.
        """
        op = self.operation(op_key)
        return op.matches_on_state if op else None

    def outcome_limit(self, op_key: str) -> int:
        op = self.operation(op_key)
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
        matches = entry.get("matches_on_state")
        operations[key] = Operation(
            key,
            frozenset(str(f).upper() for f in entry.get("fields") or ()),
            int(entry.get("max_outcomes") or 0),
            None if matches is None else bool(matches),
            frozenset(str(a).upper() for a in entry.get("aliases") or ()))

    raw_uncovered = tuple(d for d in raw.get("uncovered_directions") or ()
                          if isinstance(d, dict))
    uncovered = tuple(
        Direction(str(d.get("paragraph", "")).upper(),
                  int(d.get("ordinal", -1)),
                  str(d.get("kind", "IF")).upper(),
                  bool(d.get("direction", True)))
        for d in raw_uncovered)

    # Whose ordinals are these? Only this tool's own output may be read as an
    # identity; anything else names a paragraph at best. `coverage
    # --work-list` stamps the field, so the common round-trip keeps its
    # precision without any profile having to opt in by hand.
    ordinal_source = str(raw.get("ordinal_source", "")).strip().lower()

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
        raw_uncovered=raw_uncovered,
        trust_ordinals=(ordinal_source == "frameladder"),
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
