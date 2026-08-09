"""How much of a program a set of plans actually exercises.

"Targets reached" counts plans that arrived somewhere. Coverage is the union
of what all of them touched, which is a different and less flattering number:
one plan per paragraph can reach every paragraph while leaving half the
branch directions untried, because reaching a frame says nothing about which
way its conditions went once inside.

Branches are counted by *direction*, since taking an IF only one way is half
a branch. A paragraph with no conditions contributes nothing to the branch
total, so the denominator is decisions rather than statements.
"""

from __future__ import annotations

from dataclasses import dataclass, field


# The interpreter names a loop by the verb it saw; `branches_of` names it by
# what it is. Without this the two never join, and every loop in the program
# sits in the denominator permanently uncoverable - 30 of them across the
# corpus.
_KIND = {"PERFORM_UNTIL": "LOOP", "PERFORM_VARYING": "LOOP"}


@dataclass(frozen=True)
class Branch:
    paragraph: str
    line: int
    kind: str
    condition: str
    ordinal: int = -1

    @property
    def key(self) -> tuple:
        # Ordinal, not line: see cobol._stamp_ordinals. Two decisions
        # expanded from one COPY share a line and must not share an identity.
        return (self.paragraph, self.ordinal, self.kind)


def branches_of(program) -> list:
    """Every decision point, with the directions it could go."""
    out: list = []

    def walk(stmt, para):
        kind = stmt.get("type", "")
        attrs = stmt.get("attributes", {})
        line = stmt.get("line_start", 0)
        if kind == "IF":
            out.append(Branch(para, line, "IF", attrs.get("condition", ""),
                              stmt.get("ordinal", -1)))
        elif kind == "EVALUATE":
            for arm in stmt.get("children") or []:
                if arm.get("type") == "WHEN":
                    out.append(Branch(para, arm.get("line_start", line), "WHEN",
                                      arm.get("attributes", {}).get("value", ""),
                                      arm.get("ordinal", -1)))
        elif kind == "PHRASE":
            # `AT END` / `INVALID KEY` and their negations are decisions: the
            # handler runs or it does not, and which way it went is exactly
            # the thing a read loop turns on. Leaving them out of the
            # denominator scored their directions for free.
            out.append(Branch(para, line, "PHRASE",
                              attrs.get("phrase", ""), stmt.get("ordinal", -1)))
        elif kind.startswith("PERFORM") and (attrs.get("condition")
                                             or attrs.get("varying")):
            out.append(Branch(para, line, "LOOP",
                              attrs.get("condition") or attrs.get("varying", ""),
                              stmt.get("ordinal", -1)))
        for child in stmt.get("children") or []:
            walk(child, para)

    for para in program.paragraphs:
        for stmt in para.get("statements", []):
            walk(stmt, para["name"])

    # Consecutive WHEN arms share one body, so the same statements are
    # reachable under two arms and the walk meets them twice. They are one
    # decision in the source and must count once, or the denominator grows
    # every time a programmer writes `WHEN A / WHEN B`.
    seen, unique = set(), []
    for branch in out:
        if branch.key in seen:
            continue
        seen.add(branch.key)
        unique.append(branch)
    return unique


@dataclass
class Coverage:
    paragraphs_hit: set = field(default_factory=set)
    paragraphs_total: int = 0
    directions_hit: set = field(default_factory=set)   # (para, line, kind, bool)
    branches_total: int = 0
    runs: int = 0

    @property
    def paragraph_pct(self) -> float:
        return 100.0 * len(self.paragraphs_hit) / max(1, self.paragraphs_total)

    @property
    def direction_pct(self) -> float:
        return 100.0 * len(self.directions_hit) / max(1, 2 * self.branches_total)

    def summary(self) -> dict:
        return {"runs": self.runs,
                "paragraphs": "%d/%d" % (len(self.paragraphs_hit),
                                         self.paragraphs_total),
                "paragraph_pct": round(self.paragraph_pct, 1),
                "directions": "%d/%d" % (len(self.directions_hit),
                                         2 * self.branches_total),
                "direction_pct": round(self.direction_pct, 1)}


def accumulate(program, traces) -> Coverage:
    """Union what a set of runs touched."""
    cov = Coverage(paragraphs_total=len(program.paragraph_names),
                   branches_total=len(branches_of(program)))
    for trace in traces:
        cov.runs += 1
        cov.paragraphs_hit |= set(trace.entered)
        for event in trace.guards:
            cov.directions_hit.add((event.paragraph, event.ordinal,
                                    _KIND.get(event.kind, event.kind),
                                    bool(event.result)))
    return cov


def missing(program, cov: Coverage) -> dict:
    """What was never touched, which is the work list."""
    paragraphs = [n for n in program.paragraph_names
                  if n not in cov.paragraphs_hit]
    taken = {(p, l, k) for p, l, k, _ in cov.directions_hit}
    both = {}
    for p, l, k, r in cov.directions_hit:
        both.setdefault((p, l, k), set()).add(r)
    partial, untouched = [], []
    for b in branches_of(program):
        seen = both.get(b.key)
        if seen is None:
            untouched.append(b)
        elif len(seen) < 2:
            partial.append((b, sorted(seen)[0]))
    return {"paragraphs": paragraphs, "untouched": untouched,
            "one_way_only": partial}
