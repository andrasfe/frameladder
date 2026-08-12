"""One paragraph as a set of guarded commands, computed once and reused.

The ladder lifts an obligation outwards one call site at a time, re-deriving
what the caller does every time a chain passes through it. That is expensive
on a large program and, worse, it is *partial*: it sees the guards on the call
site but not the statements between paragraph entry and that call, so a value
bound at entry and overwritten two lines before the PERFORM looks fine. The
largest disposition on both corpora is a plan that walks its whole chain and
misses the last hop, and this is where that lives.

A summary answers the question directly. For each way through a paragraph it
records what must hold on entry, what the paragraph writes on the way, which
paragraphs it performs and in what order, and how it leaves. Composition
along a chain is then relation composition rather than a fresh search, and
"which write reaches this read on this route" is read off rather than guessed
from static order.

Why this is affordable in COBOL specifically, measured over 834 paragraphs in
41 programs: the median paragraph has **2** paths and 9 statements, 78% have
at most 4, 89% at most 16, and only **5%** contain a loop - the one construct
that needs an invariant rather than enumeration. A paragraph has no
parameters, no heap, no recursion and no aliasing except REDEFINES, so its
interface is exactly its live-in set. Very little of that is true of a
general-purpose language.

What this module will not do is pretend. A paragraph past the path cap, or
containing a loop, comes back with ``complete=False``, and a caller may use
such a summary as evidence that a path *exists* but never as evidence that one
does not. That distinction is the difference between "no plan on this chain"
and "this code is dead", and this repository has already been wrong about it
once.
"""

from __future__ import annotations

import re

from dataclasses import dataclass, field

from .conditions import condition_atoms
from .ir import move_targets, norm, parse_term

# Enumeration is a product over the decisions inside a paragraph, so it needs a
# ceiling. 16 covers 89% of the corpus and 64 covers 94%; past that the tail is
# a handful of dispatchers whose summaries would be worth little anyway. The
# cap is a budget, not a claim that the rest are uninteresting - which is why
# passing it sets `complete=False` rather than dropping paths silently.
MAX_PATHS = 16

# Statements that hand control somewhere else rather than falling through.
_LEAVES = ("GO_TO", "GOTO", "GOBACK", "STOP", "EXIT_PROGRAM")


@dataclass(frozen=True)
class Write:
    """One assignment on a path, in the order the paragraph makes it."""

    var: str
    source: str                    # the sending operand, as written
    line: int = 0
    external: bool = False         # produced by a stub, not by this statement


@dataclass(frozen=True)
class Path:
    """One way through a paragraph: what it needs, does, calls and how it ends."""

    condition: tuple = ()          # atoms that must hold at paragraph entry
    writes: tuple = ()             # Write, in order
    calls: tuple = ()              # (index into writes, performed target)
    escape: str = ""               # "" falls through, else GO TO target/GOBACK

    def writes_before(self, target: str) -> tuple:
        """Everything written before this path performs ``target``.

        The last-hop question in one line: a value bound at paragraph entry
        survives to the call only if nothing here has overwritten it.
        """
        for index, name in self.calls:
            if name.upper() == target.upper():
                return self.writes[:index]
        return self.writes

    def reaches(self, target: str) -> bool:
        return any(name.upper() == target.upper() for _i, name in self.calls)


@dataclass
class Summary:
    paragraph: str
    paths: tuple = ()
    complete: bool = True          # False: capped or contains a loop
    why_partial: str = ""

    @property
    def deterministic(self) -> bool:
        return len(self.paths) == 1

    def paths_reaching(self, target: str) -> list:
        return [p for p in self.paths if p.reaches(target)]

    def summary(self) -> dict:
        return {"paragraph": self.paragraph, "paths": len(self.paths),
                "complete": self.complete, "why_partial": self.why_partial,
                "calls": sorted({n for p in self.paths for _i, n in p.calls})}


def summarise(program, paragraph: str, max_paths: int = MAX_PATHS) -> Summary:
    """Enumerate the ways through one paragraph.

    Deliberately syntactic and deliberately local: it does not follow a
    PERFORM into the callee, because that is what composition is for, and it
    does not evaluate anything, because the interpreter is the authority on
    what a statement does. What it produces is a *claim* about structure that
    `conformance` can check against the interpreter.
    """
    para = program.paragraph(paragraph)
    if para is None:
        return Summary(paragraph.upper(), (), False, "no such paragraph")

    partial = [""]
    paths = _walk(para.get("statements", []), Path(), max_paths, partial,
                  program)
    if len(paths) > max_paths:
        paths = paths[:max_paths]
        partial[0] = partial[0] or "more than %d paths" % max_paths
    return Summary(paragraph.upper(), tuple(paths), not partial[0], partial[0])


def _walk(statements, prefix: Path, cap: int, partial: list,
          program=None) -> list:
    """Every continuation of ``prefix`` through ``statements``."""
    live = [prefix]
    for stmt in statements or ():
        if len(live) > cap:
            partial[0] = partial[0] or "more than %d paths" % cap
            return live
        nxt: list = []
        for path in live:
            if path.escape:
                nxt.append(path)          # control has already left
                continue
            nxt.extend(_step(stmt, path, cap, partial, program))
        live = nxt
    return live


def _step(stmt, path: Path, cap: int, partial: list, program=None) -> list:
    kind = stmt.get("type", "")
    attrs = stmt.get("attributes", {}) or {}
    line = stmt.get("line_start", 0)
    text = norm(stmt.get("text", ""))
    children = stmt.get("children") or []

    if kind == "IF":
        condition = attrs.get("condition", "")
        arms = [c for c in children if c.get("type") != "ELSE"]
        other = [c for c in children if c.get("type") == "ELSE"]
        out = []
        for taken, body in ((True, arms), (False, other)):
            for atoms in _alternatives(condition, negate=not taken):
                branch = Path(path.condition + tuple(atoms), path.writes,
                              path.calls, path.escape)
                inner = [c for arm in body for c in (arm.get("children") or [])] \
                    if (not taken and other) else body
                out.extend(_walk(inner, branch, cap, partial, program))
        return out or [path]

    if kind in ("EVALUATE", "SEARCH"):
        subject = attrs.get("subject", "") or attrs.get("condition", "")
        out = []
        for arm in children:
            if arm.get("type") != "WHEN":
                continue
            value = (arm.get("attributes", {}) or {}).get("value", "")
            for atoms in _arm_atoms(subject, value):
                branch = Path(path.condition + tuple(atoms), path.writes,
                              path.calls, path.escape)
                out.extend(_walk(arm.get("children") or [], branch, cap, partial, program))
        return out or [path]

    if kind == "PHRASE":
        # AT END / INVALID KEY and their negations: the handler runs or it
        # does not, and which way is decided by an operation's status rather
        # than by anything in this paragraph. Both continuations are real.
        out = []
        for body in (children, []):
            branch = Path(path.condition, path.writes, path.calls, path.escape)
            out.extend(_walk(body, branch, cap, partial, program))
        return out or [path]

    if kind.startswith("PERFORM"):
        target = (attrs.get("target") or "").strip()
        if attrs.get("condition") or attrs.get("varying") or attrs.get("times") \
                or kind == "PERFORM_INLINE":
            # A loop needs an invariant, not enumeration. The body is walked
            # once so its writes and calls are visible, and the summary says
            # it is incomplete.
            partial[0] = partial[0] or "contains a loop"
            if target:
                path = _with_calls(path, _range_members(program, target))
            return _walk(children, path, cap, partial, program) if children else [path]
        if target:
            return [_with_calls(path, _range_members(program, target))]
        return [path]

    if kind in _LEAVES:
        target = (attrs.get("target") or "").strip()
        return [Path(path.condition, path.writes, path.calls,
                     target.upper() if target else kind)]

    return [_with_writes(path, stmt, kind, attrs, line, text)]


def _range_members(program, target: str) -> list:
    """`PERFORM A THRU B` runs every paragraph from A to B in source order.

    Recorded as one call to a paragraph literally named "A THRU B" it matches
    nothing, and the summary then predicts none of the calls the range makes -
    which is 12% of this corpus, because the THRU range is how structured
    COBOL is written.
    """
    parts = [t.strip().upper() for t in
             re.split(r"\s+THRU\s+|\s+THROUGH\s+", target, flags=re.I)
             if t.strip()]
    if len(parts) < 2 or program is None:
        return parts[:1] or [target.upper()]
    order = list(program.paragraph_names)
    try:
        first, last = order.index(parts[0]), order.index(parts[-1])
    except ValueError:
        return parts
    return order[first:last + 1] if last >= first else parts


def _with_call(path: Path, target: str) -> Path:
    return _with_calls(path, [target])


def _with_calls(path: Path, targets) -> Path:
    at = len(path.writes)
    return Path(path.condition, path.writes,
                path.calls + tuple((at, t.upper()) for t in targets),
                path.escape)


def _with_writes(path: Path, stmt, kind, attrs, line, text) -> Path:
    """Record what this statement assigns, without evaluating it."""
    from .provenance import STUB_KINDS, stub_outputs

    writes = []
    if kind == "MOVE":
        source = attrs.get("source", "")
        for base in move_targets(attrs.get("targets", "")):
            writes.append(Write(base.upper(), source, line))
    elif kind == "SET":
        name = attrs.get("name")
        if name:
            writes.append(Write(str(name).upper(),
                                str(attrs.get("value", "")), line))
    elif kind == "INITIALIZE":
        body = text[len("INITIALIZE"):].strip() if text.upper().startswith(
            "INITIALIZE") else text
        for name in body.replace(",", " ").split():
            clean = name.split("(")[0].strip().upper().rstrip(".")
            if clean and clean not in ("ALL", "TO", "VALUE", "REPLACING"):
                writes.append(Write(clean, "ZERO-OR-SPACES", line))
    elif kind in ("ADD", "SUBTRACT", "MULTIPLY", "DIVIDE", "COMPUTE"):
        import re as _re
        for m in _re.finditer(r"\bTO\s+([A-Z0-9-]+)|\bGIVING\s+([A-Z0-9-]+)"
                              r"|COMPUTE\s+([A-Z0-9-]+)", text, _re.I):
            for g in m.groups():
                if g:
                    writes.append(Write(g.upper(), text, line))
    elif kind in STUB_KINDS:
        for name in stub_outputs(text):
            writes.append(Write(name.upper(), "", line, external=True))

    if not writes:
        return path
    return Path(path.condition, path.writes + tuple(writes), path.calls,
                path.escape)


def _alternatives(condition: str, negate: bool) -> list:
    """The condition in disjunctive normal form, as a list of conjunctions.

    An OR is genuinely several ways in, and collapsing it to one would make a
    summary claim a path is unreachable when the program offers three.
    """
    try:
        alts = condition_atoms(condition, negate)
    except Exception:                                        # noqa: BLE001
        return [[]]
    return [list(a) for a in alts] or [[]]


def _arm_atoms(subject: str, value: str) -> list:
    from .conditions import when_condition
    if not subject or not value:
        return [[]]
    if norm(subject).upper() in ("TRUE", "FALSE"):
        return _alternatives(value, norm(subject).upper() == "FALSE")
    if value.strip().upper() in ("OTHER", "ANY"):
        return [[]]
    return _alternatives(when_condition(subject, value), False)


def summarise_program(program, max_paths: int = MAX_PATHS) -> dict:
    """Every paragraph, summarised once. This is the point of the exercise:
    a chain through a paragraph re-reads its summary rather than re-deriving
    it, which is what makes composition cheaper than search on a large
    program."""
    return {name: summarise(program, name, max_paths)
            for name in program.paragraph_names}
