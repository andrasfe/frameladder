"""Which variables a paragraph reads before it writes them.

The README has always described a paragraph's "arguments" as its live-in set,
but nothing computed it - the ladder worked from call-site guards instead,
which is enough to *reach* a frame and not enough to *reuse* what it learned.

Reuse needs it.  A witness that opens paragraph P is only transferable to
another trace if its precondition is stated over the variables P actually
consumes: anything else in the state is incidental, and pinning it would make
the witness look caller-specific when it is not.  Equally, a witness is only
valid at a new call site if nothing on the way there overwrites those
variables - which is a question about the live-in set too.

So this is the interface that makes a frame's work an asset rather than a
one-off.
"""

from __future__ import annotations

import re

from .conditions import condition_atoms
from .ir import move_targets, norm, parse_term

_ARITH = {"ADD", "SUBTRACT", "COMPUTE", "MULTIPLY", "DIVIDE"}
_NOISE = {"TO", "FROM", "BY", "GIVING", "INTO", "THRU", "THROUGH", "UNTIL",
          "VARYING", "WHEN", "OTHER", "SIZE", "ERROR", "DELIMITED", "END-EXEC",
          "TRUE", "FALSE", "ALL", "SPACES", "SPACE", "ZERO", "ZEROS", "ZEROES",
          "LOW-VALUES", "HIGH-VALUES", "NULL", "NULLS", "DEPENDING", "ON"}
_WORD = re.compile(r"[A-Z][A-Z0-9-]*", re.I)


def variable_universe(program) -> set:
    """Every name the program uses as data, however it was declared.

    Filtering live-in against the data division alone is wrong when a
    copybook is missing - the record fields are real variables that happen
    to have no declaration here. Filtering against nothing is worse: raw
    statement text is full of verbs and program names, and they all look
    like identifiers.
    """
    cached = getattr(program, "_universe", None)
    if cached is not None:
        return cached
    known = set(program.model.declared) | set(program.model.condition_names)
    for parent, _values in program.model.condition_names.values():
        known.add(parent.upper())

    def walk(stmt):
        attrs = stmt.get("attributes", {})
        src = parse_term(attrs.get("source", ""))
        if src.kind == "var":
            known.add(src.name)
        known.update(move_targets(attrs.get("targets", "")))
        for key in ("condition", "varying", "until"):
            if attrs.get(key):
                for alternative in condition_atoms(attrs[key]):
                    for atom in alternative:
                        known.update(t.name for t in (atom.lhs, atom.rhs)
                                     if t.kind == "var")
        subject = norm(attrs.get("subject", ""))
        if subject and subject.upper() not in ("TRUE", "FALSE"):
            term = parse_term(subject)
            if term.kind == "var":
                known.add(term.name)
        for child in stmt.get("children") or []:
            walk(child)

    for para in program.paragraphs:
        for stmt in para.get("statements", []):
            walk(stmt)
    known -= set(program.paragraph_names)
    try:
        program._universe = known
    except AttributeError:
        pass
    return known


def _names(text: str) -> list:
    out = []
    for m in _WORD.finditer(norm(text or "")):
        word = m.group(0).upper()
        if word in _NOISE or word.isdigit():
            continue
        out.append(word)
    return out


def reads_of(stmt: dict) -> list:
    """Variables a single statement consumes."""
    kind = stmt.get("type", "")
    attrs = stmt.get("attributes", {})
    out: list = []

    for key in ("condition", "varying", "until"):
        text = attrs.get(key)
        if text:
            for alternative in condition_atoms(text):
                for atom in alternative:
                    out.extend(t.name for t in (atom.lhs, atom.rhs)
                               if t.kind == "var")
                    for term in (atom.lhs, atom.rhs):
                        out.extend(str(i).upper() for i in term.index)

    if kind == "MOVE":
        source = parse_term(attrs.get("source", ""))
        if source.kind == "var":
            out.append(source.name)
            out.extend(str(i).upper() for i in source.index)
        # A subscript on the *target* is read even though the target is written.
        for m in re.finditer(r"\(([^)]*)\)", attrs.get("targets", "")):
            out.extend(_names(m.group(1)))
    elif kind == "EVALUATE":
        subject = norm(attrs.get("subject", ""))
        if subject.upper() not in ("TRUE", "FALSE"):
            out.extend(_names(subject))
    elif kind == "WHEN":
        out.extend(_names(attrs.get("value", "")))
    elif kind in _ARITH:
        out.extend(_names(stmt.get("text", "")))
    elif kind in ("DISPLAY", "STRING", "UNSTRING", "INSPECT", "WRITE",
                  "REWRITE", "CALL", "SET"):
        out.extend(_names(stmt.get("text", "")))
    return out


def writes_of(stmt: dict) -> list:
    kind = stmt.get("type", "")
    attrs = stmt.get("attributes", {})
    if kind == "MOVE":
        return move_targets(attrs.get("targets", ""))
    if kind == "SET":
        return [attrs["name"]] if attrs.get("name") else []
    if kind in _ARITH:
        out = []
        for groups in re.findall(r"\bTO\s+([A-Z0-9-]+)|\bGIVING\s+([A-Z0-9-]+)"
                                 r"|COMPUTE\s+([A-Z0-9-]+)",
                                 norm(stmt.get("text", "")), re.I):
            out.extend(g.upper() for g in groups if g)
        return out
    if kind in ("READ", "RETURN", "ACCEPT"):
        return [m.group(1).upper() for m in
                re.finditer(r"\bINTO\s+([A-Z0-9-]+)", norm(stmt.get("text", "")),
                            re.I)]
    return []


def live_in(program, paragraph: str, _seen: frozenset = frozenset(),
            _cache: dict | None = None) -> set:
    """Variables read before being written, following PERFORMs.

    A read that a *later* write would satisfy is still a read: COBOL runs in
    order, so what matters is whether the value already had to be there.
    """
    paragraph = paragraph.upper()
    cache = _cache if _cache is not None else getattr(program, "_live_in", None)
    if cache is None:
        cache = {}
        try:
            program._live_in = cache
        except AttributeError:
            pass
    if paragraph in cache:
        return cache[paragraph]
    if paragraph in _seen:
        return set()                      # recursion: contributes nothing new

    para = program.paragraph(paragraph)
    if para is None:
        return set()

    needed: set = set()
    written: set = set()

    def walk(statements):
        for stmt in statements:
            kind = stmt.get("type", "")
            attrs = stmt.get("attributes", {})
            if kind in ("PERFORM", "GO_TO", "GOTO") and attrs.get("target"):
                for raw in re.split(r"\s+THRU\s+|\s+THROUGH\s+",
                                    attrs["target"], flags=re.I):
                    callee = raw.strip().upper()
                    if callee and callee != paragraph:
                        downstream = live_in(program, callee,
                                             _seen | {paragraph}, cache)
                        needed.update(v for v in downstream if v not in written)
            for name in reads_of(stmt):
                if name not in written:
                    needed.add(name)
            written.update(writes_of(stmt))
            walk(stmt.get("children") or [])

    walk(para.get("statements", []))
    resolved = {v for v in needed if v in variable_universe(program)}
    cache[paragraph] = resolved
    return resolved


def restrict(state: dict, variables: set) -> dict:
    """Keep only the part of a state a frame actually consumes."""
    return {k: v for k, v in state.items() if k.upper() in variables}
