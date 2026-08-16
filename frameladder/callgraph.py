"""Infeasibility certification for commarea-gated branch directions.

`frameladder witnesses` answers "does a recipe exist that takes this
direction". This module answers a cheaper question about the directions
nothing found one for: "could *any real caller in the corpus* have put the
value this direction needs into the field it tests, before handing control
to this program". If no caller can, the direction is not merely unwitnessed -
it is unreachable from any entry this program actually has, which is worth
reporting as a denominator reduction rather than as a gap to keep searching.

Both halves are built from evidence the programs themselves carry: a call
edge exists because an `EXEC CICS XCTL`/`LINK` statement names a target,
directly or through a table a copybook declares; a value is "producible"
because some program's own `MOVE` statements can be shown, statically, to
put it there. Nothing here is keyed off a program or field *name* - see
`.claude/skills/witness-pattern-discovery/SKILL.md` section 4 for the gate
this module was written to pass.

Deliberately not a control-flow-ordered analysis: whether a `MOVE` runs
before the `XCTL` that reads its target is a per-run question the interpreter
already answers; this asks a program-wide, order-free question instead -
"can P *ever* write this value here" - which is the weaker, safer claim an
infeasibility certificate needs. A false "producible" only sends a witness
search somewhere it will fail anyway; a false "unreachable" would throw away
a real direction, which is the one mistake this module must not make. Also
not a full CICS dispatch resolver - only `PROGRAM(...)` on `XCTL`/`LINK` is
read; dynamic `CALL` and TS/TD-queue routing are out of scope.
"""

from __future__ import annotations

import json
import os
import re
from dataclasses import asdict, dataclass

from .cobol import load_program
from .conditions import condition_atoms
from .ir import base_name
from .layout import byte_length

_CICS = re.compile(r"\bCICS\b", re.I)
_XCTL_LINK = re.compile(r"\b(XCTL|LINK)\b", re.I)
_PROGRAM_KW = re.compile(r"\bPROGRAM\s*\(", re.I)
_COMMAREA_KW = re.compile(r"\bCOMMAREA\s*\(", re.I)
_SUBSCRIPT = re.compile(r"^([A-Z0-9][A-Z0-9-]*)\s*\(\s*([A-Z0-9][A-Z0-9-]*)\s*\)$", re.I)
_LITERAL = re.compile(r"^'([^']*)'$|^\"([^\"]*)\"$")
# A MOVE's `targets` text may name several receivers, each possibly qualified
# (`X OF Y`); this finds each receiver as one match rather than splitting on
# every space, which would cut a qualified name in two.
_QUALIFIED_NAME = re.compile(
    r"[A-Z0-9][A-Z0-9-]*(?:\s+(?:OF|IN)\s+[A-Z0-9][A-Z0-9-]*)*", re.I)

# How deep a chain of "this field's value comes from that field" is followed
# before giving up. Two or three hops covers every pattern actually observed
# (`MOVE LIT-X TO A` is one; `MOVE A TO B` where A was itself derived is
# two); a hard cap makes a reference cycle terminate instead of recursing.
_MAX_HOPS = 4


@dataclass(frozen=True)
class CallEdge:
    """One `XCTL`/`LINK` call site, resolved to a real program in the corpus."""

    caller: str
    callee: str
    line: int
    verb: str                  # XCTL | LINK
    how: str                   # literal | constant | table | writer-harvest
    commarea: str = ""         # the COMMAREA operand text, "" if none

    def to_dict(self) -> dict:
        return asdict(self)


# --------------------------------------------------------------------------
# Loading a corpus once, and the small parsing helpers this module needs
# beyond what `cobol.py` already does.
# --------------------------------------------------------------------------

def _cbl_files(corpus_dir: str) -> list:
    return sorted(os.path.join(corpus_dir, e) for e in os.listdir(corpus_dir)
                  if e.lower().endswith(".cbl"))


def _program_name(path: str) -> str:
    return os.path.splitext(os.path.basename(path))[0].upper()


def load_corpus(corpus_dir: str, copybooks: str | None = None) -> dict:
    """Every `.cbl` in `corpus_dir`, loaded once, keyed by program name."""
    out: dict = {}
    for path in _cbl_files(corpus_dir):
        try:
            out[_program_name(path)] = load_program(path, copybooks)
        except Exception:                                     # noqa: BLE001
            # A program this parser cannot read contributes no edges and is
            # never a resolvable target - reported by its absence, not by
            # aborting the whole corpus over one file.
            continue
    return out


def _iter_statements(stmts, _seen=None):
    """Every statement in a subtree, each exactly once.

    Consecutive `WHEN` arms with no body of their own share the *next* arm's
    body - literally the same list object (`cobol.py`'s `_stamp_ordinals`
    relies on this to give the shared statements one ordinal). Walking each
    arm's children independently visits that body once per arm that shares
    it, so a single `EXEC CICS XCTL` under a three-way `WHEN A / WHEN B /
    WHEN C` would otherwise be counted as three call sites instead of one.
    """
    if _seen is None:
        _seen = set()
    for stmt in stmts or []:
        marker = id(stmt)
        if marker in _seen:
            continue
        _seen.add(marker)
        yield stmt
        yield from _iter_statements(stmt.get("children"), _seen)


def _iter_all(program):
    seen: set = set()
    for para in program.paragraphs:
        yield from _iter_statements(para.get("statements", []), seen)


_MOVES_CACHE: dict = {}


def _moves_of(program) -> list:
    """`(receiver_text, source_text, line)` for every MOVE in the program.

    Cached per program object: certification re-asks this for the same
    program from several call sites (once per predecessor, once per
    corpus-wide producer scan), and re-walking the whole statement tree each
    time is pure waste on a 44-program corpus asked about repeatedly.
    """
    key = id(program)
    cached = _MOVES_CACHE.get(key)
    if cached is not None:
        return cached
    out = []
    for stmt in _iter_all(program):
        if stmt.get("type") != "MOVE":
            continue
        attrs = stmt.get("attributes", {})
        src, targets = attrs.get("source"), attrs.get("targets")
        if not src or not targets:
            continue
        for m in _QUALIFIED_NAME.finditer(targets):
            out.append((m.group(0), src, stmt.get("line_start", 0)))
    _MOVES_CACHE[key] = out
    return out


def _balanced_operand(body: str, keyword: re.Pattern):
    """The text inside `KEYWORD(...)`, respecting nested parens.

    `PROGRAM(CDEMO-MENU-OPT-PGMNAME(WS-OPTION))` has its own subscript inside
    the operand it names; a regex stopping at the first `)` reads it as
    `CDEMO-MENU-OPT-PGMNAME(WS-OPTION` - unterminated, and every table-driven
    dispatch in the corpus resolves to nothing. Depth-counting from the open
    paren the keyword itself introduces is the only way to get the whole
    operand back.
    """
    m = keyword.search(body)
    if not m:
        return None
    depth, i = 1, m.end()
    start = i
    while i < len(body) and depth:
        if body[i] == "(":
            depth += 1
        elif body[i] == ")":
            depth -= 1
        i += 1
    if depth:
        return None
    return body[start:i - 1].strip()


def _literal(text: str):
    m = _LITERAL.match(text.strip())
    if not m:
        return None
    return m.group(1) if m.group(1) is not None else m.group(2)


# --------------------------------------------------------------------------
# Resolving what a field can hold: VALUE clauses, MOVEs, and OCCURS tables
# correlated with the copybook's own literal layout via REDEFINES.
# --------------------------------------------------------------------------

def _table_literal_pool(model, table_field: str) -> set:
    """The literal values a subscripted table field can be read as.

    `CDEMO-MENU-OPT-PGMNAME(WS-OPTION)` is a child of an OCCURS group that
    itself carries no VALUE clauses - the group REDEFINES a second layout
    that does, one FILLER per column per row. The pool is every literal in
    that redefined layout whose declared width matches the subscripted
    field's, found through `DataModel.redefines`/`.children`, never through
    either field's name.
    """
    name = (table_field or "").upper()
    if name not in model.declared and name not in model.pic:
        return set()
    group = name
    seen: set = set()
    while group and group not in model.occurs:
        if group in seen:
            group = ""
            break
        seen.add(group)
        group = model.parent.get(group, "")
    if not group or group not in model.occurs:
        # No OCCURS ancestor at all - the field's own VALUE, if any, is the
        # whole pool.
        v = model.initial.get(name)
        return {str(v)} if v is not None else set()

    width = byte_length(model.pic_of(name), model.usage_of(name))
    # The REDEFINES is rarely on the OCCURS group itself - COBOL nests the
    # table one level inside a group that carries the clause, the way
    # `05 CDEMO-MENU-OPTIONS REDEFINES CDEMO-MENU-OPTIONS-DATA. 10 ... OCCURS`
    # does. So the search climbs from the OCCURS group through its own
    # ancestors, not just the group itself, checking the redefines relation
    # in both directions at each step.
    literal_group = None
    node, hops = group, 0
    while node and hops < 8:
        literal_group = model.redefines.get(node)
        if literal_group is None:
            for candidate, target in model.redefines.items():
                if target == node:
                    literal_group = candidate
                    break
        if literal_group:
            break
        node = model.parent.get(node, "")
        hops += 1
    members = model.descendants(literal_group) if literal_group else model.descendants(group)

    pool: set = set()
    for member in members:
        value = model.initial.get(member)
        if value is None:
            continue
        if width and byte_length(model.pic_of(member), model.usage_of(member)) != width:
            continue
        pool.add(str(value))
    return pool


def _field_values(program, model, field_name: str, *, _depth: int = 0,
                   _seen: frozenset = frozenset()) -> set:
    """Every literal this program's own statements can put in `field_name`.

    Includes the field's own VALUE clause (if any) and every literal reached
    by following MOVE sources - a literal directly, a subscripted table
    (`_table_literal_pool`), or another field, resolved the same way up to
    `_MAX_HOPS`. Deliberately order-free: see the module docstring for why
    that is the safe direction for a certifier to over-approximate in.
    """
    target = base_name(field_name)
    if not target or target in _seen or _depth > _MAX_HOPS:
        return set()
    seen = _seen | {target}
    values: set = set()

    initial = model.initial.get(target)
    if initial is not None:
        values.add(str(initial))

    for receiver, source, _line in _moves_of(program):
        if base_name(receiver) != target:
            continue
        source = source.strip()
        lit = _literal(source)
        if lit is not None:
            values.add(lit)
            continue
        sub = _SUBSCRIPT.match(source)
        if sub:
            values |= _table_literal_pool(model, sub.group(1))
            continue
        values |= _field_values(program, model, source, _depth=_depth + 1,
                                _seen=seen)
    return values


def _resolve_program_operand(operand: str, program, model, names: set):
    """`(candidate program names, how)` for one `PROGRAM(...)` operand."""
    operand = operand.strip()
    lit = _literal(operand)
    if lit is not None:
        return {lit} & names, "literal"
    sub = _SUBSCRIPT.match(operand)
    if sub:
        return _table_literal_pool(model, sub.group(1)) & names, "table"
    name = base_name(operand)
    how = "constant" if name in model.initial else "writer-harvest"
    return _field_values(program, model, name) & names, how


# --------------------------------------------------------------------------
# The call graph itself.
# --------------------------------------------------------------------------

def call_edges_from(corpus: dict) -> list:
    """`CallEdge` list from an already-loaded corpus (see `load_corpus`)."""
    names = set(corpus)
    edges: list = []
    for caller, program in corpus.items():
        model = program.model
        for stmt in _iter_all(program):
            if stmt.get("type") != "EXEC":
                continue
            body = stmt.get("attributes", {}).get("body", "")
            if not _CICS.search(body):
                continue
            verb = _XCTL_LINK.search(body)
            if not verb:
                continue
            operand = _balanced_operand(body, _PROGRAM_KW)
            if operand is None:
                continue
            commarea = _balanced_operand(body, _COMMAREA_KW)
            targets, how = _resolve_program_operand(operand, program, model, names)
            for callee in sorted(targets):
                edges.append(CallEdge(caller, callee, stmt.get("line_start", 0),
                                      verb.group(1).upper(), how,
                                      commarea.strip() if commarea else ""))
    return edges


def call_edges(corpus_dir: str, copybooks: str | None = None) -> list:
    """`EXEC CICS XCTL`/`LINK PROGRAM(...)` edges across every `.cbl` in
    `corpus_dir`, resolved to real program names - literal, constant,
    OCCURS-table or transitive-MOVE - and nothing else.
    """
    return call_edges_from(load_corpus(corpus_dir, copybooks))


def predecessors_of(edges: list, target: str) -> list:
    target = target.upper()
    return [e for e in edges if e.callee == target]


# --------------------------------------------------------------------------
# The certifier: for a missing direction gated on a commarea field, can any
# predecessor have produced the value it needs?
# --------------------------------------------------------------------------

def _commarea_field_names(model, copybook_basenames: set) -> set:
    if not copybook_basenames:
        return set()
    return {name for name, origin in model.origin.items()
            if os.path.basename(origin or "").upper() in copybook_basenames}


def _commarea_copybooks(predecessors: list, corpus: dict, target_model) -> set:
    """Which copybook(s) declare the record(s) named in T's callers'
    COMMAREA operands - the evidence for what "commarea field" means for
    this program, read off the source rather than assumed.
    """
    names: set = set()
    for edge in predecessors:
        if not edge.commarea:
            continue
        data_name = base_name(edge.commarea)
        origin = target_model.origin.get(data_name)
        if not origin:
            caller = corpus.get(edge.caller)
            if caller is not None:
                origin = caller.model.origin.get(data_name)
        if origin:
            names.add(os.path.basename(origin).upper())
    return names


def _classify_direction(branch, direction: bool, model, commarea_fields: set,
                        names: frozenset):
    """`(field, required_value)` if this direction is a single equality gate
    on a commarea field, `(field, None)` if it is a gate on some other field
    (out of scope: not commarea), or `(None, None)` if the condition is not
    a shape this certifier reasons about at all (not a single `IF`
    comparison against a resolvable constant).
    """
    if branch.kind != "IF":
        return None, None
    try:
        alternatives = condition_atoms(branch.condition, names=names)
    except Exception:                                          # noqa: BLE001
        return None, None
    if len(alternatives) != 1 or len(alternatives[0]) != 1:
        return None, None
    atom = alternatives[0]
    atom = atom[0]
    if atom.op not in ("=", "!="):
        return None, None
    # This atom's truth is what makes the IF's TRUE arm run; the FALSE arm
    # runs on its negation. A single required value only exists for the arm
    # that corresponds to equality.
    wants_equal = direction if atom.op == "=" else not direction
    if not wants_equal:
        return None, None
    lhs, rhs = atom.lhs, atom.rhs
    if lhs.kind == "var" and rhs.kind in ("var", "const"):
        field_term, other = lhs, rhs
    elif rhs.kind == "var" and lhs.kind == "const":
        field_term, other = rhs, lhs
    else:
        return None, None
    field = base_name(field_term.name)
    if other.kind == "const":
        required = other.value
    else:
        required = model.initial.get(base_name(other.name))
        if required is None:
            return None, None
    if field not in commarea_fields:
        return field, None
    return field, str(required)


def certify(program_path: str, copybooks: str | None, corpus_dir: str,
           baseline_path: str | None = None) -> dict:
    """Certify every missing direction on `program_path` that a commarea
    field gates, against the real callers found in `corpus_dir`.

    `baseline_path` is a witnesses JSONL (paragraph/ordinal/kind/direction
    rows, the shape `witnesses.write()` produces); everything on this
    program's own decision list that is not in it counts as missing. Without
    one, every direction is examined.
    """
    from .coverage import branches_of

    corpus = load_corpus(corpus_dir, copybooks)
    edges = call_edges_from(corpus)
    target_name = _program_name(program_path)
    target = corpus.get(target_name)
    if target is None:
        target = load_program(program_path, copybooks)
        corpus[target_name] = target
    model = target.model
    predecessors = predecessors_of(edges, target_name)
    commarea_copybooks = _commarea_copybooks(predecessors, corpus, model)
    commarea_fields = _commarea_field_names(model, commarea_copybooks)
    names = frozenset(model.condition_names)

    have: set = set()
    if baseline_path and os.path.isfile(baseline_path):
        with open(baseline_path) as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                have.add((str(row.get("paragraph", "")).upper(),
                         row.get("ordinal", -1), str(row.get("kind", "")).upper(),
                         bool(row.get("direction"))))

    predecessor_names = sorted({e.caller for e in predecessors})
    writer_cache: dict = {}

    def writers_of(field: str, program_name: str) -> list:
        key = (field, program_name)
        if key not in writer_cache:
            prog = corpus.get(program_name)
            writer_cache[key] = sorted(_field_values(prog, prog.model, field)) \
                if prog is not None else []
        return writer_cache[key]

    directions: list = []
    for branch in branches_of(target):
        for direction in (True, False):
            key = (branch.paragraph, branch.ordinal, branch.kind, direction)
            if key in have:
                continue
            row = {"paragraph": branch.paragraph, "ordinal": branch.ordinal,
                   "kind": branch.kind, "direction": direction,
                   "condition": branch.condition}
            field, required = _classify_direction(branch, direction, model,
                                                   commarea_fields, names)
            if field is None:
                continue                       # not a shape this tool reasons about
            if required is None:
                row["verdict"] = "not-commarea-gated"
                row["field"] = field
                directions.append(row)
                continue

            row["field"], row["required_value"] = field, required
            row["predecessors_checked"] = predecessor_names
            writers_found = {p: writers_of(field, p) for p in predecessor_names}
            row["writers_found"] = writers_found
            producible_by = [p for p in predecessor_names
                             if required in writers_found[p]]
            if producible_by:
                row["verdict"] = "producible-by"
                row["by"] = producible_by
            else:
                row["verdict"] = "caller-unreachable"
                # Corroborating, not load-bearing: which program(s) anywhere
                # in the corpus *do* write this value into this field, for a
                # human reading the certificate. None of T's predecessors is
                # one of them, or this branch would have been "producible-by".
                row["value_producers_in_corpus"] = sorted(
                    name for name in corpus if name != target_name
                    and required in writers_of(field, name))
            directions.append(row)

    return {
        "program": target_name,
        "edges_in": [e.to_dict() for e in predecessors],
        "commarea_copybooks": sorted(commarea_copybooks),
        "corpus_programs": len(corpus),
        "corpus_edges_total": len(edges),
        "directions": directions,
    }
