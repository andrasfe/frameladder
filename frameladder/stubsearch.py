"""Stage the operation, not the entry state: the stub axis, searched backward.

The frontier search edits entry states, and its residual says so: on the
programs it saturates, the directions left over are dominated by ``EVALUATE
WS-RESP-CD / WHEN DFHRESP(NOTFND)`` arms - a condition on a field an ``EXEC
CICS`` command writes at the call site. No entry value survives to such a
read, so every one of those directions is *opaque* to an entry edit, and the
search retires them without a witness. `sequences.fault_worlds` already
answers this for files - "the READ fails at position k" is an outcome list -
but the EXEC axis had no equivalent, and a world default (`populated`,
`empty`) fixes one answer for the whole run: every command succeeds, or every
command finds nothing. A run where the account lookup succeeds and the
cross-reference lookup then fails was not expressible at all.

So this module works the problem backward, from the unwitnessed direction:

* **Which field the condition tests** comes from the condition's own atoms -
  an EVALUATE subject, an IF comparison, a level-88 resolved to its parent.
* **Which operation writes it** comes from provenance: a `STUB` writer
  visible at the branch, matched on the discriminators the source names
  (``DATASET(...)``, ``MAP(...)``). Never from the variable's name.
* **Which values to stage** come from the program first - the WHEN arms name
  the codes it distinguishes, and OTHER is their complement - then from
  `faults`, which only offers a vocabulary where the source put the field in
  that channel.
* **When a field is not stub-written**, one level of `establishing_writes`
  is chased: `IF CONF-PAY-YES` is not about a stub, but the `SET` that
  establishes it is guarded by a comparison on a screen field the terminal
  RECEIVE delivers, and that one is. Fields nothing writes fall back to an
  entry edit, which costs one run to be wrong about.

A candidate is a *recipe*: a base run that already got near the branch - the
witness of the opposite direction, a witness from the same or a calling
paragraph, the direction's own derived plan - with the staged outcome series
merged over its stubs. The series is transient by default (the operation
fails once, at position 1 or 2, and succeeds either side) because a permanent
failure usually ends the run at the handler; the permanent form is tried
last. Every candidate is executed through the battery's own deduplicating
`run()`, so a direction is only ever credited from a fresh interpreter run of
the exact recipe the ledger stores - the same bar every other phase meets.

The search is passes-to-fixpoint: a direction witnessed on one pass is a base
recipe for a deeper one on the next, which is what lets a never-entered
paragraph's arms open up once the guard admitting the paragraph is cracked.
"""

from __future__ import annotations

from .conditions import condition_atoms
from .faults import codes_for
from .heuristics import complement_value
from .ir import flip, holds, parse_term
from .lift import _wanted
from .provenance import _CICS_SELECTORS

# Bounded fan-out, everywhere. The budget is runs, and a single direction
# must not be able to spend it all: the caps below give one direction at
# most a few dozen candidates before the search moves on.
MAX_ALTERNATIVES = 4       # ways to satisfy the condition
MAX_OPTIONS_PER_ATOM = 3   # deliveries per conjunct
MAX_PROPOSALS = 6          # combined action sets per alternative
MAX_OPS = 2                # distinct writing operations to stage
MAX_BASES = 8              # base recipes to stage over
ESTABLISH_DEPTH = 2        # levels of establishing-write chasing
PER_DIRECTION_CAP = 96     # runs one direction may spend per pass


# --------------------------------------------------------------------------
# What each decision tests, indexed once
# --------------------------------------------------------------------------

def branch_index(program) -> dict:
    """``(paragraph, ordinal, kind) -> what taking it either way requires``.

    `coverage.branches_of` names the decisions; this keeps what they need:
    an IF keeps its condition, a WHEN arm keeps its EVALUATE's subject and
    the full ordered arm list - because arm *i* is only evaluated after arms
    before it failed, so its False direction needs a value that fails them
    too - and a conditional phrase keeps the operation it hangs off.
    """
    out: dict = {}

    def walk(stmt, para, parent_text):
        kind = stmt.get("type", "")
        attrs = stmt.get("attributes", {})
        line = stmt.get("line_start", 0)
        if kind == "IF":
            out[(para, stmt.get("ordinal", -1), "IF")] = {
                "kind": "IF", "para": para, "line": line,
                "condition": attrs.get("condition", "")}
        elif kind in ("EVALUATE", "SEARCH"):
            subject = attrs.get("subject", "")
            arms = [c for c in stmt.get("children") or []
                    if c.get("type") == "WHEN"]
            values = [a.get("attributes", {}).get("value", "") for a in arms]
            for index, arm in enumerate(arms):
                out[(para, arm.get("ordinal", -1), "WHEN")] = {
                    "kind": "WHEN", "para": para,
                    "line": arm.get("line_start", line), "subject": subject,
                    "value": values[index], "index": index, "arms": values}
        elif kind == "PHRASE":
            out[(para, stmt.get("ordinal", -1), "PHRASE")] = {
                "kind": "PHRASE", "para": para, "line": line,
                "phrase": attrs.get("phrase", ""), "op_text": parent_text}
        elif kind.startswith("PERFORM") and (attrs.get("condition")
                                             or attrs.get("varying")):
            out[(para, stmt.get("ordinal", -1), "LOOP")] = {
                "kind": "LOOP", "para": para, "line": line,
                "condition": attrs.get("condition")
                or attrs.get("varying", "")}
        for child in stmt.get("children") or []:
            walk(child, para, stmt.get("text", "") or parent_text)

    for para in program.paragraphs:
        for stmt in para.get("statements", []):
            walk(stmt, para["name"], "")
    return out


def caller_index(graph: dict) -> dict:
    """``paragraph -> the call sites with an edge into it``, from the graph
    the analysis already built - PERFORM, GO TO, ALTER and fall-through
    alike. The site carries its guards, and a witness that took the
    innermost of those guards *true* is a run that demonstrably executed
    the call - the one base that is known to enter the paragraph."""
    out: dict = {}
    for _caller, sites in (graph or {}).items():
        for site in sites:
            out.setdefault(site.callee, []).append(site)
    return out


def line_index(index: dict) -> dict:
    """``(paragraph, line) -> (paragraph, ordinal, kind)`` - the join between
    a guard atom's origin, which names a source line, and a ledger key,
    which names an ordinal. Both derived from this program's own statements,
    which is the only join `directions.py` found trustworthy."""
    return {(info["para"], info["line"]): key
            for key, info in index.items()}


# --------------------------------------------------------------------------
# From a direction to requirements: (field, op, value) options
# --------------------------------------------------------------------------

def _const_options(model, name, op, value, extra=()):
    """Concrete values that make ``name op value`` hold, best first."""
    if op == "=":
        return [value]
    out = []
    primary = _wanted(model, name, op, value)
    if primary is not None:
        out.append(primary)
    if op == "!=":
        for candidate in extra:
            if candidate != value and not isinstance(candidate, bool) \
                    and candidate not in out:
                out.append(candidate)
    return out[:MAX_OPTIONS_PER_ATOM]


def _atom_value_holds(atom, value) -> bool:
    """Would this whole-field value satisfy the atom - or any of the
    single-atom alternatives it carries? ``(1:1) = '-'`` arrives with
    ``(1:1) = '+'`` as its alternative, and a value is fine holding
    either."""
    return any(_one_atom_holds(a, value)
               for a in [atom] + list(atom.alternatives or ()))


def _one_atom_holds(atom, value) -> bool:
    lhs, rhs = atom.lhs, atom.rhs
    if lhs.kind != "var" or rhs.kind != "const" or isinstance(rhs.value, bool):
        return True                       # not checkable; do not veto
    piece = value
    if lhs.refmod:
        try:
            start = int(str(lhs.refmod[0]).strip())
            length = int(str(lhs.refmod[1]).strip()) if lhs.refmod[1] else 1
        except (TypeError, ValueError):
            return True
        if not isinstance(value, str) or len(value) < start - 1 + length:
            return False
        piece = value[start - 1:start - 1 + length]
    return holds(piece, atom.op, rhs.value)


def _joint_options(model, prov, name, atoms):
    """Whole-field values satisfying every atom of a one-field conjunction.

    A format check is a conjunction of slice conditions on one field -
    ``(1:1)`` a sign, ``(2:8)`` numeric, ``(10:1)`` a point - and no
    per-atom value answers it: a field set to ``'-'`` satisfies the sign
    and nothing else. `provenance._compose_sliced` already built the
    composed candidates; this picks the ones the whole conjunction admits.
    """
    candidates: list = []
    for atom in atoms:
        for _n, _o, value in _atom_options(model, prov, atom, joint=False) or []:
            candidates.append(value)
    candidates.extend(sorted(prov.literals.get(name, ()), key=repr))
    good = []
    for value in dict.fromkeys(candidates):
        if all(_atom_value_holds(atom, value) for atom in atoms):
            good.append((name, "=", value))
    return good[:MAX_OPTIONS_PER_ATOM] or None


def _atom_options(model, prov, atom, joint=True):
    """``[(field, '=', value)]`` options satisfying one atom, or None.

    None means the atom is not resolvable to a settable value here - a
    comparison between two fields, an intrinsic - which weakens the
    conjunction rather than failing it: the base recipe may satisfy it
    already, and one run finds out.
    """
    candidates = [atom] + [a for a in (atom.alternatives or ())]
    out = []
    for a in candidates:
        lhs, rhs, op = a.lhs, a.rhs, a.op
        if rhs.kind == "var" and lhs.kind == "const":
            lhs, rhs = rhs, lhs
            op = flip(op)
        if lhs.kind != "var" or rhs.kind != "const":
            continue
        if lhs.refmod and joint and not isinstance(rhs.value, bool):
            # A slice condition wants a whole-field value whose slice
            # satisfies it; the composed candidates are where those live.
            found = _joint_options(model, prov, lhs.name, [a])
            if found:
                out.extend(found)
            continue
        if isinstance(rhs.value, bool):
            entry = model.condition_names.get(lhs.name)
            if not entry:
                continue
            parent, raw = entry
            consts = [parse_term(v).value for v in raw]
            consts = [c for c in consts if not isinstance(c, bool)]
            if not consts:
                continue
            hold = (op == "=") == bool(rhs.value)
            if hold:
                out.extend((parent, "=", c) for c in consts[:2])
            else:
                other = complement_value(parent, model.pic_of(parent), consts)
                if other is not None:
                    out.append((parent, "=", other))
            continue
        literals = sorted(prov.literals.get(lhs.name, ()), key=repr)
        for value in _const_options(model, lhs.name, op, rhs.value,
                                    extra=literals):
            out.append((lhs.name, "=", value))
    if not out:
        return None
    seen, unique = set(), []
    for item in out:
        key = (item[0], repr(item[2]))
        if key not in seen:
            seen.add(key)
            unique.append(item)
    return unique[:MAX_OPTIONS_PER_ATOM]


def _when_options(program, prov, info, want):
    """Requirement groups for one EVALUATE arm direction."""
    model = program.model
    subject = parse_term(info["subject"])
    raw = (info["value"] or "").strip()
    truth = (info["subject"] or "").strip().upper()
    if truth in ("TRUE", "FALSE"):
        # `EVALUATE TRUE / WHEN <condition>` matches when the condition
        # holds; `EVALUATE FALSE` when it does not.
        negate = want if truth == "FALSE" else not want
        out = []
        for alt in condition_atoms(
                raw, negate=negate,
                names=frozenset(model.condition_names))[:MAX_ALTERNATIVES]:
            groups = []
            for atom in alt:
                opts = _atom_options(model, prov, atom)
                if opts is not None:
                    groups.append(opts)
            out.append(groups)
        return out
    if subject.kind != "var":
        return []
    name = subject.name
    arm_consts = []
    for value in info["arms"]:
        text = (value or "").strip()
        if text.upper() in ("OTHER", "ANY"):
            arm_consts.append(None)
            continue
        term = parse_term(text)
        arm_consts.append(term.value if term.kind == "const" else None)
    named = [c for c in arm_consts if c is not None]
    own = arm_consts[info["index"]] if info["index"] < len(arm_consts) else None
    other_arm = raw.upper() in ("OTHER", "ANY")

    def family_complement(exclude):
        for code in codes_for(name, model):
            if code not in exclude:
                return code
        return complement_value(name, model.pic_of(name), list(exclude))

    options = []
    if other_arm:
        if want:
            candidate = family_complement(named)
            if candidate is not None:
                options.append((name, "=", candidate))
        else:
            options.extend((name, "=", c) for c in named[:2])
    elif own is not None:
        if want:
            options.append((name, "=", own))
        else:
            earlier = [c for c in arm_consts[: info["index"] + 1]
                       if c is not None]
            later = [c for c in arm_consts[info["index"] + 1:]
                     if c is not None and c not in earlier]
            options.extend((name, "=", c) for c in later[:2])
            candidate = family_complement(named)
            if candidate is not None and all(candidate != c for _n, _o, c
                                             in options):
                options.append((name, "=", candidate))
    if not options:
        return []
    return [[options[:MAX_OPTIONS_PER_ATOM]]]


_PHRASE_CODES = {"at_end": "10", "not_at_end": "00",
                 "invalid_key": "23", "not_invalid_key": "00"}


def _phrase_options(program, info, want):
    """A conditional phrase is a decision on the operation's own status."""
    from .provenance import op_key
    from .ir import norm
    key = op_key(norm(info.get("op_text") or ""))
    if ":" not in key:
        return []
    status = program.model.file_status.get(key.rsplit(":", 1)[-1], "")
    if not status:
        return []
    phrase = info.get("phrase", "")
    code = _PHRASE_CODES.get(phrase)
    if code is None:
        return []
    if not want:
        code = _PHRASE_CODES.get(
            phrase[4:] if phrase.startswith("not_") else "not_" + phrase)
    if code is None:
        return []
    return [[[(status, "=", code)]]]


def requirement_groups(program, prov, info, want):
    """Alternatives, each a conjunction of requirement groups.

    A group is a list of ``(field, '=', value)`` options - satisfying any one
    satisfies the conjunct. Unresolvable conjuncts are dropped rather than
    failing the alternative: the base recipe may already satisfy them.
    """
    model = program.model
    kind = info["kind"]
    if kind in ("IF", "LOOP"):
        alts = condition_atoms(info["condition"], negate=not want,
                               names=frozenset(model.condition_names))
        out = []
        for alt in alts[:MAX_ALTERNATIVES]:
            groups = []
            for atom in alt:
                opts = _atom_options(model, prov, atom)
                if opts is not None:
                    groups.append(opts)
            out.append(groups)
        return out
    if kind == "WHEN":
        return _when_options(program, prov, info, want)
    if kind == "PHRASE":
        return _phrase_options(program, info, want)
    return []


# --------------------------------------------------------------------------
# From a requirement to deliveries: stage an operation, or edit the entry
# --------------------------------------------------------------------------

def _site_when(prov, writer) -> dict:
    """The when-clause staging this writer's own call site, and only clauses
    the statement itself carries. A discriminator read from the *state* can
    silently fail to match at run time and the staged outcome then never
    fires; a ``DATASET(...)``/``MAP(...)`` clause is a property of the
    statement and matches deterministically."""
    return {k: v for k, v in prov.discriminators(writer.literals,
                                                 writer.op_key).items()
            if k in _CICS_SELECTORS}


# An operation that ends the task cannot hand a value back to the code
# after it; staging one produces a recipe that stops exactly where the
# outcome was supposed to matter.
_TERMINATING = ("EXEC:CICS:RETURN", "EXEC:CICS:XCTL", "EXEC:CICS:ABEND")


def deliveries(program, prov, at, name, value, depth=0, seen=frozenset()):
    """Ways to make ``name = value`` hold at ``at``: each a list of actions.

    An action is ``("stub", op_key, when, field, value, paragraph)`` or
    ``("entry", field, value)``. Stub writers visible at the read come
    first; a field with none is chased one level through the write that
    would establish the value. The entry edit is always offered last: a
    stub-written field can *also* arrive from the entry state - a screen
    field is re-delivered from it at every RECEIVE - and on a route that
    never invokes the operation the entry edit is the only form that
    lands. It costs one run to be wrong about.
    """
    model = program.model
    options: list = []
    writers = prov.visible(name, at)
    stub_writers = [w for w in writers if w.kind == "STUB"
                    and w.op_key not in _TERMINATING]
    staged = set()
    for writer in stub_writers:
        when = _site_when(prov, writer)
        identity = (writer.op_key, tuple(sorted(when.items())))
        if identity in staged:
            continue
        staged.add(identity)
        options.append([("stub", writer.op_key, when, name, value,
                         writer.para)])
        if len(staged) >= MAX_OPS:
            break
    # A MOVE is a rename: when the reaching definition copies the field
    # from somewhere else - a screen field refreshed from a saved record on
    # one route - the value must be planted at the *origin* the producer
    # walk names, because anything placed at the destination is overwritten
    # by the copy itself.
    try:
        producer = prov.producer(name, at)
    except Exception:                                        # noqa: BLE001
        producer = None
    if producer is not None and producer.var \
            and producer.var.upper() != name.upper():
        if producer.kind == "input":
            options.append([("entry", producer.var, value)])
        elif producer.kind == "stub" \
                and producer.op_key not in _TERMINATING:
            when = {k: v for k, v in (producer.discriminators or {}).items()
                    if k in _CICS_SELECTORS}
            options.append([("stub", producer.op_key, when, producer.var,
                             value, producer.site or "")])
    if not stub_writers and depth < ESTABLISH_DEPTH and name not in seen:
        for writer in prov.establishing_writes(name, "=", value)[:2]:
            if not writer.guards:
                continue
            groups = []
            for atom in writer.guards:
                opts = _atom_options(model, prov, atom)
                if opts is not None:
                    groups.append(opts)
            if not groups:
                continue
            options.extend(combine(program, prov,
                                   (writer.para, writer.line), groups,
                                   depth + 1, seen | {name}))
    options.append([("entry", name, value)])
    return options[:MAX_PROPOSALS]


def _avoidance_groups(program, prov, name, value, limit=2):
    """Requirement groups steering around the writes that would break
    ``name = value`` on the way there.

    The validation-paragraph shape: a dozen guarded ``MOVE 'Y' TO
    WS-ERR-FLG`` sit between the entry and the read, and holding the flag
    off means none of them ran. Negating the innermost guard of each is
    what `blocking_writes` exists for, bounded here so one flag with many
    writers cannot flood the conjunction.
    """
    from .ir import negate_atom
    model = program.model
    out = []
    for writer in prov.blocking_writes(name, "=", value)[:limit]:
        if not writer.guards:
            continue
        options = []
        for negated in negate_atom(writer.guards[-1]):
            opts = _atom_options(model, prov, negated)
            if opts:
                options.extend(opts)
        if options:
            out.append(options[:MAX_OPTIONS_PER_ATOM])
    return out


def combine(program, prov, at, groups, depth=0, seen=frozenset()):
    """Action lists satisfying every group in a conjunction, fan-out capped."""
    expanded = list(groups)
    for options in groups[:2]:
        if options:
            name, _op, value = options[0]
            expanded.extend(_avoidance_groups(program, prov, name, value))
    proposals = [[]]
    for options in expanded:
        ways = []
        for _name, _op, value in options[:MAX_OPTIONS_PER_ATOM]:
            ways.extend(deliveries(program, prov, at, _name, value,
                                   depth, seen))
        if not ways:
            continue
        proposals = [p + w for p in proposals
                     for w in ways[:MAX_OPTIONS_PER_ATOM]][:MAX_PROPOSALS]
    return [p for p in proposals if p]


def _site_ordinal(program, caller: str, line: int):
    """The ordinal of the PERFORM at ``line`` in ``caller``, if findable."""
    para = program.paragraph(caller)
    found = [None]

    def walk(stmt):
        if stmt.get("type") == "PERFORM" \
                and stmt.get("line_start") == line \
                and found[0] is None:
            found[0] = stmt.get("ordinal")
        for child in stmt.get("children") or []:
            walk(child)

    for stmt in (para or {}).get("statements", []):
        walk(stmt)
    return found[0]


def _route_groups(program, prov, info, callers, depth: int = 0,
                  seen: frozenset = frozenset()):
    """Requirement groups that admit the branch's paragraph, per route.

    The condition's own requirements say nothing about *getting there*: a
    staged screen field is worthless on a run whose attention key routes
    past the paragraph that reads it. A route is assembled from evidence at
    every hop: the call site's guards (what admits the call), the caller's
    own survival gauntlet up to the call (`derail_groups` - an unguarded
    PERFORM is only reached on a task where the validation before it
    passed), and then the caller's own route, recursively. Bounded to three
    hops and two sites per hop.
    """
    model = program.model
    out = [[]]
    if depth >= 3:
        return out
    for site in (callers or {}).get(info["para"], [])[:2]:
        if site.caller in seen or site.caller == info["para"]:
            continue
        groups = []
        for atom in site.guards or ():
            opts = _atom_options(model, prov, atom)
            if opts is not None:
                groups.append(opts)
        cutoff = _site_ordinal(program, site.caller, site.line)
        if cutoff is not None:
            groups.extend(derail_groups(
                program, prov, {"para": site.caller, "line": site.line},
                cutoff))
        deeper = _route_groups(program, prov, {"para": site.caller,
                                               "line": site.line},
                               callers, depth + 1, seen | {info["para"]})
        for onward in deeper[:3]:
            route = groups + onward
            if route:
                out.append(route)
    return out[:6]


def _restart_paragraphs(prov) -> set:
    """Paragraphs that end the task when performed.

    Evidence, not naming: a paragraph is a task-ender because its own
    statements issue ``EXEC CICS RETURN`` / ``XCTL`` / ``ABEND`` - the ops
    `provenance` already indexed per paragraph - never because it is called
    SEND-something.
    """
    enders = set(_TERMINATING) | {"EXEC:CICS:RETURN"}
    return {para for para, ops in (getattr(prov, "operations", {}) or {}).items()
            if ops & enders}


def _body_restarts(children, restarts) -> bool:
    """Does this arm's body hand the task back, unconditionally?

    Only unguarded direct statements count: a restart behind a further IF is
    not certain, and asserting its guard's negation would be a guess.
    """
    for child in children or []:
        kind = child.get("type", "")
        if kind == "PERFORM":
            target = (child.get("attributes", {}).get("target") or "").strip()
            head = target.split()[0].upper() if target else ""
            if head in restarts:
                return True
        elif kind == "EXEC":
            from .ir import norm
            from .provenance import op_key
            if op_key(norm(child.get("text", ""))) in (
                    set(_TERMINATING) | {"EXEC:CICS:RETURN"}):
                return True
    return False


def _effective_bodies(arms) -> list:
    """Body per WHEN arm, honouring shared bodies.

    ``WHEN 'N' / WHEN 'n' / <body>`` parses as empty-bodied arms followed by
    the arm that carries the statements; matching any of them runs that one
    body.
    """
    bodies, pending = [], []
    for arm in arms:
        children = arm.get("children") or []
        pending.append(arm)
        if children:
            bodies.extend((a, children) for a in pending)
            pending = []
    bodies.extend((a, []) for a in pending)
    order = {id(a): body for a, body in bodies}
    return [(a, order.get(id(a), [])) for a in arms]


def derail_groups(program, prov, info, ordinal, depth=0):
    """Requirements that keep the run alive to the decision.

    A validation paragraph is a run of decisions whose failing arms hand the
    task straight back - ``MOVE 'Y' TO WS-ERR-FLG / PERFORM SEND-...`` where
    the SEND paragraph issues ``EXEC CICS RETURN`` - so a decision late in
    the run is only ever evaluated on a task where every earlier gauntlet
    arm went the surviving way. Those survival requirements are readable off
    the source: for each earlier decision whose arm restarts the task, the
    subject must hold a value that misses it. One level of PERFORM is
    followed, because the gauntlet ahead of an ``EVALUATE CONFIRMI`` is
    typically a performed sibling, not an inline one.
    """
    model = program.model
    names = frozenset(model.condition_names)
    restarts = _restart_paragraphs(prov)
    para = program.paragraph(info["para"])
    if para is None:
        return []
    out: list = []

    # One value per field must survive *every* check the route makes on it:
    # a screen field is tested non-blank by one statement, numeric by the
    # next and for its sign by a third, and a value chosen per statement
    # satisfies one check while failing its neighbours. Atoms are pooled by
    # field across the whole scan and resolved once at the end, against the
    # union.
    field_atoms: dict = {}
    loose_groups: list = []

    def negation_groups(condition, negate=True):
        from .graph import first_with_alternatives
        # `first_with_alternatives` keeps the other single-atom ways to
        # satisfy the condition on the atom itself: the negation of a sign
        # check is `(1:1) = '-' OR (1:1) = '+'`, and pooling only the first
        # disjunct would reject every composed value carrying the other.
        atoms = first_with_alternatives(
            condition_atoms(condition, negate=negate, names=names))
        for atom in atoms:
            if atom.lhs.kind == "var" and atom.rhs.kind == "const" \
                    and not isinstance(atom.rhs.value, bool):
                field_atoms.setdefault(atom.lhs.name, []).append(atom)
            else:
                opts = _atom_options(model, prov, atom)
                if opts is not None:
                    loose_groups.append(opts)
        return []

    def scan(stmts, cutoff, level):
        for stmt in stmts:
            own = stmt.get("ordinal", -1)
            if cutoff is not None and own >= 0 and own >= cutoff:
                return
            kind = stmt.get("type", "")
            attrs = stmt.get("attributes", {})
            if kind == "PERFORM" and level == 0:
                target = (attrs.get("target") or "").strip()
                head = target.split()[0].upper() if target else ""
                callee = program.paragraph(head)
                if callee is not None and head not in restarts \
                        and not attrs.get("condition"):
                    scan(callee.get("statements", []), None, level + 1)
            elif kind == "EVALUATE":
                subject = parse_term(attrs.get("subject", ""))
                truth = (attrs.get("subject") or "").strip().upper()
                arms = [c for c in stmt.get("children") or []
                        if c.get("type") == "WHEN"]
                unsafe_consts, safe_consts, other_restarts = [], [], False
                safe_condition = None
                for arm, body in _effective_bodies(arms):
                    raw = (arm.get("attributes", {}).get("value") or "").strip()
                    bad = _body_restarts(body, restarts)
                    if truth in ("TRUE", "FALSE"):
                        if raw.upper() in ("OTHER", "ANY"):
                            other_restarts = other_restarts or bad
                        elif bad:
                            out.extend(negation_groups(
                                raw, negate=(truth == "TRUE")))
                        elif safe_condition is None:
                            safe_condition = raw
                        continue
                    if raw.upper() in ("OTHER", "ANY"):
                        other_restarts = other_restarts or bad
                        continue
                    term = parse_term(raw)
                    if term.kind != "const":
                        continue
                    (unsafe_consts if bad else safe_consts).append(term.value)
                if truth in ("TRUE", "FALSE") and other_restarts \
                        and safe_condition is not None:
                    # WHEN OTHER hands the task back, so surviving means
                    # *some* arm matches - assert the first that does not.
                    out.extend(negation_groups(
                        safe_condition, negate=(truth != "TRUE")))
                if subject.kind == "var" and unsafe_consts:
                    options = [(subject.name, "=", c) for c in safe_consts]
                    if not other_restarts:
                        extra = complement_value(
                            subject.name, model.pic_of(subject.name),
                            unsafe_consts + safe_consts)
                        if extra is not None:
                            options.append((subject.name, "=", extra))
                    if options:
                        out.append(options[:MAX_OPTIONS_PER_ATOM])
            elif kind == "IF":
                then_part = [c for c in stmt.get("children") or []
                             if c.get("type") != "ELSE"]
                else_part = [c for e in stmt.get("children") or []
                             if e.get("type") == "ELSE"
                             for c in e.get("children") or []]
                if _body_restarts(then_part, restarts):
                    out.extend(negation_groups(attrs.get("condition", "")))
                elif _body_restarts(else_part, restarts):
                    out.extend(negation_groups(attrs.get("condition", ""),
                                               negate=False))
                scan(then_part, cutoff, level)
            if kind in ("EVALUATE", "SEARCH"):
                for arm in stmt.get("children") or []:
                    scan(arm.get("children") or [], cutoff, level)

    scan(para.get("statements", []), ordinal, 0)
    for field, atoms in field_atoms.items():
        opts = _joint_options(model, prov, field, atoms) \
            if len(atoms) > 1 else _atom_options(model, prov, atoms[0])
        if opts is not None:
            out.append(opts)
    out.extend(loose_groups)
    seen, unique = set(), []
    for group in out:
        key = tuple(sorted((n, repr(v)) for n, _o, v in group))
        if key not in seen:
            seen.add(key)
            unique.append(group)
    return unique[:24]


def proposals_for(program, prov, info, want, callers=None, ordinal=None):
    """Every staged-action set worth one run for this direction, best first.

    The bare condition requirements come first - the cheap case where a base
    run already stands at the decision. Then the same requirements joined
    with the survival gauntlet (`derail_groups`), for the decision no task
    stays alive long enough to evaluate; then joined with each call site's
    admitting guards, for the direction whose paragraph no base enters.
    """
    at = (info["para"], info["line"])
    gauntlet = derail_groups(program, prov, info, ordinal) \
        if ordinal is not None else []
    extensions = [[]]
    if gauntlet:
        extensions.append(gauntlet)
    for route in _route_groups(program, prov, info, callers)[1:]:
        extensions.append(route)
        if gauntlet:
            extensions.append(gauntlet + route)
    out = []
    for extension in extensions:
        for groups in requirement_groups(program, prov, info, want):
            if not groups:
                continue
            out.extend(combine(program, prov, at, groups + extension))
    seen, unique = set(), []
    for proposal in out:
        key = tuple(sorted(repr(a) for a in proposal))
        if key not in seen:
            seen.add(key)
            unique.append(proposal)
    # One representative per *shape* first - the set of fields an action
    # set touches - then the value variations. Six value spellings of one
    # shape ahead of the first sighting of a richer shape is how a
    # per-direction cap gets spent without ever trying the combination
    # that works.
    shapes, first, rest = set(), [], []
    for proposal in unique:
        shape = frozenset(action[1] if action[0] == "entry" else action[3]
                          for action in proposal)
        if shape in shapes:
            rest.append(proposal)
        else:
            shapes.add(shape)
            first.append(proposal)
    return (first + rest)[:MAX_PROPOSALS * 6]


# --------------------------------------------------------------------------
# From a proposal to recipes: a base run, with the series merged over it
# --------------------------------------------------------------------------

def staged_recipes(model, base, actions):
    """Concrete recipes for one action set over one base run.

    Three series per stub action, in the order the fault-world machinery
    already measured as most useful: fail on the first matching call, fail on
    the second (the position an entry state cannot express at all), fail on
    every call. The failing operation succeeds either side - its terminal is
    the channel's success code - so the fault is transient, which is the form
    that exercises the code *after* the handler.
    """
    state0, world, stubs0, terminals0 = base
    variants = ("at1", "at2", "always")
    if not any(action[0] == "stub" for action in actions):
        variants = ("at1",)
    for variant in variants:
        state = dict(state0 or {})
        stubs = {k: [dict(e) for e in v] for k, v in (stubs0 or {}).items()}
        terminals = {k: dict(v) for k, v in (terminals0 or {}).items()}
        # Two staged fields on one operation are one delivery, not two: a
        # RECEIVE fills every field of the screen in one call, and emitting
        # one entry each would hand back the first field and then the
        # second on a call that never comes - the same defect
        # `Plan.stub_plan` documents.
        merged: dict = {}
        for action in actions:
            if action[0] == "entry":
                _, name, value = action
                state[name] = value
                continue
            _, op_key, when, name, value, _site = action
            slot = (op_key, tuple(sorted(when.items())))
            merged.setdefault(slot, {})[name] = value
        for (op_key, when_items), fields in merged.items():
            when = dict(when_items)
            successes = {name: codes_for(name, model, op_key)[0]
                         for name in fields
                         if codes_for(name, model, op_key)}
            existing = stubs.get(op_key)
            if existing:
                # The base recipe already stages this operation - a plan's
                # own RECEIVE payload, a sequence world's records - and
                # replacing its entries throws away the staging that made
                # the base reach anywhere. Overlay the fields instead: the
                # fault lands at the variant's position, the base's other
                # fields keep arriving.
                spot = 1 if variant == "at2" and len(existing) > 1 else 0
                for index, entry in enumerate(existing):
                    extra = fields if (variant == "always" or index == spot) \
                        else successes
                    entry["set"] = dict(entry.get("set") or {}, **extra)
                if variant == "always":
                    terminals[op_key] = dict(terminals.get(op_key) or {},
                                             **fields)
                elif successes:
                    terminals[op_key] = dict(terminals.get(op_key) or {},
                                             **successes)
                continue
            fault = {"when": when, "set": dict(fields), "seq": 0,
                     "inferred": False}
            if variant == "at2":
                prefix = {"when": dict(when), "set": dict(successes),
                          "seq": 0, "inferred": False}
                entries = [prefix, dict(fault, seq=1)]
            else:
                entries = [fault]
            stubs[op_key] = entries
            if variant == "always":
                terminals[op_key] = dict(fields)
            elif successes:
                terminals[op_key] = dict(successes)
            else:
                terminals.pop(op_key, None)
        yield state, world, stubs, terminals


def admitting_keys(paragraph, callers, lines) -> list:
    """Ledger keys whose True witness demonstrably entered ``paragraph``.

    A call site's guards name the decisions that admit it, each with the
    source line it lives on; the join to a ledger key goes through the line,
    never through a counted index. The innermost guard comes first - it is
    the one closest to the call.
    """
    per_site = []
    for site in callers.get(paragraph) or []:
        keys = []
        for atom in reversed(list(site.guards or ())):
            origin = getattr(atom, "origin", "") or ""
            para, _sep, line = origin.rpartition(":")
            try:
                branch = lines.get((para, int(line)))
            except ValueError:
                branch = None
            if branch is not None:
                keys.append(branch + (True,))
        per_site.append(keys)
    # Round-robin across sites, so two routes into the paragraph each get
    # their innermost admitting witness before either gets its second.
    out = []
    for rank in range(max((len(k) for k in per_site), default=0)):
        for keys in per_site:
            if rank < len(keys):
                out.append(keys[rank])
    return list(dict.fromkeys(out))


def base_recipes(ledger, key, plan_recipes, callers, lines, op_paras=()):
    """Base runs for one direction, most-evidence-first.

    The witness of the opposite direction demonstrably evaluated this very
    decision. A witness that took a call-site guard into the branch's
    paragraph demonstrably *entered* it. A witness from a paragraph
    containing a staged operation demonstrably *invoked* it - a staged
    outcome fires only on a run that reaches the call, and the first defect
    this phase had was staging terminal input over runs that never ran the
    RECEIVE. The direction's own plan carries the chain gating the solver
    derived; an empty state under each non-bare world is the last resort.
    """
    paragraph, ordinal, kind, want = key
    out, seen = [], set()

    def add(state, world, stubs, terminals):
        identity = (tuple(sorted((k, repr(v)) for k, v in state.items())),
                    world, repr(stubs), repr(terminals))
        if identity in seen:
            return
        seen.add(identity)
        out.append((state, world, stubs, terminals))

    def add_witness(witness_key):
        recipe = ledger.witnesses.get(witness_key)
        if recipe is None:
            return
        payload = recipe.payload()
        add(payload["input_state"], payload["world"], payload["stubs"],
            payload["terminals"])

    add_witness((paragraph, ordinal, kind, not want))
    for witness_key in admitting_keys(paragraph, callers, lines)[:2]:
        add_witness(witness_key)
    for op_para in op_paras:
        if op_para == paragraph:
            continue
        nearby = sorted((k for k in ledger.witnesses if k[0] == op_para),
                        key=lambda k: k[1])
        for witness_key in nearby[:1]:
            add_witness(witness_key)
        for witness_key in admitting_keys(op_para, callers, lines)[:1]:
            add_witness(witness_key)
    plan = (plan_recipes or {}).get(key) \
        or (plan_recipes or {}).get((paragraph, ordinal, kind, not want))
    if plan is not None:
        state, stubs, terminals = plan
        add(dict(state), "populated", stubs, terminals)
    nearby = sorted((k for k in ledger.witnesses if k[0] == paragraph),
                    key=lambda k: abs(k[1] - ordinal))
    for witness_key in nearby[:2]:
        add_witness(witness_key)
    add({}, "populated", None, None)
    add({}, "empty", None, None)
    # A witness verified under `bare` carries a world where every EXEC the
    # route needs comes back unset, so a staged outcome downstream of a
    # successful lookup can never fire from it. The same state under
    # `populated` is a distinct base worth one run.
    for state, world, stubs, terminals in list(out):
        if world != "populated":
            add(state, "populated", stubs, terminals)
    return out[:MAX_BASES + 2]


# --------------------------------------------------------------------------
# The search
# --------------------------------------------------------------------------

def search(program, prov, graph, ledger, run, *, budget: int,
           plan_recipes: dict | None = None, on_witness=None) -> dict:
    """Work the missing list backward through staged outcomes, to fixpoint.

    ``run`` is the battery's crediting closure - a fresh interpreter per
    recipe, deduplicated, folding the trace into the ledger - so nothing is
    credited here except through the same replay every other phase uses.
    ``on_witness`` receives each recipe that witnessed its direction, which
    is how the frontier search downstream gets to start from inside a
    staged world.

    Returns the phase's accounting, negatives included: ``no_proposals``
    counts directions no evidence chain reaches (nothing stub-written,
    nothing establishable, nothing entry-editable), which is the honest
    residual this mechanism cannot speak to.
    """
    from .ledger import missing
    index = branch_index(program)
    callers = caller_index(graph)
    lines = line_index(index)
    stats = {"budget": budget, "runs": 0, "directions_witnessed": 0,
             "no_proposals": 0, "passes": 0}
    no_proposals: set = set()
    progress = True
    while progress and stats["runs"] < budget:
        progress = False
        stats["passes"] += 1
        for branch, want in missing(program, ledger):
            if stats["runs"] >= budget:
                break
            key = (branch.paragraph, branch.ordinal, branch.kind, want)
            info = index.get(key[:3])
            if info is None:
                continue
            proposals = proposals_for(program, prov, info, want,
                                      callers=callers, ordinal=branch.ordinal)
            if not proposals:
                no_proposals.add(key)
                continue
            op_paras = list(dict.fromkeys(
                action[5] for actions in proposals for action in actions
                if action[0] == "stub"))
            bases = base_recipes(ledger, key, plan_recipes, callers, lines,
                                 op_paras=op_paras[:2])
            witnessed = False
            spent = 0
            # Breadth-first over (variant, base, proposal): every proposal
            # is tried at its cheapest staging over every base before any
            # gets its second variant. Depth-first spent the whole
            # per-direction cap exploring variants of the first proposal
            # from ever-worse starting points and never reached the
            # combination that works.
            for variant_index in range(3):
                for base in bases:
                    for actions in proposals:
                        recipes = list(staged_recipes(program.model, base,
                                                      actions))
                        if variant_index >= len(recipes):
                            continue
                        if stats["runs"] >= budget \
                                or spent >= PER_DIRECTION_CAP:
                            break
                        recipe = recipes[variant_index]
                        # A candidate the dedup already refused is free -
                        # only executed runs spend the budget - so a later
                        # pass re-proposing the same recipe costs nothing
                        # and only a fresh base actually runs.
                        if run(*recipe, "stub:%s:%d:%s"
                               % (branch.paragraph, branch.ordinal,
                                  want)) is not None:
                            stats["runs"] += 1
                            spent += 1
                        if key in ledger.witnesses:
                            witnessed = True
                            if on_witness is not None:
                                on_witness(recipe)
                            break
                    if witnessed or spent >= PER_DIRECTION_CAP \
                            or stats["runs"] >= budget:
                        break
                if witnessed or spent >= PER_DIRECTION_CAP \
                        or stats["runs"] >= budget:
                    break
            if witnessed:
                stats["directions_witnessed"] += 1
                progress = True
    stats["no_proposals"] = len(no_proposals)
    return stats
