"""The ladder: lift a target's obligations outwards until they name knobs."""

from __future__ import annotations

import re
from collections import deque

from .conditions import condition_atoms
from .graph import build_graph, chain_via, execution_order, shortest_chain
from .ir import (Atom, Binding, Plan, Producer, Term, flip, holds,
                 negate_atom, parse_term)
from .provenance import Provenance


def rendezvous_value(a: str, b: str, model) -> object:
    """A fresh value to plant at both ends of an equality coupling.

    Any value at all will do - which is exactly the point.  What sampling
    cannot do is put the *same* one in two independent places.
    """
    spec = model.pic.get(a) or model.pic.get(b) or "X(16)"
    if "X" in spec.upper() or "A" in spec.upper():
        m = re.search(r"[XA]\((\d+)\)", spec, re.I)
        width = int(m.group(1)) if m else max(len(spec), 4)
        return "4111111111111111"[:width].ljust(width, "1")
    m = re.search(r"9\((\d+)\)", spec)
    width = int(m.group(1)) if m else 4
    return int("1" * max(1, min(width, 15)))


def witness(op: str, other: Term, domain: set) -> object:
    """A value satisfying ``x op other``."""
    if other.kind != "const":
        return None
    val = other.value
    if op == "=":
        return val
    if op == "!=":
        for cand in sorted(domain, key=repr):
            if cand != val:
                return cand
        if isinstance(val, (int, float)):
            return val + 1
        return "X" if val != "X" else "Y"
    if isinstance(val, (int, float)):
        return {">": val + 1, ">=": val, "<": val - 1, "<=": val}[op]
    for cand in sorted(domain, key=repr):
        if holds(cand, op, val):
            return cand
    return val if op in (">=", "<=") else None


def origin_site(origin: str):
    if not origin or ":" not in origin:
        return None
    para, _, line = origin.rpartition(":")
    para = para.replace("avoid ", "").strip()
    try:
        return para, int(line)
    except ValueError:
        return None


def _resolve_88(atom: Atom, model) -> Atom:
    """``IF ACCT-ACTIVE`` is an obligation on the field the 88 sits under."""
    if atom.rhs.kind == "const" and atom.rhs.value is True and atom.lhs.kind == "var":
        entry = model.condition_names.get(atom.lhs.name)
        if entry:
            parent, values = entry
            for raw in values:
                term = parse_term(raw)
                if term.kind == "const":
                    return Atom(Term("var", name=parent.upper()),
                                atom.op, term, atom.origin)
    return atom


def analyse(program):
    """Graph, execution order and provenance, computed once per program.

    Sweeping a program means planning for every paragraph in it; rebuilding
    the whole index each time turns a seconds-long job into a minutes-long
    one for no gain, since none of it depends on the target.
    """
    cached = getattr(program, "_analysis", None)
    if cached is None:
        graph = build_graph(program)
        order = execution_order(graph, program.paragraph_names[0])
        cached = (graph, Provenance(program, order))
        try:
            program._analysis = cached
        except AttributeError:
            pass
    return cached


def build_plan(program, target: str, *, entry: str | None = None, via=(),
               agent_bindings: dict | None = None, kinds: set | None = None,
               max_rounds: int = 8) -> Plan:
    """Derive a reaching plan for ``target``.

    ``via`` pins the call trace through named frames, so a caller can ask
    for the deep route through a cascade rather than whichever edge
    happens to be shortest.  ``agent_bindings`` are decisions made
    outside this module - by a human or an agent reading the frame - and
    they win over anything the ladder would derive itself.
    """
    graph, prov = analyse(program)
    entry = (entry or program.paragraph_names[0]).upper()
    target = target.upper()
    model = program.model

    path = (chain_via(graph, entry, via, target, kinds=kinds) if via
            else shortest_chain(graph, entry, target, kinds=kinds))
    if path is None:
        return Plan(target, [], [], [], [], [],
                    [(Atom(Term("var", name=target), "=", Term("const", value=True)),
                      "no call chain from %s%s" % (entry, " via " + ",".join(via)
                                                   if via else ""))])

    chain = [entry] + [s.callee for s in path]

    # Deepest frame first: its obligations are the most specific, and pinning
    # them constrains what the shallower frames merely have to preserve.
    atoms = [_resolve_88(a, model) for site in reversed(path) for a in site.guards]

    bindings: list = []
    rendezvous: list = []
    open_obs: list = []
    derived: list = []
    notes: list = []
    assigned: dict = {}
    avoided: dict = {}

    def bind(producer: Producer, value, reason: str, source: str = "ladder",
             atom=None) -> bool:
        prior = assigned.get(producer.slot)
        if prior is not None:
            return prior.value == value
        b = Binding(producer.slot, producer, value, reason, source, atom)
        assigned[producer.slot] = b
        bindings.append(b)
        return True

    def revise(existing: Binding, op: str, const_term) -> bool:
        """Re-open an earlier decision that had another way to be satisfied.

        Obligations are discharged deepest-frame-first, so a shallow frame
        can contradict a choice a deep one already made.  If that earlier
        choice came from an OR with an unused branch, the contradiction is
        not a dead end - it means the wrong branch was taken.
        """
        if existing.source == "agent" or existing.atom is None:
            return False
        for alt in existing.atom.alternatives:
            side = alt.rhs if alt.rhs.kind == "const" else alt.lhs
            if side.kind != "const" or not holds(side.value, op, const_term.value):
                continue
            existing.value = side.value
            existing.reason += "  (revised to %r: %s also had to hold)" % (
                side.value, "%s %s %s" % (existing.producer.var, op, const_term))
            return True
        return False

    # Agent decisions go in first so nothing derived can contradict them.
    for name, value in (agent_bindings or {}).items():
        upper = name.upper()
        producer = prov.producer(upper)
        if producer.kind == "unknown":
            producer = Producer("input", var=upper)
        bind(producer, value, "supplied by agent", source="agent")

    def chain_position(atom) -> int:
        site = origin_site(atom.origin)
        if site and site[0] in chain:
            return chain.index(site[0])
        return len(chain)

    def program_advanced(var: str) -> bool:
        """Does the program itself move this variable on, unconditionally?

        A dispatcher's file selector is set by the program at every step, so
        a chain can need it to hold two different values at two different
        moments. Only the *first* is settable - the entry state - and the
        program produces the rest.
        """
        from .ir import parse_term as _pt
        return any(w.kind == "MOVE" and not w.conditional
                   and _pt(w.source).kind == "const"
                   for w in prov.writers.get(var.upper(), []))

    queue = deque((a, 0) for a in atoms)
    handled: set = set()

    while queue:
        atom, round_no = queue.popleft()
        marker = (str(atom), round_no)
        if marker in handled or round_no > max_rounds:
            continue
        handled.add(marker)
        lhs, rhs = atom.lhs, atom.rhs
        at = origin_site(atom.origin)

        if lhs.kind == "const" and rhs.kind == "const":
            if not holds(lhs.value, atom.op, rhs.value):
                open_obs.append((atom, "constant obligation is false"))
            continue

        # ---- both sides produced: the coupling case ----------------------
        if lhs.kind == "var" and rhs.kind == "var":
            pa, pb = prov.producer(lhs.name, at), prov.producer(rhs.name, at)
            if atom.op != "=":
                if atom.op not in ("<=", ">="):
                    open_obs.append((atom, "strict ordering between two produced "
                                           "values (%s, %s)" % (pa.slot, pb.slot)))
                continue
            if pa.kind == "literal" or pb.kind == "literal":
                lit, other = (pa, pb) if pa.kind == "literal" else (pb, pa)
                if not bind(other, lit.value,
                            "matched to literal %r fixed at %s" % (lit.value, lit.site)):
                    open_obs.append((atom, "conflicting binding for %s" % other.slot))
                continue
            value = rendezvous_value(lhs.name, rhs.name, model)
            if assigned.get(pa.slot):
                value = assigned[pa.slot].value
            elif assigned.get(pb.slot):
                value = assigned[pb.slot].value
            if bind(pa, value, "rendezvous with %s" % pb.slot) and \
               bind(pb, value, "rendezvous with %s" % pa.slot):
                rendezvous.append((pa.slot, pb.slot, value))
            else:
                open_obs.append((atom, "rendezvous blocked by an earlier binding"))
            continue

        # ---- one side produced, one constant -----------------------------
        # `A = SPACES OR A = LOW-VALUES` offers two ways to satisfy one
        # condition. Committing to the first and reporting a conflict when it
        # clashes downstream calls a satisfiable chain infeasible, so every
        # alternative gets a turn before the obligation is given up on.
        candidates = [atom] + list(atom.alternatives)
        settled = False
        failures = []
        for candidate in candidates:
            c_lhs, c_rhs = candidate.lhs, candidate.rhs
            if c_lhs.kind == c_rhs.kind:
                continue
            var_term, const_term = ((c_lhs, c_rhs) if c_lhs.kind == "var"
                                    else (c_rhs, c_lhs))
            op = candidate.op if c_lhs.kind == "var" else flip(candidate.op)
            domain = prov.literals.get(var_term.name, set())
            value = witness(op, const_term, domain)
            if value is None:
                failures.append("no witness value for %s" % candidate)
                continue

            producer = prov.producer(var_term.name, at)
            existing = assigned.get(producer.slot)
            if existing is not None:
                if holds(existing.value, op, const_term.value):
                    settled = True
                    break
                if existing.source == "agent":
                    notes.append("agent binding %s=%r overrides %s"
                                 % (producer.slot, existing.value, candidate))
                    settled = True
                    break
                if revise(existing, op, const_term):
                    settled = True
                    break
                if program_advanced(var_term.name) and op == "=":
                    earlier = (existing.atom is None
                               or chain_position(candidate)
                               < chain_position(existing.atom))
                    if earlier:
                        notes.append("%s: entry value %r (the program advances "
                                     "it to %r later)"
                                     % (var_term.name, value, existing.value))
                        existing.value = value
                        existing.atom = candidate
                    else:
                        notes.append("%s: %r is reached by the program advancing "
                                     "it, not by the entry state"
                                     % (var_term.name, value))
                    settled = True
                    break
                failures.append("%s already bound to %r" % (producer.slot,
                                                            existing.value))
                continue

            blockers = prov.blocking_writes(var_term.name, op, value)
            if blockers:
                for w in blockers:
                    # The literal being steered away from is, in a read loop,
                    # the end-of-file signal. Remember it: something has to
                    # deliver it eventually or the loop never ends.
                    for guard in w.guards:
                        for term in (guard.lhs, guard.rhs):
                            if term.kind == "var" and guard.op == "=":
                                other = guard.rhs if term is guard.lhs else guard.lhs
                                if other.kind == "const":
                                    avoided.setdefault(term.name, other.value)
                    for guard in w.guards:
                        for neg in negate_atom(guard):
                            derived.append((neg, "avoid %s TO %s at %s:%d"
                                            % (w.source, var_term.name,
                                               w.para, w.line)))
                            queue.append((neg, round_no + 1))
                settled = True
                break

            if producer.kind == "literal":
                if holds(producer.value, op, value):
                    settled = True
                    break
                failures.append("literal %r fixed at %s contradicts it"
                                % (producer.value, producer.site))
                continue

            if bind(producer, value, "from %s  [%s]" % (candidate, candidate.origin),
                    atom=candidate):
                settled = True
                break
            failures.append("conflicting binding for %s" % producer.slot)

        if not settled:
            open_obs.append((atom, "; ".join(failures[:3]) or "unsatisfiable"))

    terminals: dict = {}
    for b in bindings:
        if b.producer.kind != "stub":
            continue
        exit_value = avoided.get(b.producer.var)
        if exit_value is not None and exit_value != b.value:
            terminals.setdefault(b.producer.op_key, {})[b.producer.var] = exit_value
    if terminals:
        notes.append("terminal outcomes derived from avoided literals: %s" % terminals)

    return Plan(target, chain, [s.kind for s in path], atoms, bindings,
                rendezvous, open_obs, derived, notes, terminals)
