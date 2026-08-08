"""Call graph, guarded call sites, and the chains through them."""

from __future__ import annotations

import re
from collections import deque
from dataclasses import dataclass, field

from .conditions import condition_atoms, when_condition
from .ir import Atom, Term, move_targets, negate_atom, norm, parse_term

_VARYING = re.compile(
    r"VARYING\s+([A-Z0-9-]+)\s+FROM\s+(\S+)\s+BY\s+(\S+)\s+UNTIL\s+(.*)", re.I)
_TERMINATORS = {"GO_TO", "GOTO", "GOBACK", "STOP", "EXIT_PROGRAM"}


@dataclass
class CallSite:
    caller: str
    callee: str
    line: int
    guards: list
    kind: str = "perform"          # perform | goto | alter | fallthrough


def first_with_alternatives(alts) -> list:
    """Take the first alternative, but remember the others.

    Only single-atom alternatives are carried - a plain OR of comparisons,
    which is the case that actually matters and the one a solver most
    often needs to reconsider.
    """
    if not alts:
        return []
    spares = tuple(a[0] for a in alts[1:] if len(a) == 1)
    chosen = alts[0]
    if not spares or not chosen:
        return list(chosen)
    head = chosen[0]
    return [Atom(head.lhs, head.op, head.rhs, head.origin, spares)] + list(chosen[1:])


def substitute(atoms, bindings: dict) -> list:
    """Tier-0: replace loop induction variables with first-iteration constants,
    in the terms and in the subscripts."""
    out = []
    for atom in atoms:
        sides = []
        for term in (atom.lhs, atom.rhs):
            if term.kind == "var" and term.name in bindings and not term.index:
                sides.append(Term("const", value=bindings[term.name]))
            elif term.index:
                sides.append(Term("var", name=term.name,
                                  index=tuple(bindings.get(str(i).upper(), i)
                                              for i in term.index)))
            else:
                sides.append(term)
        out.append(Atom(sides[0], atom.op, sides[1], atom.origin,
                        atom.alternatives))
    return out


def _after_earlier_arms(stmt: dict, subject: str, siblings, origin: str) -> list:
    """EVALUATE takes the *first* arm that matches.

    So reaching arm N means arms 1..N-1 all failed, and without saying so an
    arm looks satisfiable on its own condition alone - which is why a long
    EVALUATE ends up with only its first arm ever taken. Consecutive WHENs
    sharing a body are one alternative each, so every preceding one counts.
    """
    out: list = []
    for sib in siblings or ():
        if sib is stmt:
            break
        if sib.get("type") != "WHEN":
            continue
        value = norm(sib.get("attributes", {}).get("value", ""))
        if not value or value.upper() in ("OTHER", "ANY"):
            continue
        if norm(subject).upper() in ("TRUE", "FALSE"):
            alts = condition_atoms(value, norm(subject).upper() == "TRUE",
                                   origin)
            out.extend(alts[0] if alts else [])
        else:
            alts = condition_atoms(when_condition(subject, value), True,
                                   origin)
            out.extend(alts[0] if alts else [])
    return out


def _when_guards(stmt: dict, subject: str, siblings, origin: str) -> list:
    value = norm(stmt.get("attributes", {}).get("value", ""))
    if not subject:
        return []

    # `EVALUATE TRUE / WHEN <condition>` is the COBOL switch-on-predicates
    # idiom: the arm is a whole condition, not a value to compare against.
    if norm(subject).upper() in ("TRUE", "FALSE"):
        invert = norm(subject).upper() == "FALSE"
        if value.upper() in ("OTHER", "ANY"):
            out = []
            for sib in siblings:
                sv = norm(sib.get("attributes", {}).get("value", ""))
                if sib is stmt or sv.upper() in ("OTHER", "ANY") or not sv:
                    continue
                alts = condition_atoms(sv, not invert, origin)
                out.extend(alts[0] if alts else [])
            return out
        own = first_with_alternatives(condition_atoms(value, invert, origin))
        # The arm's own condition is the point of the plan, so it is settled
        # first; the preceding arms it must out-rank are real obligations but
        # secondary, and binding them first consumes the slots it needs.
        return own + _after_earlier_arms(stmt, subject, siblings, origin)

    subj = Term("var", name=parse_term(subject).name)
    if value.upper() in ("OTHER", "ANY"):
        # WHEN OTHER holds exactly when every other arm fails.
        out = []
        for sib in siblings:
            sv = norm(sib.get("attributes", {}).get("value", ""))
            if sib is stmt or sv.upper() in ("OTHER", "ANY") or not sv:
                continue
            branch = condition_atoms(when_condition(subject, sv), True, origin)
            out.extend(branch[0] if branch else [])
        return out
    # `WHEN 1 THRU 9` and `WHEN > 10` are a range and a relation, not values
    # to compare the subject against; rendering them as `subject = <phrase>`
    # invents a field named after the phrase and the arm becomes unplannable.
    own = first_with_alternatives(
        condition_atoms(when_condition(subject, value), False, origin))
    if not own:
        return []
    return own + _after_earlier_arms(stmt, subject, siblings, origin)


def _loop_guards(stmt: dict, origin: str) -> tuple[list, dict]:
    attrs = stmt.get("attributes", {})
    induction: dict = {}
    m = _VARYING.search(norm(attrs.get("varying") or ""))
    if m:
        induction[m.group(1).upper()] = parse_term(m.group(2)).value
        return first_with_alternatives(
            condition_atoms(m.group(4), True, origin)), induction
    cond = attrs.get("condition") or attrs.get("until") or ""
    if cond:
        return first_with_alternatives(
            condition_atoms(cond, True, origin)), induction
    return [], induction


def walk_guarded(paragraph: dict, visit):
    """Walk a paragraph handing each statement the conditions enclosing it.

    ``ELSE`` is the subtle one.  It arrives as a *child* of the IF, so the
    naive walk gives its body the IF's condition - the exact opposite of
    the truth.  Here the then-branch and the else-branch are walked
    separately, with the condition and its negation respectively.
    """
    name = paragraph["name"]

    def rec(stmts, guards, induction, literals):
        for stmt in stmts:
            kind = stmt.get("type", "")
            attrs = stmt.get("attributes", {})
            line = stmt.get("line_start", 0)
            origin = "%s:%d" % (name, line)
            visit(stmt, name, substitute(guards, induction), dict(induction),
                  dict(literals))

            if kind == "MOVE":
                src = parse_term(attrs.get("source", ""))
                for base in move_targets(attrs.get("targets", "")):
                    if src.kind == "const" and not guards:
                        literals[base] = src.value
                    else:
                        literals.pop(base, None)

            children = stmt.get("children") or []
            if not children:
                continue

            if kind == "IF":
                condition = attrs.get("condition", "")
                yes = condition_atoms(condition, False, origin)
                no = condition_atoms(condition, True, origin)
                then_part = [c for c in children if c.get("type") != "ELSE"]
                else_part = [c for c in children if c.get("type") == "ELSE"]
                rec(then_part, list(guards) + first_with_alternatives(yes),
                    dict(induction), literals)
                for node in else_part:
                    visit(node, name, substitute(guards, induction),
                          dict(induction), dict(literals))
                    rec(node.get("children") or [],
                        list(guards) + first_with_alternatives(no),
                        dict(induction), literals)
                continue

            if kind == "EVALUATE":
                subject = attrs.get("subject", "")
                for arm in children:
                    visit(arm, name, substitute(guards, induction),
                          dict(induction), dict(literals))
                    own = _when_guards(arm, subject, children,
                                       "%s:%d" % (name, arm.get("line_start", line)))
                    rec(arm.get("children") or [], list(guards) + own,
                        dict(induction), literals)
                continue

            own, induct = ([], {})
            if kind.startswith("PERFORM"):
                own, induct = _loop_guards(stmt, origin)
            merged = dict(induction)
            merged.update(induct)
            rec(children, list(guards) + own, merged, literals)

    rec(paragraph.get("statements", []), [], {}, {})


def obligations_for_branch(program, paragraph: str, line: int,
                           direction: bool, ordinal: int | None = None) -> list:
    """What must hold for one decision to go a particular way.

    Aiming a plan at a paragraph only satisfies the guards on the way *to*
    it; every condition inside then evaluates against whatever the defaults
    happen to be, which is why so many end up always false. Aiming at a
    direction adds the condition itself, plus the guards enclosing it within
    the paragraph, so the run arrives with the decision already determined.

    Addressed by ordinal when one is given. A line does not identify a
    decision: `COPY CSUTLDPY` expands twenty of them onto the line of the
    directive, and matching by line conjoins every one of their conditions
    into a single unsatisfiable obligation.
    """
    para = program.paragraph(paragraph)
    if para is None:
        return []
    found: list = []

    # A WHEN arm does not carry its own subject; the EVALUATE above it does.
    subjects: dict = {}

    def index(stmt):
        if stmt.get("type") == "EVALUATE":
            subject = stmt.get("attributes", {}).get("subject", "")
            for arm in stmt.get("children") or []:
                if arm.get("type") == "WHEN":
                    subjects[arm.get("line_start", 0)] = (subject,
                                                          stmt.get("children"))
        for child in stmt.get("children") or []:
            index(child)

    for stmt in para.get("statements", []):
        index(stmt)

    def visit(stmt, pname, guards, induction, literals):
        if ordinal is not None:
            if stmt.get("ordinal", -1) != ordinal:
                return
        elif stmt.get("line_start", 0) != line:
            return
        kind = stmt.get("type", "")
        attrs = stmt.get("attributes", {})
        origin = "%s:%d" % (pname, line)
        own: list = []
        if kind == "IF":
            alts = condition_atoms(attrs.get("condition", ""), not direction,
                                   origin)
            own = first_with_alternatives(alts)
        elif kind == "WHEN":
            subject, siblings = subjects.get(line, ("", [stmt]))
            own = _when_guards(stmt, subject, siblings or [stmt], origin)
            if not direction:
                own = [a for atom in own for a in negate_atom(atom)]
        elif kind.startswith("PERFORM"):
            own, _induct = _loop_guards(stmt, origin)
            if not direction:
                own = [a for atom in own for a in negate_atom(atom)]
        if own or guards:
            found.extend(list(guards) + list(own))

    walk_guarded(para, visit)
    if not found:
        return found

    # Reaching a statement means no earlier escape in the paragraph fired.
    # CardDemo's edit paragraphs are a run of `IF bad → SET flag, GO TO EXIT`,
    # so every decision after the first escape is unreachable unless that is
    # said. The same computation already guards call sites; it was simply
    # never applied to the decisions themselves.
    own = {v for a in found for v in a.variables}
    for escape_line, negation in _escapes(para):
        if escape_line >= line:
            continue
        if own & {v for a in negation for v in a.variables}:
            continue
        own |= {v for a in negation for v in a.variables}
        found.extend(negation)
    return found


# Ways a paragraph ends the whole run, as opposed to merely ending itself.
# GO TO is deliberately absent: inside a performed range it leaves the
# paragraph, it does not stop the program.
_ENDERS = {"GOBACK", "STOP", "EXIT_PROGRAM"}
_ABEND_CALLS = {"CEE3ABD", "ILBOABN0", "ILBOABN", "CANCEL"}


def _ends_run(stmt: dict) -> bool:
    if stmt.get("type", "") in _ENDERS:
        return True
    if stmt.get("type", "") == "CALL":
        target = norm(stmt.get("attributes", {}).get("target", "")).strip("'\" ")
        return target.upper() in _ABEND_CALLS
    return False


def terminations(program, paragraph: str, seen=None) -> tuple[list, bool]:
    """How this paragraph can stop the run: (guarded ways, stops_always).

    Transitive, because a paragraph that performs a validator which abends on
    bad input ends the run just as surely as if it abended itself.
    """
    seen = seen if seen is not None else set()
    if paragraph in seen:
        return [], False
    seen.add(paragraph)
    para = program.paragraph(paragraph)
    if para is None:
        return [], False

    found: list = []
    always = [False]

    def visit(stmt, pname, own_guards, induction, literals):
        if _ends_run(stmt):
            if own_guards:
                found.append(list(own_guards))
            else:
                always[0] = True
            return
        if stmt.get("type", "").startswith("PERFORM"):
            callee = (stmt.get("attributes", {}).get("target") or "").strip()
            if not callee or stmt.get("attributes", {}).get("condition"):
                return
            deeper, sub_always = terminations(program, callee, seen)
            for guards in deeper:
                found.append(list(own_guards) + guards)
            if sub_always:
                if own_guards:
                    found.append(list(own_guards))
                else:
                    always[0] = True

    walk_guarded(para, visit)
    return found, always[0]


def survival_atoms(program, path, limit: int = 24) -> list:
    """What must hold for the run to still be alive at each step of a chain.

    Reaching a frame is not only a matter of the guards on the calls that
    lead to it. Everything performed *before* those calls has to have
    returned. A batch program whose second act is `PERFORM 1100-OPEN-FILES`
    and whose third is `PERFORM 2000-PROCESS` cannot reach the third at all
    if the second abends, and no amount of solving the guards on 2000 will
    say so - the ladder simply produces a plan that dies one paragraph
    early and reports it as solved.

    So for every earlier sibling call, each guarded way it could end the run
    contributes the negation of that guard. An *un*guarded one is not an
    obligation but a proof: nothing after it is reachable, and the caller
    should hear that rather than a plan.

    The obligations are capped. A program with many validators generates a
    long tail of these, and past a point they stop discriminating and start
    crowding out the guards that actually select the target - which is how
    an earlier attempt at this over-produced and had to be reverted.
    """
    out: list = []
    for site in path:
        caller = program.paragraph(site.caller)
        if caller is None:
            continue
        for stmt in caller.get("statements", []) or []:
            line = stmt.get("line_start", 0)
            if line >= site.line or not stmt.get("type", "").startswith("PERFORM"):
                continue
            callee = (stmt.get("attributes", {}).get("target") or "").strip()
            if not callee or callee == site.callee:
                continue
            guarded, always = terminations(program, callee)
            if always:
                return [("INFEASIBLE", callee, site.caller, line)]
            for guards in guarded:
                # Surviving means not every conjunct held. Negating one is
                # enough, and the first is the one the program itself tests.
                for atom in negate_atom(guards[-1]):
                    out.append(atom)
                    if len(out) >= limit:
                        return out
    return out


def build_graph(program) -> dict:
    """PERFORM and GO TO edges, plus the two COBOL-specific ones a naive
    graph misses.

    ``ALTER X TO PROCEED TO Y`` rewrites another paragraph's GO TO at run
    time; without an edge for it, a dispatcher-style program looks mostly
    unreachable.  Fall-through matters for the same reason: a paragraph
    that does not end in a GO TO or GOBACK simply runs into the next one,
    and for many programs that is the only way the mainline is entered.
    """
    graph: dict = {}
    alters: list = []
    order = program.paragraph_names

    for para in program.paragraphs:
        sites: list = []

        def visit(stmt, pname, guards, induction, literals, _sites=sites):
            attrs = stmt.get("attributes", {})
            kind = stmt.get("type", "")
            line = stmt.get("line_start", 0)
            if kind in ("GO_TO", "GOTO") and attrs.get("targets"):
                # A computed GO TO reaches every label in its list. One edge
                # leaves the other n-1 arms looking unreachable, so no chain
                # is ever built to them.
                for tgt in attrs["targets"]:
                    if tgt:
                        _sites.append(CallSite(pname, tgt.upper(), line,
                                               list(guards), "goto"))
            elif kind in ("PERFORM", "GO_TO", "GOTO") and attrs.get("target"):
                for tgt in re.split(r"\s+THRU\s+|\s+THROUGH\s+", attrs["target"],
                                    flags=re.I):
                    tgt = tgt.strip().upper()
                    if tgt:
                        _sites.append(CallSite(pname, tgt, line, list(guards),
                                               "perform" if kind == "PERFORM"
                                               else "goto"))
            elif kind == "ALTER" and attrs.get("destination"):
                # The redirection only happens if the arm holding the ALTER
                # actually ran, so its guards belong on the edge. The arm
                # then jumps straight there, so it is also a direct edge
                # from *this* paragraph - and routing through the altered
                # one in two hops lets a search pair the jump with a
                # different arm than the one that set it up.
                alters.append((attrs["altered"], attrs["destination"], line,
                               list(guards)))
                _sites.append(CallSite(pname, attrs["destination"], line,
                                       list(guards), "alter"))

        walk_guarded(para, visit)
        # Reaching anything at line N means no earlier guarded escape fired.
        # Without this a GO TO late in a paragraph looks unconditional, and
        # the ladder lifts no obligation at all for the hop it enables.
        escapes = _escapes(para)
        for site in sites:
            own = {v for g in site.guards for v in g.variables}
            for line, negation in escapes:
                if line >= site.line:
                    continue
                # An escape whose condition is about the same variables the
                # site is already guarded on is a sibling branch, not an
                # earlier exit - an EVALUATE arm, say. Its guard is already
                # settled by the site's own, and re-asserting the negation
                # only manufactures a contradiction.
                if own & {v for a in negation for v in a.variables}:
                    continue
                site.guards = list(site.guards) + list(negation)
        graph[para["name"]] = sites

    for altered, destination, line, guards in alters:
        if altered in graph and not any(s.callee == destination
                                        for s in graph[altered]):
            graph[altered].append(CallSite(altered, destination, line,
                                           list(guards), "alter"))

    for i, name in enumerate(order[:-1]):
        para = program.paragraphs[i]
        guards, escapes = _fallthrough_guards(para)
        if escapes:
            continue                       # control always leaves first
        nxt = order[i + 1]
        if not any(s.callee == nxt for s in graph[name]):
            graph[name].append(CallSite(name, nxt, para.get("line_end", 0),
                                        guards, "fallthrough"))
    return graph


def completes(statements) -> bool:
    """Can control reach the end of this statement list?

    A paragraph whose every branch jumps away never falls through to the
    next one, and inventing that edge invents obligations with it - which
    is how a dispatcher ends up demanding its selector be four values at
    once.  IF counts as escaping only when *both* arms do; EVALUATE only
    when it has a catch-all arm and all of them do.
    """
    for stmt in statements or []:
        kind = stmt.get("type", "")
        children = stmt.get("children") or []
        if kind in ("GO_TO", "GOTO", "GOBACK", "STOP", "EXIT_PROGRAM"):
            return False
        if kind == "IF":
            then_part = [c for c in children if c.get("type") != "ELSE"]
            else_node = next((c for c in children if c.get("type") == "ELSE"), None)
            else_part = (else_node.get("children") or []) if else_node else None
            if not completes(then_part) and else_part is not None \
                    and not completes(else_part):
                return False
        elif kind == "EVALUATE":
            arms = [c for c in children if c.get("type") == "WHEN"]
            catch_all = any(norm(a.get("attributes", {}).get("value", "")).upper()
                            in ("OTHER", "ANY") for a in arms)
            if arms and catch_all and all(not completes(a.get("children") or [])
                                          for a in arms):
                return False
    return True


def _escapes(paragraph: dict) -> list:
    """Guarded ways out of a paragraph, each with the condition that avoids it."""
    out: list = []

    def visit(stmt, pname, own_guards, induction, literals):
        if stmt.get("type") not in _TERMINATORS or not own_guards:
            return
        out.append((stmt.get("line_start", 0), negate_atom(own_guards[-1])))

    walk_guarded(paragraph, visit)
    return out


def _fallthrough_guards(paragraph: dict) -> tuple[list, bool]:
    """What must hold for control to run off the end of a paragraph.

    Falling through is not unconditional: every guarded ``GO TO`` or
    ``GOBACK`` inside the paragraph is a way out, and reaching the next
    paragraph means none of them fired.  An *un*guarded one means control
    never gets there at all.  Without this the ladder emits a chain whose
    fall-through edge it has no obligation for, and the plan quietly fails
    at exactly that step.
    """
    guards: list = []
    escaped = [not completes(paragraph.get("statements") or [])]

    def visit(stmt, pname, own_guards, induction, literals):
        if stmt.get("type") not in _TERMINATORS:
            return
        if not own_guards:
            escaped[0] = True
            return
        # NOT(A AND B) is satisfied by negating any one conjunct; the
        # innermost is the condition that actually guards the jump.
        innermost = own_guards[-1]
        guards.extend(negate_atom(own_guards[-1]))

    walk_guarded(paragraph, visit)
    return guards, escaped[0]


def _render(atom: Atom) -> str:
    def side(t: Term) -> str:
        if t.kind == "const":
            return "'%s'" % t.value if isinstance(t.value, str) else str(t.value)
        return t.name
    return "%s %s %s" % (side(atom.lhs), atom.op, side(atom.rhs))


# --------------------------------------------------------------------------
# Chains
# --------------------------------------------------------------------------

def shortest_chain(graph: dict, entry: str, target: str, *,
                   kinds: set | None = None) -> list | None:
    """Fewest frames from entry to target. Shallow chains carry the fewest
    obligations, so this is the default."""
    queue, seen = deque([(entry, [])]), {entry}
    while queue:
        para, path = queue.popleft()
        for site in graph.get(para, []):
            if kinds and site.kind not in kinds:
                continue
            if site.callee == target:
                return path + [site]
            if site.callee not in seen:
                seen.add(site.callee)
                queue.append((site.callee, path + [site]))
    return None


def chain_via(graph: dict, entry: str, waypoints, target: str, *,
              kinds: set | None = None) -> list | None:
    """A chain that passes through named frames, in order.

    This is how a caller asks for a *particular* call trace rather than
    whichever one happens to be shortest - the deep route through a
    validation cascade, say, instead of the direct edge that skips it.
    """
    legs, current = [], entry
    for stop in list(waypoints) + [target]:
        stop = stop.upper()
        if stop == current:
            continue
        leg = shortest_chain(graph, current, stop, kinds=kinds)
        if leg is None:
            return None
        legs.extend(leg)
        current = stop
    return legs


def depths(graph: dict, entry: str) -> dict:
    """Fewest frames from entry to every reachable paragraph."""
    out = {entry: 0}
    queue = deque([entry])
    while queue:
        para = queue.popleft()
        for site in graph.get(para, []):
            if site.callee not in out:
                out[site.callee] = out[para] + 1
                queue.append(site.callee)
    return out


def execution_order(graph: dict, entry: str) -> dict:
    """Depth-first order in which paragraphs first run.

    Static def-use alone is ambiguous whenever two paragraphs copy the
    same fields in opposite directions; following the call structure
    breaks the tie, because only an earlier write can be the one a read
    sees.  It stays a *preference*, never a filter - a dispatcher
    rewritten by ALTER makes any single static order a guess.
    """
    order: dict = {}
    counter = 0
    stack = [entry]
    while stack:
        para = stack.pop()
        if para in order:
            continue
        order[para] = counter
        counter += 1
        for site in reversed(graph.get(para, [])):
            if site.callee not in order:
                stack.append(site.callee)
    for para in graph:
        if para not in order:
            order[para] = counter
            counter += 1
    return order


def guard_count(graph: dict, entry: str, target: str) -> int:
    chain = shortest_chain(graph, entry, target)
    return sum(len(s.guards) for s in chain) if chain else 0
