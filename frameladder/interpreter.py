"""Run the COBOL subset concretely, to check a plan and to say where it failed.

This is tier 1.  A plan that type-checks symbolically can still be wrong -
a guard the ladder never lifted, an ordering it got backwards - and the
only way to know is to run it.  When a plan does fail, the useful output
is not "false" but *which guard on the chain went the wrong way*, because
that is the single question worth handing to an agent.

Subscripts are flattened: ``WS-TAB(I)`` and ``WS-TAB`` are the same cell.
That mirrors how the rest of the toolchain models tables and keeps the
interpreter small; it means array-indexed plans are verified loosely, and
:attr:`Trace.approximations` says so rather than hiding it.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .conditions import condition_atoms
from .ir import holds, norm, parse_term

# Reaching a target takes hundreds of steps, not thousands. A
# generous ceiling only means a non-terminating plan burns
# seconds before saying so.
MAX_STEPS = 20_000
MAX_DEPTH = 64
MAX_LOOP = 200
RUNAWAY = 400        # one paragraph running this often is a loop, not progress

# Standard runtime services that terminate the program rather than return.
# Knowing these is the same kind of knowledge as knowing that abort() does
# not return - it is about the platform, not about any one program - and
# without it every abend path looks like it carries on executing.
TERMINATING_CALLS = {"CEE3ABD", "ILBOABN0", "ILBOABN", "CANCEL"}


class _Goto(Exception):
    def __init__(self, target: str):
        self.target = target


class _Stop(Exception):
    pass


@dataclass
class GuardEvent:
    paragraph: str
    line: int
    kind: str
    condition: str
    result: bool
    values: dict = field(default_factory=dict)


@dataclass
class Trace:
    entered: list = field(default_factory=list)
    guards: list = field(default_factory=list)
    steps: int = 0
    stopped: str = ""
    runaway: str = ""
    approximations: list = field(default_factory=list)

    @property
    def entered_set(self) -> set:
        return set(self.entered)


class Interpreter:
    """Execute the subset, applying stub returns *at the call site*.

    Pinning a stub's return as an ordinary variable is wrong in a way that
    matters: a file read returns records and then end-of-file, and a plan
    that pins the return code to '00' forever describes a file that never
    ends.  Outcomes are therefore delivered per call, matched on the same
    discriminators the ladder used to tell two invocations apart, and a
    terminal value takes over once the planned ones run out.
    """

    def __init__(self, program, state: dict | None = None, *,
                 stubs: dict | None = None, terminals: dict | None = None,
                 defaults: dict | None = None, repeat: int = 1,
                 sequential: bool = True):
        self.program = program
        self.model = program.model
        self.state = {k.upper(): v for k, v in (state or {}).items()}
        self.stubs = stubs or {}
        self.terminals = {k.upper(): {n.upper(): v for n, v in vals.items()}
                          for k, vals in (terminals or {}).items()}
        # A default is what an operation returns when no planned outcome
        # matches it at all - an OPEN succeeding while the plan only says
        # what a READ returns. A terminal is different: it is what happens
        # once the planned outcomes are used up, which is how a read loop
        # ends. Conflating them makes every open fail or every read endless.
        self.defaults = {k.upper(): {n.upper(): v for n, v in vals.items()}
                         for k, vals in (defaults or {}).items()}
        self.repeat = max(1, repeat)
        self.sequential = sequential
        self.trace = Trace()
        self._names = program.paragraph_names
        self._pinned = set(self.state)
        self._delivered: dict = {}
        self._visits: dict = {}
        self.calls: dict = {}
        # ALTER rewrites another paragraph's GO TO at run time. A dispatcher
        # built on it - and CardDemo's is - cycles forever without this.
        self.altered: dict = {}

    # -- values ------------------------------------------------------------
    def value_of(self, term) -> object:
        if term.kind == "const":
            return term.value
        name = term.name
        if name in self.state:
            return self.state[name]
        # A qualified reference names a declaration that is recorded under its
        # base name, so reads have to see through the qualifier exactly as
        # lookups elsewhere do - otherwise every write lands on one key, every
        # read misses, and the condition is decided on a default.
        found = self.model.look(self.state, name)
        if found is not None:
            return found
        found = self.model.look(self.model.initial, name)
        if found is not None:
            return found
        spec = (self.model.pic_of(name) or "").upper()
        return 0 if spec and "9" in spec and "X" not in spec else ""

    def evaluate(self, condition: str) -> bool:
        text = norm(condition)
        if not text:
            return True
        for alternative in condition_atoms(text):
            if not alternative:
                continue
            if all(self._atom(a) for a in alternative):
                return True
        return False

    def _atom(self, atom) -> bool:
        lhs, rhs = atom.lhs, atom.rhs
        if rhs.kind == "const" and rhs.value is True and lhs.kind == "var":
            entry = self.model.condition_names.get(lhs.name)
            if entry:
                parent, values = entry
                actual = self.value_of(parse_term(parent))
                truth = any(holds(actual, "=", parse_term(v).value) for v in values)
                return truth if atom.op == "=" else not truth
        return holds(self.value_of(lhs), atom.op, self.value_of(rhs))

    def assign(self, name: str, value) -> None:
        name = name.upper()
        # Values the plan pins are the stub returns and program inputs; the
        # program overwriting them mid-run would undo the very thing being
        # tested, so they hold.
        if name in self._pinned:
            return
        self.state[name] = value
        for child in self.model.descendants(name):
            if child not in self._pinned:
                self.state[child] = value

    # -- execution ---------------------------------------------------------
    def run(self, entry: str) -> Trace:
        index = self._names.index(entry.upper()) if entry.upper() in self._names else 0
        while 0 <= index < len(self._names):
            para = self.program.paragraphs[index]
            try:
                self.perform(para["name"], depth=0)
            except _Stop:
                if not self.trace.stopped:
                    self.trace.stopped = ("runaway loop in %s" % self.trace.runaway
                                          if self.trace.runaway
                                          else "STOP RUN / GOBACK")
                break
            except _Goto as jump:
                if jump.target in self._names:
                    index = self._names.index(jump.target)
                    continue
                break
            except RecursionError:
                self.trace.stopped = "recursion limit"
                break
            if not self.sequential:
                break
            index += 1
        return self.trace

    def _tick(self, name: str) -> None:
        """Notice a paragraph running away.

        Burning the whole step budget and reporting "not reached" hides the
        actual finding, which is that one paragraph ran thousands of times -
        usually a read loop with no end-of-file, or an abend handler that
        returns. Naming it turns a timeout into a diagnosis.
        """
        self._visits[name] = self._visits.get(name, 0) + 1
        if self._visits[name] > RUNAWAY:
            self.trace.runaway = name
            raise _Stop()

    def perform(self, spec: str, depth: int) -> None:
        """Run one paragraph, or a THRU range.

        ``PERFORM A THRU B`` runs every paragraph from A to B in source
        order - fall-through inside the range included.  Treating it as
        ``PERFORM A`` silently skips the middle of the range, which is
        where the interesting code usually is.
        """
        if depth > MAX_DEPTH:
            return
        start, _, end = spec.partition(" THRU ")
        start, end = start.strip().upper(), end.strip().upper()
        if not end or end not in self._names or start not in self._names:
            para = self.program.paragraph(start)
            if para is None:
                return
            self.trace.entered.append(start)
            self._tick(start)
            self.block(para.get("statements", []), para["name"], depth)
            return

        first, last = self._names.index(start), self._names.index(end)
        if last < first:
            first, last = last, first
        index = first
        while first <= index <= last:
            para = self.program.paragraphs[index]
            self.trace.entered.append(para["name"])
            self._tick(para["name"])
            try:
                self.block(para.get("statements", []), para["name"], depth)
            except _Goto as jump:
                # A jump inside the range keeps the PERFORM alive; one that
                # leaves the range propagates out of it.
                if jump.target in self._names:
                    landing = self._names.index(jump.target)
                    if first <= landing <= last:
                        index = landing
                        continue
                raise
            index += 1

    def block(self, statements, para: str, depth: int) -> None:
        for stmt in statements:
            self.step(stmt, para, depth)

    def step(self, stmt, para: str, depth: int) -> None:
        self.trace.steps += 1
        if self.trace.steps > MAX_STEPS:
            raise _Stop()
        kind = stmt.get("type", "")
        attrs = stmt.get("attributes", {})
        line = stmt.get("line_start", 0)
        children = stmt.get("children") or []

        if kind == "IF":
            condition = attrs.get("condition", "")
            result = self.evaluate(condition)
            self.trace.guards.append(GuardEvent(para, line, "IF", condition, result,
                                                self._snapshot(condition)))
            branch = [c for c in children if c.get("type") != "ELSE"]
            other = [c for c in children if c.get("type") == "ELSE"]
            if result:
                self.block(branch, para, depth)
            elif other:
                self.block(other[0].get("children") or [], para, depth)
            return

        if kind == "EVALUATE":
            subject = attrs.get("subject", "")
            arms = [c for c in children if c.get("type") == "WHEN"]
            for arm in arms:
                value = norm(arm.get("attributes", {}).get("value", ""))
                if value.upper() in ("OTHER", "ANY"):
                    continue
                condition = (value if norm(subject).upper() in ("TRUE", "FALSE")
                             else "%s = %s" % (subject, value))
                result = self.evaluate(condition)
                if norm(subject).upper() == "FALSE":
                    result = not result
                self.trace.guards.append(
                    GuardEvent(para, arm.get("line_start", line), "WHEN",
                               condition, result, self._snapshot(condition)))
                if result:
                    self.block(arm.get("children") or [], para, depth)
                    return
            for arm in arms:
                if norm(arm.get("attributes", {}).get("value", "")).upper() in ("OTHER", "ANY"):
                    self.trace.guards.append(
                        GuardEvent(para, arm.get("line_start", line), "WHEN",
                                   "OTHER", True, {}))
                    self.block(arm.get("children") or [], para, depth)
                    return
            return

        if kind == "PERFORM":
            target = (attrs.get("target") or "").strip()
            condition = attrs.get("condition")
            if condition and children:
                self._loop(condition, children, para, depth, line)
                return
            if condition:
                count = 0
                while not self.evaluate(condition) and count < MAX_LOOP:
                    self.perform(target, depth + 1)
                    count += 1
                self.trace.guards.append(GuardEvent(para, line, "PERFORM_UNTIL",
                                                    condition, count > 0, {}))
                return
            if target:
                self.perform(target, depth + 1)
            return

        if kind == "PERFORM_INLINE":
            varying = attrs.get("varying")
            if varying:
                self._varying(varying, children, para, depth, line)
                return
            condition = attrs.get("condition")
            if condition:
                self._loop(condition, children, para, depth, line)
                return
            self.block(children, para, depth)
            return

        if kind in ("GO_TO", "GOTO"):
            target = self.altered.get(para) or attrs.get("target")
            if target:
                raise _Goto(target.upper())
            return

        if kind == "ALTER":
            altered, destination = attrs.get("altered"), attrs.get("destination")
            if altered and destination:
                self.altered[altered.upper()] = destination.upper()
            return

        if kind in ("GOBACK", "STOP"):
            raise _Stop()

        if kind == "MOVE":
            source = parse_term(attrs.get("source", ""))
            value = self.value_of(source)
            from .ir import move_targets
            for name in move_targets(attrs.get("targets", "")):
                self.assign(name, value)
            return

        if kind == "SET":
            name, raw = attrs.get("name"), attrs.get("value")
            if name and raw:
                entry = self.model.condition_names.get(name.upper())
                if entry and raw.upper() == "TRUE":
                    parent, values = entry
                    if values:
                        self.assign(parent, parse_term(values[0]).value)
                else:
                    self.assign(name, parse_term(raw).value)
            return

        if kind in ("ADD", "SUBTRACT", "COMPUTE", "MULTIPLY", "DIVIDE"):
            self._arithmetic(kind, stmt)
            return

        from .provenance import STUB_KINDS, op_key
        if kind in STUB_KINDS:
            self._external(stmt, para, line)
            if children:
                self.block(children, para, depth)
            return

        if children:
            self.block(children, para, depth)

    def _external(self, stmt, para: str, line: int) -> None:
        """Deliver the planned outcome for one external operation."""
        from .provenance import op_key
        key = op_key(norm(stmt.get("text", "")))
        self.calls[key] = self.calls.get(key, 0) + 1
        if key.startswith("CALL:") and key[5:] in TERMINATING_CALLS:
            self.trace.stopped = "terminated by %s" % key[5:]
            raise _Stop()
        entries = self.stubs.get(key, [])
        matched = False
        for index, entry in enumerate(entries):
            when = {k.upper(): v for k, v in (entry.get("when") or {}).items()}
            if all(holds(self.value_of(parse_term(k)), "=", v)
                   for k, v in when.items()):
                matched = True
                break
        if not matched:
            for name, value in self.defaults.get(key, {}).items():
                self._force(name, value)
            return
        for index, entry in enumerate(entries):
            when = {k.upper(): v for k, v in (entry.get("when") or {}).items()}
            if not all(holds(self.value_of(parse_term(k)), "=", v)
                       for k, v in when.items()):
                continue
            if self._delivered.get((key, index), 0) >= self.repeat:
                continue
            self._delivered[(key, index)] = self._delivered.get((key, index), 0) + 1
            for name, value in (entry.get("set") or {}).items():
                self._force(name, value)
            return
        for name, value in self.terminals.get(key, {}).items():
            self._force(name, value)

    def _force(self, name: str, value) -> None:
        name = name.upper()
        self.state[name] = value
        for child in self.model.descendants(name):
            self.state[child] = value

    def _snapshot(self, condition: str) -> dict:
        out = {}
        for alternative in condition_atoms(condition):
            for atom in alternative:
                for term in (atom.lhs, atom.rhs):
                    if term.kind == "var":
                        out[term.name] = self.value_of(term)
        return out

    def _loop(self, condition: str, children, para: str, depth: int, line: int):
        count = 0
        while count < MAX_LOOP and not self.evaluate(condition):
            self.block(children, para, depth)
            count += 1
        self.trace.guards.append(GuardEvent(para, line, "PERFORM_UNTIL", condition,
                                            count > 0, self._snapshot(condition)))

    def _varying(self, clause: str, children, para: str, depth: int, line: int):
        import re
        m = re.search(r"VARYING\s+([A-Z0-9-]+)\s+FROM\s+(\S+)\s+BY\s+(\S+)\s+UNTIL\s+(.*)",
                      norm(clause), re.I)
        if not m:
            self.block(children, para, depth)
            return
        var, start, by, until = (m.group(1).upper(), parse_term(m.group(2)).value,
                                 parse_term(m.group(3)).value, m.group(4))
        self.assign(var, start)
        count = 0
        entered = False
        while count < MAX_LOOP and not self.evaluate(until):
            entered = True
            self.block(children, para, depth)
            try:
                self.assign(var, float(self.value_of(parse_term(var))) + float(by))
            except (TypeError, ValueError):
                break
            count += 1
        self.trace.guards.append(GuardEvent(para, line, "PERFORM_VARYING", until,
                                            entered, self._snapshot(until)))

    def _arithmetic(self, kind: str, stmt) -> None:
        import re
        text = norm(stmt.get("text", ""))
        m = re.match(r"(?:ADD|SUBTRACT)\s+(\S+)\s+(?:TO|FROM)\s+(\S+)\s+"
                     r"GIVING\s+([A-Z0-9-]+)", text, re.I)
        if m:
            a = self.value_of(parse_term(m.group(1)))
            b = self.value_of(parse_term(m.group(2)))
            try:
                total = (float(a) + float(b) if text.upper().startswith("ADD")
                         else float(b) - float(a))
                self.assign(m.group(3), total)
            except (TypeError, ValueError):
                pass
            return
        m = re.match(r"ADD\s+(\S+)\s+TO\s+([A-Z0-9-]+)", text, re.I)
        if m:
            a = self.value_of(parse_term(m.group(1)))
            b = self.value_of(parse_term(m.group(2)))
            try:
                self.assign(m.group(2), float(a) + float(b))
            except (TypeError, ValueError):
                pass
            return
        m = re.match(r"SUBTRACT\s+(\S+)\s+FROM\s+([A-Z0-9-]+)", text, re.I)
        if m:
            a = self.value_of(parse_term(m.group(1)))
            b = self.value_of(parse_term(m.group(2)))
            try:
                self.assign(m.group(2), float(b) - float(a))
            except (TypeError, ValueError):
                pass
            return
        if kind == "COMPUTE":
            self.trace.approximations.append("COMPUTE not evaluated: %s" % text[:60])


def verify(program, plan, entry: str, *, terminals: dict | None = None,
           defaults: dict | None = None, repeat: int = 1) -> dict:
    """Run the plan and report whether the target was reached, and if not,
    the first guard on the chain that went the wrong way."""
    interp = Interpreter(program, plan.input_state(), stubs=plan.stub_plan(),
                         terminals=terminals or plan.terminals,
                         defaults=defaults, repeat=repeat)
    trace = interp.run(entry)
    reached = plan.target in trace.entered_set
    chain = [c for c in plan.chain]
    frontier = None
    for frame in chain:
        if frame not in trace.entered_set:
            frontier = frame
            break

    blocking = []
    if not reached:
        wanted = set(chain)
        for event in trace.guards:
            if event.paragraph in wanted and not event.result:
                blocking.append(event)

    return {
        "reached": reached,
        "entry": entry,
        "target": plan.target,
        "chain": chain,
        "chain_reached": [c for c in chain if c in trace.entered_set],
        "first_missing_frame": frontier,
        "steps": trace.steps,
        "stopped": trace.stopped,
        "paragraphs_entered": len(trace.entered_set),
        "approximations": trace.approximations[:5],
        "exhausted_steps": trace.steps >= MAX_STEPS,
        "runaway": trace.runaway,
        "external_calls": interp.calls,
        "blocking_guards": [
            {"paragraph": e.paragraph, "line": e.line, "kind": e.kind,
             "condition": e.condition, "values": e.values}
            for e in blocking[:12]
        ],
    }
