"""Terms, atoms and the small algebra the ladder reasons in."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any

_LITERAL = re.compile(r"^'([^']*)'$|^\"([^\"]*)\"$|^([+-]?\d+(?:\.\d+)?)$")
_SUBSCRIPTED = re.compile(r"^([A-Z0-9][A-Z0-9-]*)\s*\(([^)]*)\)$", re.I)
_TARGET = re.compile(r"([A-Z0-9][A-Z0-9-]*)\s*(?:\(([^)]*)\))?", re.I)

FIGURATIVE = {"ZERO": 0, "ZEROS": 0, "ZEROES": 0, "SPACE": " ", "SPACES": " ",
              "LOW-VALUE": "\x00", "LOW-VALUES": "\x00", "HIGH-VALUE": "\xff",
              "HIGH-VALUES": "\xff", "NULL": "", "NULLS": ""}
NEGATE = {"=": "!=", "!=": "=", ">": "<=", "<=": ">", "<": ">=", ">=": "<"}


def norm(text: str) -> str:
    """Conditions arrive folded across source lines; flatten them first."""
    return re.sub(r"\s+", " ", (text or "").replace("\n", " ")).strip()


@dataclass(frozen=True)
class Term:
    kind: str                      # 'const' | 'var'
    name: str = ""
    value: Any = None
    index: tuple = ()

    @property
    def key(self) -> str:
        if self.kind == "const":
            return repr(self.value)
        return self.name + ("(%s)" % ",".join(str(i) for i in self.index)
                            if self.index else "")

    def __str__(self) -> str:
        return self.key


@dataclass(frozen=True)
class Atom:
    lhs: Term
    op: str
    rhs: Term
    origin: str = ""
    # Other single-atom ways to satisfy the same condition. `A = SPACES OR
    # A = LOW-VALUES` yields one atom plus one alternative, and a solver
    # that forgets the alternative will call a satisfiable chain infeasible.
    alternatives: tuple = ()

    def __str__(self) -> str:
        return "%s %s %s" % (self.lhs, self.op, self.rhs)

    @property
    def variables(self) -> list[str]:
        return [t.name for t in (self.lhs, self.rhs) if t.kind == "var"]


def balanced(text: str) -> bool:
    depth = 0
    for ch in text:
        depth += (ch == "(") - (ch == ")")
        if depth < 0:
            return False
    return depth == 0


def parse_term(text: str) -> Term:
    text = norm(text).strip(".")
    while text.startswith("(") and text.endswith(")") and balanced(text[1:-1]):
        text = text[1:-1].strip()
    if not text:
        return Term("const", value="")
    m = _LITERAL.match(text)
    if m:
        if m.group(3) is not None:
            num = m.group(3)
            return Term("const", value=float(num) if "." in num else int(num))
        return Term("const", value=m.group(1) if m.group(1) is not None else m.group(2))
    upper = text.upper()
    if upper in FIGURATIVE:
        return Term("const", value=FIGURATIVE[upper])
    m = _SUBSCRIPTED.match(text)
    if m:
        return Term("var", name=m.group(1).upper(),
                    index=tuple(s.strip() for s in m.group(2).split(",")))
    return Term("var", name=upper)


def move_targets(text: str) -> list[str]:
    """Base names written by a MOVE.

    Splitting on whitespace is wrong: in ``MOVE TR-CNT TO WS-TRCT (CR-CNT)``
    the subscript is a *read*, and counting it as a write invents a def-use
    edge that derails the whole provenance walk.
    """
    return [m.group(1).upper() for m in _TARGET.finditer(norm(text))]


def holds(left: Any, op: str, right: Any) -> bool:
    """Compare the way COBOL would: mixed alphanumeric and numeric operands
    are reconciled rather than raising."""
    try:
        if isinstance(left, str) != isinstance(right, str):
            try:
                left, right = float(str(left).strip()), float(str(right).strip())
            except (TypeError, ValueError):
                left, right = str(left).strip(), str(right).strip()
        elif isinstance(left, str):
            left, right = left.strip(), right.strip()
        return {"=": left == right, "!=": left != right, ">": left > right,
                "<": left < right, ">=": left >= right, "<=": left <= right}[op]
    except (TypeError, KeyError):
        return op != "="


def flip(op: str) -> str:
    return {">": "<", "<": ">", ">=": "<=", "<=": ">="}.get(op, op)


def negate_atom(atom: Atom) -> list:
    """Negate an atom without going through text.

    Rendering an atom back to COBOL and re-parsing it loses whatever has
    no surface syntax - a level-88 truth value comes back as a variable
    called TRUE - and it silently drops the OR-alternatives.  Negating an
    OR means negating *every* branch, so those come along as conjuncts.
    """
    out = [Atom(atom.lhs, NEGATE.get(atom.op, atom.op), atom.rhs, atom.origin)]
    for alt in atom.alternatives:
        out.append(Atom(alt.lhs, NEGATE.get(alt.op, alt.op), alt.rhs, alt.origin))
    return out


def render(atom: Atom) -> str:
    """An atom back as COBOL-ish text, for re-parsing when negating a guard."""
    def side(t: Term) -> str:
        if t.kind == "const":
            return "'%s'" % t.value if isinstance(t.value, str) else str(t.value)
        return t.name
    return "%s %s %s" % (side(atom.lhs), atom.op, side(atom.rhs))


# --------------------------------------------------------------------------
# Producers and plans
# --------------------------------------------------------------------------

@dataclass
class Producer:
    """Where a value is born, and whether the harness can set it."""
    kind: str                      # 'stub' | 'literal' | 'input' | 'unknown'
    var: str = ""
    site: str = ""
    op_key: str = ""
    value: Any = None
    discriminators: dict = field(default_factory=dict)
    trace: tuple = ()
    inferred: bool = False

    @property
    def slot(self) -> str:
        """Identity of the settable knob. Two obligations reducing to the same
        slot are talking about the same thing."""
        if self.kind == "stub":
            disc = ",".join("%s=%r" % kv for kv in sorted(self.discriminators.items()))
            return "%s[%s].%s" % (self.op_key, disc, self.var)
        # 'unknown' means the walk could not name a producer, not that a
        # different knob is involved: it is still set in the entry state, and
        # giving it its own slot would let two obligations bind the same
        # variable to different values without ever noticing.
        kind = "input" if self.kind in ("input", "unknown") else self.kind
        return "%s:%s" % (kind, self.var)


@dataclass
class Binding:
    slot: str
    producer: Producer
    value: Any
    reason: str
    source: str = "ladder"         # 'ladder' | 'agent'
    atom: Any = None               # the obligation that caused it
    seq: int = 0                   # position in this operation's outcome sequence
    free: bool = False             # the constraint fixed a relationship, not a value


@dataclass
class Plan:
    target: str
    chain: list
    edges: list
    atoms: list
    bindings: list
    rendezvous: list
    open_obligations: list
    derived: list = field(default_factory=list)
    notes: list = field(default_factory=list)
    terminals: dict = field(default_factory=dict)

    @property
    def solved(self) -> bool:
        return bool(self.chain) and not self.open_obligations

    def input_state(self) -> dict:
        return {b.producer.var: b.value for b in self.bindings
                if b.producer.kind in ("input", "unknown")}

    def stub_plan(self) -> dict:
        """Outcomes per operation, in the order they are delivered.

        An external operation returns a *sequence*: a record, then another,
        then end-of-file. Two bindings on the same field are therefore not
        in conflict - they are consecutive outcomes - so ordering matters
        and `seq` carries it.
        """
        out: dict = {}
        for b in sorted(self.bindings, key=lambda x: x.seq):
            if b.producer.kind != "stub":
                continue
            out.setdefault(b.producer.op_key, []).append({
                "when": b.producer.discriminators,
                "set": {b.producer.var: b.value},
                "seq": b.seq,
                "inferred": b.producer.inferred,
            })
        return out

    def flat_state(self) -> dict:
        """Every binding as one variable->value map.

        Only the *first* outcome of each operation is included: a flattened
        view cannot represent a sequence, and the first is what the run
        starts from.
        """
        state = dict(self.input_state())
        for entries in self.stub_plan().values():
            for entry in entries:
                for name, value in entry["set"].items():
                    state.setdefault(name, value)
        return state

    def to_dict(self) -> dict:
        return {
            "target": self.target,
            "chain": self.chain,
            "edges": self.edges,
            "obligations": [{"atom": str(a), "origin": a.origin} for a in self.atoms],
            "derived": [{"atom": str(a), "why": w} for a, w in self.derived],
            "bindings": [{"slot": b.slot, "value": b.value, "reason": b.reason,
                          "free": b.free,
                          "source": b.source, "kind": b.producer.kind,
                          "var": b.producer.var, "op_key": b.producer.op_key,
                          "when": b.producer.discriminators,
                          "inferred": b.producer.inferred,
                          "provenance": list(b.producer.trace)}
                         for b in self.bindings],
            "rendezvous": [{"left": a, "right": b, "value": v}
                           for a, b, v in self.rendezvous],
            "open": [{"atom": str(a), "why": w} for a, w in self.open_obligations],
            "input_state": self.input_state(),
            "stub_plan": self.stub_plan(),
            "flat_state": self.flat_state(),
            "notes": self.notes,
            "terminals": self.terminals,
            "solved": self.solved,
        }
