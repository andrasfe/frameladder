"""Terms, atoms and the small algebra the ladder reasons in."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Any

# Memoisation sizes. A program has a fixed vocabulary of condition texts and
# operand spellings, so these caches saturate early and then never miss; the
# limit exists to bound a process that loads several programs, not to bound
# one. Nothing here is order-dependent: every memoised function below is a
# pure function of its arguments returning an immutable value, so the cache
# can only change how long an answer takes, never which answer it is.
_CACHE = 1 << 16

_LITERAL = re.compile(r"^'([^']*)'$|^\"([^\"]*)\"$|^([+-]?\d+(?:\.\d+)?)$")
# X'0A1B' - hexadecimal, two digits per byte.
_HEX_LITERAL = re.compile(r"^[Xx]'([0-9A-Fa-f]*)'$|^[Xx]\"([0-9A-Fa-f]*)\"$")
# Z'..' (null-terminated) and N'..' (national) are ordinary literals wearing
# a prefix; without this they parse as a variable called Z or N.
_QUOTED_PREFIXED = re.compile(r"^[ZzNn]'([^']*)'$|^[ZzNn]\"([^\"]*)\"$")
_SUBSCRIPTED = re.compile(r"^([A-Z0-9][A-Z0-9-]*)\s*\(([^)]*)\)$", re.I)
# A qualified reference is ONE name. Splitting `ACCT-ID OF MAPAI` on spaces
# yields three targets, and writing to the group member `MAPAI` clobbers every
# field of the map area for the sake of one screen field.
_TARGET = re.compile(
    r"([A-Z0-9][A-Z0-9-]*(?:\s+(?:OF|IN)\s+[A-Z0-9][A-Z0-9-]*)*)"
    r"\s*(?:\(([^)]*)\))?", re.I)

FIGURATIVE = {"ZERO": 0, "ZEROS": 0, "ZEROES": 0, "SPACE": " ", "SPACES": " ",
              "LOW-VALUE": "\x00", "LOW-VALUES": "\x00", "HIGH-VALUE": "\xff",
              "HIGH-VALUES": "\xff", "NULL": "", "NULLS": ""}
NEGATE = {"=": "!=", "!=": "=", ">": "<=", "<=": ">", "<": ">=", ">=": "<",
          "IS": "IS-NOT", "IS-NOT": "IS"}

# CICS response and value constants. Platform vocabulary, fixed the way HTTP
# status codes are - not an assumption about how anyone names anything.
CICS_CONSTANTS = {
    "DFHRESP": {"NORMAL": 0, "ERROR": 1, "RDATT": 2, "WRBRK": 3, "EOF": 4,
                "EODS": 5, "EOC": 6, "INBFMH": 7, "ENDINPT": 8, "NONVAL": 9,
                "NOSTART": 10, "TERMIDERR": 11, "FILENOTFOUND": 12,
                "NOTFND": 13, "DUPREC": 14, "DUPKEY": 15, "INVREQ": 16,
                "IOERR": 17, "NOSPACE": 18, "NOTOPEN": 19, "ENDFILE": 20,
                "ILLOGIC": 21, "LENGERR": 22, "QZERO": 23, "SIGNAL": 24,
                "QBUSY": 25, "ITEMERR": 26, "PGMIDERR": 27, "TRANSIDERR": 28,
                "ENDDATA": 29, "INVTSREQ": 30, "EXPIRED": 31, "RETPAGE": 32,
                "RTEFAIL": 33, "RTESOME": 34, "TSIOERR": 35, "MAPFAIL": 36,
                "INVERRTERM": 37, "INVMPSZ": 38, "IGREQID": 39, "OVERFLOW": 40,
                "INVLDC": 41, "NOSTG": 42, "JIDERR": 43, "QIDERR": 44,
                "NOJBUFSP": 45, "DSSTAT": 46, "SELNERR": 47, "FUNCERR": 48,
                "UNEXPIN": 49, "NOPASSBKRD": 50, "NOPASSBKWR": 51},
    "DFHVALUE": {"NORMAL": 0, "CURSOR": 1},
}

# The attention identifier: which key the user pressed. CICS puts it in
# EIBAID at task start, and a screen program's whole control flow is one
# `EVALUATE EIBAID`. The names live in the standard `DFHAID` copybook, which
# ships with CICS and is therefore almost never in an application repository -
# so every one of them parses as a field nobody declares, holding the empty
# default, and no arm can match but WHEN OTHER.
#
# This is platform vocabulary in the same sense as DFHRESP or an HTTP status
# code: the values are fixed by CICS, not chosen by whoever wrote the program,
# and knowing them is not a guess about naming. The bytes below are the
# display characters the copybook assigns.
#
# The limitation, stated plainly: this resolves during parsing, which has no
# model to consult, so a site that ships a *modified* DFHAID gets the standard
# values rather than its own. The names are IBM's and redefining them is close
# to unheard of, but it is a real assumption and not a checked one - unlike
# the rest of the platform vocabulary here, which only applies where the
# source itself puts a field in that channel.
AID_VALUES = {
    "DFHNULL": "\x00", "DFHENTER": "'", "DFHCLEAR": "_", "DFHCLRP": "\x6a",
    "DFHPEN": "=", "DFHOPID": "W", "DFHMSRE": "X", "DFHSTRF": "h",
    "DFHTRIG": '"', "DFHPA1": "%", "DFHPA2": ">", "DFHPA3": ",",
    "DFHPF1": "1", "DFHPF2": "2", "DFHPF3": "3", "DFHPF4": "4",
    "DFHPF5": "5", "DFHPF6": "6", "DFHPF7": "7", "DFHPF8": "8",
    "DFHPF9": "9", "DFHPF10": ":", "DFHPF11": "#", "DFHPF12": "@",
    "DFHPF13": "A", "DFHPF14": "B", "DFHPF15": "C", "DFHPF16": "D",
    "DFHPF17": "E", "DFHPF18": "F", "DFHPF19": "G", "DFHPF20": "H",
    "DFHPF21": "I", "DFHPF22": "\xa2", "DFHPF23": ".", "DFHPF24": "<",
}


_QUOTED_RUN = re.compile(r"'[^']*'|\"[^\"]*\"")


_WHITESPACE = re.compile(r"\s+")


@lru_cache(maxsize=200_000)
def _normed(text: str) -> str:
    out, at = [], 0
    for m in _QUOTED_RUN.finditer(text):
        out.append(_WHITESPACE.sub(" ", text[at:m.start()]))
        out.append(m.group(0))
        at = m.end()
    out.append(_WHITESPACE.sub(" ", text[at:]))
    return "".join(out).strip()


def norm(text: str) -> str:
    """Conditions arrive folded across source lines; flatten them first.

    Memoised, and the patterns are compiled once. A run asks this the same
    question tens of millions of times - it sits under `parse_term`,
    `base_name` and `condition_atoms`, each called per operand per statement
    - and `re.sub` with a pattern *string* pays the module's cache lookup on
    every one of them. Measured at 68.8M calls and 143.6s cumulative on one
    program before caching.

    Everything outside a quoted literal is whitespace-insensitive and
    everything inside one is not. Collapsing runs of spaces indiscriminately
    shortens `MOVE '   ' TO X` and `IF X = '  A00B'` by a character each
    time, so a comparison against an edit mask, a blank key or any literal
    with two spaces in it is decided against a literal the program does not
    contain.
    """
    return _normed(text.replace("\n", " ")) if text else ""


@dataclass(frozen=True)
class Term:
    kind: str                      # 'const' | 'var'
    name: str = ""
    value: Any = None
    index: tuple = ()
    # `WS-A(3:2)` names the same field as `WS-A` but a different two bytes of
    # it, so the slice belongs to the reference and not to the declaration.
    # Keeping `name` the bare field is what lets provenance, liveness and the
    # ladder go on treating it as the field it is.
    refmod: tuple = ()             # (start-expression, length-expression)
    # An intrinsic is a function of its arguments, not a field called
    # "FUNCTION TRIM(X)". `name` carries the first variable argument so the
    # obligation still lands on something the harness can set.
    func: str = ""
    args: tuple = ()

    @property
    def key(self) -> str:
        if self.kind == "const":
            return repr(self.value)
        if self.func:
            return "%s(%s)" % (self.func, ",".join(a.key for a in self.args))
        return self.name + ("(%s)" % ",".join(str(i) for i in self.index)
                            if self.index else "") + (
            "(%s:%s)" % self.refmod if self.refmod else "")

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


# `ACSHLIMI OF CACTUPAI` names one field and says which group it belongs to,
# for disambiguation. Keeping the qualifier in the name makes the reference
# match no declaration, carry no PIC and bind to nothing - and CardDemo's
# screen handling is written almost entirely this way.
_QUALIFIED = re.compile(r"^(.*?)\s+(?:OF|IN)\s+[A-Z0-9][A-Z0-9-]*"
                        r"(?:\s+(?:OF|IN)\s+[A-Z0-9][A-Z0-9-]*)*\s*$", re.I)


@lru_cache(maxsize=_CACHE)
def base_name(text: str) -> str:
    """The field a qualified reference names, without its qualifier.

    Used for *lookups* only. The qualifier must stay part of the identity:
    a BMS map has the same field name under its input and its output area,
    and collapsing them makes two separately satisfiable conditions collide.
    """
    m = _QUALIFIED.match(norm(text))
    return m.group(1).strip().upper() if m else norm(text).upper()


# An intrinsic call: `FUNCTION TRIM (WS-X)`, and the no-argument spellings
# `FUNCTION CURRENT-DATE`. Read as a plain identifier the whole call becomes a
# field nobody declares, whose value is therefore the empty default - so
# `FUNCTION TEST-NUMVAL-C(X) = 0` is false however X is set, and that
# direction cannot be planned or sampled into.
_FUNCTION = re.compile(r"^FUNCTION\s+([A-Z][A-Z0-9-]*)\s*(\(.*\))?$", re.I)
_LENGTH_OF = re.compile(r"^LENGTH\s+OF\s+([A-Z0-9][A-Z0-9-]*(?:\s*\(.*\))?)$", re.I)


def _split_args(text: str) -> list:
    """Top-level comma split, so `MOD(A, B)` is two arguments and
    `TRIM(X(1:N))` is one.

    The standard makes a space as good a separator as a comma, and the
    reference manuals write it that way: `FUNCTION MAX(A B C)`,
    `FUNCTION MOD(A B)`, `FUNCTION TRIM(X TRAILING)`.  Split on the comma
    alone and every one of those is a single argument named after the whole
    text, which no field carries - so MAX returns 0, MOD returns 0, and the
    condition testing the result has one reachable direction.

    An argument may also be an arithmetic expression, and there the space is
    a separator *inside* one argument (`MOD(A + 1, 3)`).  The two are told
    apart by the rule COBOL already relies on elsewhere: an arithmetic
    operator has to stand alone, so a piece containing one is left whole.
    """
    out, depth, buf = [], 0, []
    for ch in text:
        depth += (ch == "(") - (ch == ")")
        if ch == "," and depth == 0:
            out.append("".join(buf))
            buf = []
        else:
            buf.append(ch)
    out.append("".join(buf))
    pieces = [p.strip() for p in out if p.strip()]
    split: list = []
    for piece in pieces:
        words = _top_level_words(piece)
        if (len(words) > 1 and not any(w in _ARITH_OPS for w in words)
                and not _LENGTH_OF.match(piece)):
            split.extend(words)
        else:
            split.append(piece)
    return split


def _top_level_words(text: str) -> list:
    """Whitespace split that keeps brackets and quotes together."""
    out, depth, quote, buf = [], 0, "", []
    for ch in text:
        if quote:
            buf.append(ch)
            if ch == quote:
                quote = ""
            continue
        if ch in "'\"":
            quote = ch
            buf.append(ch)
            continue
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch.isspace() and depth == 0:
            if buf:
                out.append("".join(buf))
                buf = []
            continue
        buf.append(ch)
    if buf:
        out.append("".join(buf))
    return out


def _split_refmod(text: str):
    """Split ``head ( start : length )`` into its parts, or None.

    The head may be qualified (`TRNAMTI OF COTRN2AI`), which is why this
    cannot be a single anchored regex on an identifier.
    """
    if not text.endswith(")"):
        return None
    depth = 0
    for i in range(len(text) - 1, -1, -1):
        depth += (text[i] == ")") - (text[i] == "(")
        if depth == 0:
            head, inside = text[:i].strip(), text[i + 1:-1]
            if not head:
                return None
            parts = _split_top_colon(inside)
            if len(parts) != 2:
                return None
            return head, parts[0].strip(), parts[1].strip()
    return None


def _split_top_colon(text: str) -> list:
    out, depth, buf = [], 0, []
    for ch in text:
        depth += (ch == "(") - (ch == ")")
        if ch == ":" and depth == 0:
            out.append("".join(buf))
            buf = []
        else:
            buf.append(ch)
    out.append("".join(buf))
    return out


@lru_cache(maxsize=_CACHE)
def parse_term(text: str) -> Term:
    """Read one operand.

    Memoised: a `Term` is frozen, so what comes back cannot be altered by
    whoever asked for it, and the same operand text is re-read once per
    statement per run - fourteen million times on a 1,500-line program.
    """
    text = norm(text).strip(".")
    while text.startswith("(") and text.endswith(")") and balanced(text[1:-1]):
        text = text[1:-1].strip()
    if not text:
        return Term("const", value="")
    # A hexadecimal literal is a constant, and reading it as a name is worse
    # than merely losing it: `88 FC-INVALID-DATE VALUE X'00...'` becomes a
    # condition-name whose value is a variable nobody writes, so every arm
    # testing it is dead and the obligation on it can never be met. Z'..' is
    # the null-terminated form and N'..' the national one; both are still
    # literals whatever their encoding.
    m = _HEX_LITERAL.match(text)
    if m:
        digits = m.group(1) if m.group(1) is not None else m.group(2)
        if len(digits) % 2 == 0:
            try:
                return Term("const",
                            value=bytes.fromhex(digits).decode("latin-1"))
            except ValueError:
                pass
    m = _QUOTED_PREFIXED.match(text)
    if m:
        return Term("const",
                    value=m.group(1) if m.group(1) is not None else m.group(2))
    # `LENGTH OF X` is the non-FUNCTION spelling of FUNCTION LENGTH(X) and is
    # the one the language reserves; CardDemo writes it 127 times. Read as a
    # name it becomes a field nobody declares, so every reference modification
    # built on it starts at byte 1 and every group move lands on the wrong
    # half of the record.
    lo = _LENGTH_OF.match(text)
    if lo:
        inner = parse_term(lo.group(1))
        if inner.kind == "var" and inner.name:
            return Term("var", name=inner.name, func="LENGTH", args=(inner,))
    fn = _FUNCTION.match(text)
    if fn:
        raw = (fn.group(2) or "")[1:-1]
        args = tuple(parse_term(a) for a in _split_args(raw))
        carrier = next((a.name for a in args if a.kind == "var" and a.name), "")
        return Term("var", name=carrier, func=fn.group(1).upper(), args=args)
    slic = _split_refmod(text)
    if slic and not _LITERAL.match(text):
        head, start, length = slic
        inner = parse_term(head)
        if inner.kind == "var" and not inner.refmod:
            return Term("var", name=inner.name, index=inner.index,
                        refmod=(start, length))
    m = _LITERAL.match(text)
    if m:
        if m.group(3) is not None:
            num = m.group(3)
            return Term("const", value=float(num) if "." in num else int(num))
        return Term("const", value=m.group(1) if m.group(1) is not None else m.group(2))
    upper = text.upper()
    if upper in FIGURATIVE:
        return Term("const", value=FIGURATIVE[upper])
    if upper in AID_VALUES:
        return Term("const", value=AID_VALUES[upper])
    m = _SUBSCRIPTED.match(text)
    if m:
        head = m.group(1).upper()
        # DFHRESP(NOTFND) is a compile-time constant the translator replaces
        # with a number; read as a subscript it becomes an array nobody can
        # set, and the obligation on it is unsatisfiable.
        if head in CICS_CONSTANTS:
            return Term("const", value=CICS_CONSTANTS[head].get(
                m.group(2).strip().upper(), 0))
        # Subscripts may be separated by a comma or by nothing but space:
        # `WS-CELL(I, J)` and `WS-CELL(I J)` are the same reference. Split on
        # the comma alone and a two-dimensional table collapses to its first
        # row, because the whole "I J" evaluates to no number at all.
        # A subscript may itself be an expression - `WS-E(IX + 1)` is the
        # ordinary way to look at the next entry - and an arithmetic operator
        # must stand alone in COBOL, so the same whitespace that separates two
        # dimensions also separates the three tokens of one. Split naively,
        # a one-dimensional table is read as three-dimensional and the
        # reference falls back to occurrence 1.
        return Term("var", name=head,
                    index=tuple(_merge_subscript_operators(
                        [s for s in re.split(r"[,\s]+", m.group(2).strip()) if s])))
    return Term("var", name=upper)


def _merge_subscript_operators(parts: list) -> list:
    out: list = []
    pending = False
    for part in parts:
        if pending:
            out[-1] = out[-1] + " " + part
            pending = part in _ARITH_OPS
            continue
        if part in _ARITH_OPS and out:
            out[-1] = out[-1] + " " + part
            pending = True
            continue
        out.append(part)
    return out


_ARITH_OPS = {"+", "-", "*", "/", "**"}


def arith_tokens(text: str) -> list:
    """Split an arithmetic expression into operands, operators and parens.
    A fresh list every time, because a caller may consume it.
    """
    return list(_arith_tokens(text))


@lru_cache(maxsize=_CACHE)
def _arith_tokens(text: str) -> tuple:
    """The tokens themselves, memoised. See `arith_tokens`.

    COBOL identifiers contain hyphens, so `WS-A - WS-B` and `WS-A-WS-B` are
    different things and the language settles it with whitespace: an
    arithmetic operator must stand alone.  Tokenising on that rule is what
    keeps `ACCT-CURR-BAL` one name instead of three subtractions.
    """
    spaced = norm(text).replace("(", " ( ").replace(")", " ) ")
    tokens = [t for t in spaced.split(" ") if t]
    # `LENGTH OF X` is one operand written as three words. Left split it
    # evaluates as a field called LENGTH followed by two tokens the grammar
    # has no rule for, so the expression silently comes out as whatever the
    # first operand was - and `X(LENGTH OF A + 1:n)` then slices from byte 1.
    merged: list = []
    index = 0
    while index < len(tokens):
        if (tokens[index].upper() == "LENGTH" and index + 2 < len(tokens)
                and tokens[index + 1].upper() == "OF"):
            merged.append(" ".join(tokens[index:index + 3]))
            index += 3
            continue
        # `FUNCTION MAX(A B)` is one operand written as two tokens, and the
        # bracket merge below only ever joins a bracket to the token in front
        # of it. Left split, `FUNCTION` is a field nobody declares and the
        # expression evaluates to whatever that default is - so a COMPUTE
        # over an intrinsic writes 0 and every test on the result is fixed.
        if tokens[index].upper() == "FUNCTION" and index + 1 < len(tokens):
            merged.append("FUNCTION " + tokens[index + 1])
            index += 2
            continue
        # `WS-TOTAL (I) + 1` is a subscripted operand, not a name multiplied
        # by a bracket: COBOL has no implicit multiplication, so a `(` that
        # follows an operand belongs to that operand. Left split, the whole
        # expression fails to parse and the COMPUTE writes nothing at all.
        if (tokens[index] == "(" and merged
                and merged[-1] not in _ARITH_OPS
                and merged[-1] not in ("(", ")")):
            depth, body, index = 0, [], index
            while index < len(tokens):
                token = tokens[index]
                if token == "(":
                    depth += 1
                elif token == ")":
                    depth -= 1
                body.append(token)
                index += 1
                if depth == 0:
                    break
            merged[-1] = merged[-1] + "(" + " ".join(body[1:-1]) + ")"
            continue
        merged.append(tokens[index])
        index += 1
    return tuple(merged)


@lru_cache(maxsize=_CACHE)
def is_arithmetic(text: str) -> bool:
    """True when the text is an expression rather than a single operand."""
    tokens = _arith_tokens(text)
    return any(t in _ARITH_OPS for t in tokens) and len(tokens) > 1


def eval_arith(text: str, resolve) -> float:
    """Evaluate an arithmetic expression, resolving operands through
    `resolve`.  Raises ValueError when the text is not arithmetic."""
    tokens = arith_tokens(text)
    pos = [0]

    def peek():
        return tokens[pos[0]] if pos[0] < len(tokens) else ""

    def take():
        pos[0] += 1
        return tokens[pos[0] - 1]

    def primary():
        token = take()
        if token == "(":
            value = expression()
            if peek() == ")":
                take()
            return value
        if token == "-":
            return -primary()
        if token == "+":
            return primary()
        return float(resolve(token))

    def power():
        value = primary()
        while peek() == "**":
            take()
            value = value ** primary()
        return value

    def term():
        value = power()
        while peek() in ("*", "/"):
            op = take()
            other = power()
            value = value * other if op == "*" else (value / other if other else 0.0)
        return value

    def expression():
        value = term()
        while peek() in ("+", "-"):
            op = take()
            other = term()
            value = value + other if op == "+" else value - other
        return value

    result = expression()
    if pos[0] != len(tokens):
        raise ValueError("trailing tokens in %r" % text)
    return result


def move_targets(text: str) -> list[str]:
    """Base names written by a MOVE.

    Splitting on whitespace is wrong: in ``MOVE TR-CNT TO WS-TRCT (CR-CNT)``
    the subscript is a *read*, and counting it as a write invents a def-use
    edge that derails the whole provenance walk.
    """
    return [norm(m.group(1)).upper() for m in _TARGET.finditer(norm(text))]


def move_target_terms(text: str) -> list:
    """The same targets, as terms, so a slice survives.

    ``move_targets`` deliberately returns base names: provenance asks *which
    field is written*, and `B(3:2)` is a write to `B`. Execution needs the
    other half of the answer. ``MOVE A TO B(n:m)`` replaces m bytes of B and
    leaves the rest alone, and assigning the whole of B instead is how a
    commarea assembled in two pieces ends up holding only the second one.
    """
    out = []
    for m in _TARGET.finditer(norm(text)):
        try:
            term = parse_term(m.group(0))
        except Exception:                                        # noqa: BLE001
            continue
        if term.kind == "var" and term.name:
            out.append(term)
    return out


def class_holds(value: Any, klass: str) -> bool:
    """A class condition asks about the *shape* of the bytes.

    Without this the comparison table raises KeyError and the handler returns
    True for both `IS` and `IS-NOT` - so every class test is true whichever
    way it is asked, and neither direction can ever be planned for.
    """
    klass = (klass or "").upper()
    text = "" if value is None else str(value)
    if klass == "NUMERIC":
        return text.strip() != "" and text.strip().lstrip("+-").isdigit()
    if klass.startswith("ALPHABETIC"):
        letters = [c for c in text if not c.isspace()]
        if klass == "ALPHABETIC-LOWER":
            return bool(letters) and all(c.islower() for c in letters)
        if klass == "ALPHABETIC-UPPER":
            return bool(letters) and all(c.isupper() for c in letters)
        return bool(letters) and all(c.isalpha() for c in letters)
    try:
        number = float(str(value).strip())
    except (TypeError, ValueError):
        return False
    if klass == "POSITIVE":
        return number > 0
    if klass == "NEGATIVE":
        return number < 0
    if klass == "ZERO":
        return number == 0
    return False


# LOW-VALUE and HIGH-VALUE name a byte, and a figurative constant takes the
# size of the item it is compared with. Trailing-space stripping cannot
# reconcile them, because neither byte is a space - so a field holding twenty
# NULs would come out unequal to LOW-VALUES, which is how a screen program
# tests an empty input field. One rule, here, because the planner, the lift
# and the interpreter all decide conditions through this function and a
# second copy of it is how they come to disagree.
_FIGURATIVE_BYTES = ("\x00", "\xff")


def _widen(value: Any, other: Any) -> Any:
    if (isinstance(value, str) and value in _FIGURATIVE_BYTES
            and isinstance(other, str) and len(other) > 1):
        return value * len(other)
    return value


def holds(left: Any, op: str, right: Any) -> bool:
    """Compare the way COBOL would: mixed alphanumeric and numeric operands
    are reconciled rather than raising."""
    if op in ("IS", "IS-NOT"):
        result = class_holds(left, str(right))
        return result if op == "IS" else not result
    left, right = _widen(left, right), _widen(right, left)
    try:
        if isinstance(left, str) != isinstance(right, str):
            try:
                left, right = float(str(left).strip()), float(str(right).strip())
            except (TypeError, ValueError):
                left, right = str(left).strip(), str(right).strip()
        elif isinstance(left, str):
            # Two alphanumeric operands are compared byte for byte after the
            # shorter is padded on the *right* with spaces. Stripping both
            # ends instead makes leading blanks invisible, so `'  ABC'` and
            # `'ABC'` compare equal - a field that a JUSTIFIED move, an
            # editing PIC or a right-aligned screen field filled cannot then
            # be told apart from one that was not, and the ordering
            # comparisons on it come out backwards.
            width = max(len(left), len(right))
            left, right = left.ljust(width), right.ljust(width)
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

        One outcome can name several fields, though, and that is the common
        case rather than the exotic one: a terminal read fills every field on
        the screen and a record read fills every field of the record. Those
        bindings differ by variable, not by position, so they are the same
        delivery - `seq` says so - and emitting one entry each described a
        call that returns one field and then returns again. The consumer
        delivers the first matching entry and stops, so nine of ten planned
        fields were dropped at the one moment they were supposed to arrive.
        """
        out: dict = {}
        index: dict = {}
        for b in sorted(self.bindings, key=lambda x: x.seq):
            if b.producer.kind != "stub":
                continue
            when = b.producer.discriminators
            slot = (b.producer.op_key, tuple(sorted(when.items())), b.seq)
            entry = index.get(slot)
            if entry is None:
                entry = {"when": when, "set": {}, "seq": b.seq,
                         "inferred": b.producer.inferred}
                index[slot] = entry
                out.setdefault(b.producer.op_key, []).append(entry)
            entry["set"][b.producer.var] = b.value
            entry["inferred"] = entry["inferred"] or b.producer.inferred
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
