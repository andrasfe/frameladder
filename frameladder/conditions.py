"""COBOL conditions to disjunctive normal form."""

from __future__ import annotations

import re
from functools import lru_cache

from .ir import Atom, NEGATE, Term, balanced, norm, parse_term

# Relational operators, longest first so "NOT EQUAL TO" wins over "EQUAL".
# COBOL lets almost every word here be omitted, so all the spellings appear.
_RELATIONS = [
    "IS NOT EQUAL TO", "IS NOT EQUAL", "NOT EQUAL TO", "IS NOT GREATER THAN",
    "IS NOT LESS THAN", "NOT GREATER THAN", "NOT LESS THAN", "IS EQUAL TO",
    "IS GREATER THAN", "IS LESS THAN", "GREATER THAN OR EQUAL TO",
    "LESS THAN OR EQUAL TO", "EQUAL TO", "GREATER THAN", "LESS THAN",
    "NOT EQUAL", "NOT GREATER", "NOT LESS", "IS EQUAL", "IS GREATER",
    "IS LESS", "EQUALS", "EQUAL", "EXCEEDS", "GREATER", "LESS",
    "NOT =", "IS NOT", ">=", "<=", "<>", "!=", "=", ">", "<",
]
_COMPARE = re.compile(
    r"^(.*?)\s*(" + "|".join(
        (r"\b%s\b" % r.replace(" ", r"\s+")) if r[0].isalpha() else re.escape(r)
        for r in _RELATIONS) + r")\s*(.*)$", re.I)

_OP_WORDS = {
    "EQUAL": "=", "EQUALS": "=", "EQUAL TO": "=", "IS EQUAL": "=",
    "IS EQUAL TO": "=", "NOT EQUAL": "!=", "NOT EQUAL TO": "!=",
    "IS NOT EQUAL": "!=", "IS NOT EQUAL TO": "!=", "IS NOT": "!=",
    "NOT =": "!=", "<>": "!=",
    "GREATER": ">", "GREATER THAN": ">", "IS GREATER": ">",
    "IS GREATER THAN": ">", "EXCEEDS": ">",
    "LESS": "<", "LESS THAN": "<", "IS LESS": "<", "IS LESS THAN": "<",
    "NOT GREATER": "<=", "NOT GREATER THAN": "<=", "IS NOT GREATER THAN": "<=",
    "NOT LESS": ">=", "NOT LESS THAN": ">=", "IS NOT LESS THAN": ">=",
    "GREATER THAN OR EQUAL TO": ">=", "LESS THAN OR EQUAL TO": "<=",
}


def split_top(text: str, keyword: str) -> list[str]:
    """Split on a logical keyword at paren depth zero."""
    parts, depth, buf, i = [], 0, [], 0
    pat, padded = " %s " % keyword, " " + text + " "
    while i < len(padded):
        ch = padded[i]
        depth += (ch == "(") - (ch == ")")
        if depth == 0 and padded[i:i + len(pat)].upper() == pat:
            parts.append("".join(buf))
            buf = []
            i += len(pat) - 1
        else:
            buf.append(ch)
        i += 1
    parts.append("".join(buf))
    return [p.strip() for p in parts if p.strip()]


def expand_abbreviated(parts: list[str]) -> list[str]:
    """Restore the subject COBOL lets you leave out.

    ``IF WS-RC = '00' OR '04'`` means ``WS-RC = '00' OR WS-RC = '04'``.
    Splitting on OR first strips the subject off every later term, and a
    bare ``'04'`` then reads as a condition-name - silently wrong rather
    than loudly wrong, which is the worst kind.
    """
    out, subject = [], None
    for part in parts:
        m = _COMPARE.match(part)
        if m and parse_term(m.group(1)).kind == "var":
            subject = (m.group(1).strip(), norm(m.group(2)))
            out.append(part)
        elif subject and not m:
            out.append("%s %s %s" % (subject[0], subject[1], part))
        else:
            out.append(part)
    return out


def condition_atoms(condition: str, negate: bool = False,
                    origin: str = "") -> list[list[Atom]]:
    """Expand a condition into alternatives, each a conjunction of atoms.

    Satisfying any one alternative satisfies the condition, so the ladder
    can take the first that resolves and keep the rest in reserve.

    Memoised: the interpreter re-evaluates the same handful of conditions
    thousands of times per run, and re-running the relational-operator
    regex each time dominates everything else.
    """
    return [list(alt) for alt in _atoms_cached(norm(condition), negate, origin)]


@lru_cache(maxsize=8192)
def _atoms_cached(condition: str, negate: bool, origin: str) -> tuple:
    return tuple(tuple(alt) for alt in _condition_atoms(condition, negate, origin))


def _condition_atoms(condition: str, negate: bool = False,
                     origin: str = "") -> list[list[Atom]]:
    text = norm(condition)
    if not text:
        return [[]]
    while text.upper().startswith("NOT "):
        text, negate = text[4:].strip(), not negate
    while text.startswith("(") and text.endswith(")") and balanced(text[1:-1]):
        text = text[1:-1].strip()

    ors = expand_abbreviated(split_top(text, "OR"))
    if len(ors) > 1:
        if negate:                                   # NOT(A OR B) = !A AND !B
            merged: list[Atom] = []
            for part in ors:
                alts = _condition_atoms(part, True, origin)
                merged.extend(alts[0] if alts else [])
            return [merged]
        out: list[list[Atom]] = []
        for part in ors:
            out.extend(_condition_atoms(part, False, origin))
        return out

    ands = split_top(text, "AND")
    if len(ands) > 1:
        if negate:                                   # NOT(A AND B) -> disjuncts
            out = []
            for part in ands:
                out.extend(_condition_atoms(part, True, origin))
            return out
        merged = []
        for part in ands:
            alts = _condition_atoms(part, False, origin)
            merged.extend(alts[0] if alts else [])
        return [merged]

    m = _COMPARE.match(text)
    if not m:
        # A bare 88-level condition name. Its truth is the obligation; the
        # solver resolves it against the level-88 table.
        return [[Atom(Term("var", name=text.upper()), "!=" if negate else "=",
                      Term("const", value=True), origin)]]

    lhs_text, op_text, rhs_text = m.group(1), norm(m.group(2)).upper(), m.group(3)
    op = _OP_WORDS.get(op_text, op_text)
    if negate:
        op = NEGATE.get(op, op)
    lhs = parse_term(lhs_text)
    return [[Atom(lhs, op, parse_term(r), origin)]
            for r in split_top(rhs_text, "OR")]
