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
    "IS NOT =", "NOT =", "IS NOT", ">=", "<=", "<>", "!=", "=", ">", "<",
]
def _relation_pattern(text: str) -> str:
    """A word-operator needs word boundaries; a symbol cannot have them.

    `NOT =` is both. Wrapping the whole thing in \b..\b puts a boundary
    after the `=`, which cannot match before a quote - so `WS-ST NOT = '00'`
    fell through to the bare `=` and the variable came out as `WS-ST NOT`.
    """
    # Between two words a space is required; between a word and a symbol it
    # is optional, because `NOT=` is as legal as `NOT =` and a mandatory
    # space makes the whole relation fall through to the bare `=`.
    parts = text.split(" ")
    body = re.escape(parts[0])
    for previous, part in zip(parts, parts[1:]):
        joiner = r"\s+" if (previous[-1].isalnum() and part[0].isalnum()) else r"\s*"
        body += joiner + re.escape(part)
    if text[0].isalpha():
        body = r"\b" + body
    if text[-1].isalnum():
        body = body + r"\b"
    return body


_COMPARE = re.compile(
    r"^(.*?)\s*(" + "|".join(_relation_pattern(r) for r in _RELATIONS)
    + r")\s*(.*)$", re.I)

_OP_WORDS = {
    "EQUAL": "=", "EQUALS": "=", "EQUAL TO": "=", "IS EQUAL": "=",
    "IS EQUAL TO": "=", "NOT EQUAL": "!=", "NOT EQUAL TO": "!=",
    "IS NOT EQUAL": "!=", "IS NOT EQUAL TO": "!=", "IS NOT": "!=",
    "NOT =": "!=", "IS NOT =": "!=", "<>": "!=",
    "GREATER": ">", "GREATER THAN": ">", "IS GREATER": ">",
    "IS GREATER THAN": ">", "EXCEEDS": ">",
    "LESS": "<", "LESS THAN": "<", "IS LESS": "<", "IS LESS THAN": "<",
    "NOT GREATER": "<=", "NOT GREATER THAN": "<=", "IS NOT GREATER THAN": "<=",
    "NOT LESS": ">=", "NOT LESS THAN": ">=", "IS NOT LESS THAN": ">=",
    "GREATER THAN OR EQUAL TO": ">=", "LESS THAN OR EQUAL TO": "<=",
}


_OP_WORDS_TIGHT = {k.replace(" ", ""): v for k, v in _OP_WORDS.items()}


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


_NEGATED_NAME = re.compile(r"^\s*NOT\s+[A-Z0-9][A-Z0-9-]*\s*$", re.I)


def _is_negated_name(part: str) -> bool:
    """`NOT SOME-FLAG` is a condition-name being negated, not a bare operand.

    Restoring the subject onto it yields `A = 'NOT SOME-FLAG'` - a comparison
    against a field named after the phrase, which no value can satisfy. It is
    the same mistake as reading `X(2:8)` or `FUNCTION TRIM(X)` as a variable,
    and it makes the arm permanently false rather than merely imprecise.
    """
    return bool(_NEGATED_NAME.match(part or ""))


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
        elif m and subject and not norm(m.group(1)):
            # Only the operator was repeated: `IF A > 5 AND < 10`. The
            # relation is there but the subject is not, and reading the empty
            # left side as a constant compares nothing against 10.
            out.append("%s %s" % (subject[0], part))
        elif subject and not m and not _is_negated_name(part):
            out.append("%s %s %s" % (subject[0], subject[1], part))
        else:
            out.append(part)
    return out


# `WS-X IS NUMERIC` constrains the *shape* of a value rather than its value,
# so it is not a relation and must be recognised before the relational
# operators are tried - otherwise "IS NOT" matches and NUMERIC is read as a
# value to compare against, which looks plausible and is nonsense.
# `IS` is optional in every one of these: `IF WS-X NOT NUMERIC` is as legal
# as `IF WS-X IS NOT NUMERIC`, and CardDemo writes both. Requiring the word
# leaves the short spelling to fall through to the relational parser, which
# finds no operator and files the whole phrase as a condition-name - so the
# test is false however the field is set, and one direction of it is
# unreachable by construction.
_CLASS = re.compile(r"^(.*?)\s+(?:IS\s+)?(NOT\s+)?(NUMERIC|ALPHABETIC(?:-[A-Z]+)?|"
                    r"POSITIVE|NEGATIVE|ZERO)\s*$", re.I)
CLASS_OP = "IS"
CLASS_OP_NOT = "IS-NOT"


def class_condition(text: str, negate: bool, origin: str):
    m = _CLASS.match(norm(text))
    if not m:
        return None
    # Without `IS` the tail is ambiguous: `WS-X = ZERO` also ends in ZERO but
    # is a comparison against the figurative constant. A subject that still
    # contains a relational operator is that case, not a class test.
    if not re.search(r"\bIS\b", norm(text), re.I) and _COMPARE.match(m.group(1)):
        return None
    subject = parse_term(m.group(1))
    if subject.kind != "var":
        return None
    inverted = bool(m.group(2)) != negate
    return [[Atom(subject, CLASS_OP_NOT if inverted else CLASS_OP,
                  Term("const", value=m.group(3).upper()), origin)]]


_WHEN_RANGE = re.compile(r"^(.+?)\s+(?:THRU|THROUGH)\s+(.+)$", re.I)
_LEADING_RELATION = re.compile(
    r"^\s*(" + "|".join(_relation_pattern(r) for r in _RELATIONS) + r")\s*(.*)$",
    re.I)


def when_condition(subject: str, value: str) -> str:
    """The condition an EVALUATE arm stands for.

    `WHEN 1 THRU 9` is a range and `WHEN > 10` is a relation with the subject
    left out; pasted into ``subject = value`` both become a comparison
    against a phrase, which is false for every value the subject can hold.
    """
    body = norm(value)
    on_truth = norm(subject).upper() in ("TRUE", "FALSE")
    negated = False
    while body.upper().startswith("NOT ") and not on_truth:
        body, negated = body[4:].strip(), not negated
    m = _WHEN_RANGE.match(body)
    if m and not on_truth:
        text = "%s >= %s AND %s <= %s" % (subject, m.group(1).strip(),
                                          subject, m.group(2).strip())
        return "NOT (%s)" % text if negated else text
    m = _LEADING_RELATION.match(body)
    if m and m.group(2).strip() and not on_truth:
        text = "%s %s %s" % (subject, norm(m.group(1)), m.group(2).strip())
        return "NOT (%s)" % text if negated else text
    if on_truth:
        return norm(value)
    text = "%s = %s" % (subject, body)
    return "NOT (%s)" % text if negated else text


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
        rest = text[4:].strip()
        # NOT binds tighter than AND and OR, so `NOT A AND B` is
        # `(NOT A) AND B`. Absorbing the NOT into everything that follows
        # inverts the sense of the whole expression whenever a top-level
        # operator comes after it -- and since the splits below recurse,
        # leaving the NOT in place lets it be applied to its own operand.
        # `NOT (A OR B)` is unaffected: the operator is inside the parens,
        # so neither split sees it here.
        if len(split_top(rest, "OR")) > 1 or len(split_top(rest, "AND")) > 1:
            break
        text, negate = rest, not negate
    while text.startswith("(") and text.endswith(")") and balanced(text[1:-1]):
        text = text[1:-1].strip()

    shaped = class_condition(text, negate, origin)
    if shaped is not None:
        return shaped

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

    # The subject and the operator may be left out after AND just as after
    # OR: `IF X NOT = '-' AND '+'` is two comparisons on X. Restoring them
    # only for OR leaves the bare literal to be read as a condition-name,
    # which is always false - so the conjunction is unsatisfiable and the
    # true direction of the whole condition cannot be reached.
    ands = expand_abbreviated(split_top(text, "AND"))
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
    # The spelling that matched need not be the spelling in the table: `NOT=`
    # and `NOT =` are the same operator, so compare with the spaces removed.
    op = _OP_WORDS_TIGHT.get(op_text.replace(" ", ""), op_text)
    if negate:
        op = NEGATE.get(op, op)
    lhs = parse_term(lhs_text)
    return [[Atom(lhs, op, parse_term(r), origin)]
            for r in split_top(rhs_text, "OR")]
