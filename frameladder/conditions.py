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


def expand_abbreviated(parts: list[str], names: frozenset = frozenset()) -> list[str]:
    """Restore the subject COBOL lets you leave out.

    ``IF WS-RC = '00' OR '04'`` means ``WS-RC = '00' OR WS-RC = '04'``.
    Splitting on OR first strips the subject off every later term, and a
    bare ``'04'`` then reads as a condition-name - silently wrong rather
    than loudly wrong, which is the worst kind.

    ``names`` is the program's level-88 table, when the caller has one. A
    condition-name is a *condition*, not an operand: ``UNTIL WS-IDX >= 11
    OR USER-SEC-EOF`` tests the end-of-file flag on its own, and restoring
    the subject makes it ``WS-IDX >= USER-SEC-EOF`` - a comparison against
    the empty value of a field nobody declares, true from the first
    iteration, so the read loop below it runs zero times and every arm it
    guards is unreachable. Only the data division can tell that bare name
    from an elided operand, which is why the set is a parameter rather
    than a guess.
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
        elif subject and not m and not _is_negated_name(part) \
                and norm(part).upper() not in names:
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


_ALSO = re.compile(r"\s+ALSO\s+", re.I)
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
    # `EVALUATE A ALSO B / WHEN 1 ALSO 3` is two independent comparisons that
    # must both hold, and the subjects pair with the values by position.
    # Pasted together whole it becomes `A ALSO B = 1 ALSO 3`, which is one
    # comparison against a phrase - so the arm's result is decided by whatever
    # a name called "B" happens to hold and the second subject is never
    # tested at all.
    subjects = _ALSO.split(norm(subject))
    values = _ALSO.split(norm(value))
    if len(subjects) > 1 and len(values) == len(subjects):
        parts = []
        for one_subject, one_value in zip(subjects, values):
            if one_value.strip().upper() in ("ANY", "OTHER"):
                continue                  # matches whatever the subject holds
            one = when_condition(one_subject.strip(), one_value.strip())
            # A `FALSE` subject asks for the arm's condition *not* to hold.
            # The single-subject spelling is negated by the caller, which
            # cannot see a FALSE that is only one of several subjects.
            if one_subject.strip().upper() == "FALSE":
                one = "NOT (%s)" % one
            parts.append("(%s)" % one)
        return " AND ".join(parts) if parts else "1 = 1"

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
                    origin: str = "",
                    names: frozenset = frozenset()) -> list[list[Atom]]:
    """Expand a condition into alternatives, each a conjunction of atoms.

    Satisfying any one alternative satisfies the condition, so the ladder
    can take the first that resolves and keep the rest in reserve.

    ``names`` is the program's set of level-88 condition-names, and it
    changes how an abbreviated relation reads - see `expand_abbreviated`.
    Callers with a model in hand should pass it; the default keeps the
    parser usable on bare text.

    Memoised: the interpreter re-evaluates the same handful of conditions
    thousands of times per run, and re-running the relational-operator
    regex each time dominates everything else.
    """
    return [list(alt) for alt in _atoms_cached(_strip_tail(norm(condition)),
                                               negate, origin, names)]


# Words that end a condition rather than belong to it. `IF X = '00' THEN` and
# `IF X = 'Y' NEXT SENTENCE` are both ordinary COBOL, and the tail is part of
# the *statement*, not of the comparison. Left in place it is swallowed by
# whatever operand it touches: the right-hand side of the first becomes the
# literal `'00' THEN`, which nothing the program can hold ever equals, so the
# direction is not merely mis-parsed - it is permanently unsatisfiable, and
# nothing says so.
_TAIL = re.compile(r"\s+(?:THEN|NEXT\s+SENTENCE)\s*$", re.I)


def _strip_tail(condition: str) -> str:
    previous = None
    while previous != condition:
        previous = condition
        condition = _TAIL.sub("", condition).strip()
    return _expand_paren_list(condition)


# `X NOT EQUAL ('00' AND '04' AND '05')` is one abbreviated combined
# relation, not a comparison against a three-word literal. The subject and
# the operator distribute over the connector, which is kept: with AND the
# expansion is a conjunction, with OR a disjunction.
_PAREN_LIST = re.compile(
    r"(?P<subject>[A-Z0-9][A-Z0-9\-]*(?:\s+OF\s+[A-Z0-9][A-Z0-9\-]*)*)\s*"
    r"(?P<op>NOT\s+EQUAL\s+TO|NOT\s+EQUAL|IS\s+NOT\s+EQUAL\s+TO|NOT\s*=|"
    r"EQUAL\s+TO|EQUALS|EQUAL|=|>=|<=|<>|>|<)\s*"
    r"\((?P<items>[^()]+)\)", re.I)
_CONNECTOR = re.compile(r"\s+(AND|OR)\s+", re.I)


def _expand_paren_list(condition: str) -> str:
    """Distribute a relation across a parenthesised list of bare operands.

    Left alone, the whole bracket becomes one right-hand operand and the
    comparison is against a value no field can hold - the same silent
    unsatisfiability as a trailing THEN. Only lists whose members carry no
    relational operator of their own are touched; anything else is a real
    parenthesised expression and is left for the ordinary parser.
    """
    def rewrite(m):
        items = [p.strip() for p in _CONNECTOR.split(m.group("items"))]
        operands, connectors = items[0::2], [c.upper() for c in items[1::2]]
        if len(operands) < 2 or not connectors:
            return m.group(0)
        if len(set(connectors)) != 1:
            return m.group(0)          # mixed AND/OR: not this shape
        if any(_COMPARE.match(o) or not o for o in operands):
            return m.group(0)          # a real expression, not a bare list
        subject, op = m.group("subject"), " ".join(m.group("op").split())
        joined = (" %s " % connectors[0]).join(
            "%s %s %s" % (subject, op, operand) for operand in operands)
        return "(%s)" % joined

    previous = None
    while previous != condition:
        previous = condition
        condition = _PAREN_LIST.sub(rewrite, condition)
    return condition


@lru_cache(maxsize=8192)
def _atoms_cached(condition: str, negate: bool, origin: str,
                  names: frozenset = frozenset()) -> tuple:
    return tuple(tuple(alt) for alt in _condition_atoms(condition, negate,
                                                        origin, names))


# Disjunctive normal form of a conjunction is a cross product, and a
# condition with eight parenthesised alternatives has 256 of them. The point
# of the form is to be enumerable, so past this width the extra alternatives
# are dropped rather than allowed to dominate the run.
MAX_ALTERNATIVES = 64


def _conjoin(groups: list) -> list[list[Atom]]:
    """AND together several already-disjunctive conditions.

    ``(A OR B) AND C`` is ``(A AND C) OR (B AND C)``. Keeping only the first
    alternative of each conjunct - which is what this did - is not an
    approximation, it is a different condition: with A false, B true and C
    true the real answer is true and the kept one is false. GnuCOBOL takes
    that branch and the interpreter did not, so every `IF (X OR Y) AND Z`
    was scored on the wrong arm, and the planner was solving for `X AND Z`
    while believing it had covered the condition. COACTUPC writes the shape
    58 times in one paragraph.
    """
    product: list[list[Atom]] = [[]]
    for alternatives in groups:
        if not alternatives:
            continue
        if len(product) * len(alternatives) > MAX_ALTERNATIVES:
            product = [conj + list(alternatives[0]) for conj in product]
            continue
        product = [conj + list(alt) for conj in product for alt in alternatives]
    return product


def _condition_atoms(condition: str, negate: bool = False,
                     origin: str = "",
                     names: frozenset = frozenset()) -> list[list[Atom]]:
    text = norm(condition)
    if not text:
        return [[]]
    # Stripping a NOT can uncover a bracket and stripping a bracket can
    # uncover a NOT, so neither pass is enough on its own: `(NOT (A = 1))`
    # leaves `NOT (A = 1)` sitting in front of a comparison matcher that
    # reads it as a field called "NOT (A" - an atom no program can satisfy,
    # in a conjunction that is then permanently false.
    while True:
        before = text
        text, negate = _strip_not(text, negate)
        while text.startswith("(") and text.endswith(")") and balanced(text[1:-1]):
            text = text[1:-1].strip()
        if text == before:
            break

    shaped = class_condition(text, negate, origin)
    if shaped is not None:
        return shaped

    ors = expand_abbreviated(split_top(text, "OR"), names)
    if len(ors) > 1:
        if negate:                                   # NOT(A OR B) = !A AND !B
            return _conjoin([_condition_atoms(p, True, origin, names)
                             for p in ors])
        out: list[list[Atom]] = []
        for part in ors:
            out.extend(_condition_atoms(part, False, origin, names))
        return out

    # The subject and the operator may be left out after AND just as after
    # OR: `IF X NOT = '-' AND '+'` is two comparisons on X. Restoring them
    # only for OR leaves the bare literal to be read as a condition-name,
    # which is always false - so the conjunction is unsatisfiable and the
    # true direction of the whole condition cannot be reached.
    ands = expand_abbreviated(split_top(text, "AND"), names)
    if len(ands) > 1:
        if negate:                                   # NOT(A AND B) -> disjuncts
            out = []
            for part in ands:
                out.extend(_condition_atoms(part, True, origin, names))
            return out
        return _conjoin([_condition_atoms(p, False, origin, names)
                         for p in ands])

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


def _strip_not(text: str, negate: bool):
    """Peel leading NOTs off a condition, flipping the sense each time."""
    while text.upper().startswith("NOT "):
        rest = text[4:].strip()
        # NOT binds tighter than AND and OR, so `NOT A AND B` is
        # `(NOT A) AND B`. Absorbing the NOT into everything that follows
        # inverts the sense of the whole expression whenever a top-level
        # operator comes after it -- and since the splits recurse, leaving
        # the NOT in place lets it be applied to its own operand.
        # `NOT (A OR B)` is unaffected: the operator is inside the parens,
        # so neither split sees it here.
        if len(split_top(rest, "OR")) > 1 or len(split_top(rest, "AND")) > 1:
            break
        text, negate = rest, not negate
    return text, negate
