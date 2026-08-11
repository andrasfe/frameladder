"""Naming one decision, when the two tools count decisions differently.

A harness and this planner both know which branch directions are still
uncovered, and neither can say so in the other's words. `frameladder` names a
decision by its *statement position inside its paragraph* (`cobol._stamp_ordinals`),
because a COPY expansion puts many decisions on one source line and the line
cannot tell them apart. Specter names it by a 0-based counter *per (paragraph,
kind)*. Both are defensible; they are not the same number.

Measured on `COTRN02C`, the four `IF`s in `MAIN-PARA` are ordinals 3, 8, 12
and 22 here and 0, 1, 2, 3 there. The failure this produces is the bad kind:
Specter's third `IF` is ordinal 3, which *is* a valid ordinal here, so it
resolves silently to the wrong decision instead of raising anything. A run
reports a plan, reaches the paragraph, and covers a direction nobody asked
for. That is exactly what came back from the field: 268 targets analysed, one
exported, and the witness landing on `1000-INITIALIZATION` but not on its
uncovered direction.

So an ordinal from outside is treated as a hint and never as an identity,
unless the profile explicitly claims it was produced by this tool. What does
carry across is what the *program* says rather than what either tool counts:
the condition text, and the source line. Those are properties of the COBOL,
so both sides can read them off the same file.

Resolution is reported, never assumed. Every entry comes back with how it was
matched, and an entry that matched several decisions says so and targets all
of them - over-targeting costs planning budget, while silently picking one of
five costs a witness that means nothing.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

# Kinds, as the two sides spell them. `branches_of` emits IF / WHEN / LOOP /
# PHRASE; a harness reading the same source is as likely to say EVALUATE for
# the arm or AT END for the phrase.
_KIND_ALIASES = {
    "IF": "IF", "ELSE": "IF",
    "WHEN": "WHEN", "EVALUATE": "WHEN", "WHEN-OTHER": "WHEN",
    "SEARCH": "WHEN",
    "LOOP": "LOOP", "PERFORM": "LOOP", "PERFORM_UNTIL": "LOOP",
    "PERFORM-UNTIL": "LOOP", "PERFORM UNTIL": "LOOP",
    "PERFORM_VARYING": "LOOP", "PERFORM-VARYING": "LOOP",
    "PERFORM VARYING": "LOOP", "UNTIL": "LOOP", "VARYING": "LOOP",
    "PHRASE": "PHRASE", "AT_END": "PHRASE", "AT-END": "PHRASE",
    "INVALID_KEY": "PHRASE", "INVALID-KEY": "PHRASE",
    "AT END": "PHRASE", "INVALID KEY": "PHRASE",
}

# Ways of writing one relation. COBOL spells most comparisons two or three
# ways and a harness may echo whichever the source used, so the text is
# reduced to one spelling before either side is compared. This is COBOL's own
# vocabulary, not any program's: nothing here mentions a field name.
_RELATIONS = (
    (r"\bIS\s+NOT\s+GREATER\s+THAN\s+OR\s+EQUAL\s+TO\b", " < "),
    (r"\bIS\s+NOT\s+LESS\s+THAN\s+OR\s+EQUAL\s+TO\b", " > "),
    (r"\bNOT\s+GREATER\s+THAN\s+OR\s+EQUAL\s+TO\b", " < "),
    (r"\bNOT\s+LESS\s+THAN\s+OR\s+EQUAL\s+TO\b", " > "),
    (r"\bGREATER\s+THAN\s+OR\s+EQUAL\s+TO\b", " >= "),
    (r"\bLESS\s+THAN\s+OR\s+EQUAL\s+TO\b", " <= "),
    (r"\bIS\s+NOT\s+EQUAL\s+TO\b", " NOT = "),
    (r"\bIS\s+NOT\s+GREATER\s+THAN\b", " NOT > "),
    (r"\bIS\s+NOT\s+LESS\s+THAN\b", " NOT < "),
    (r"\bNOT\s+EQUAL\s+TO\b", " NOT = "),
    (r"\bNOT\s+EQUALS?\b", " NOT = "),
    (r"\bNOT\s+GREATER\s+THAN\b", " NOT > "),
    (r"\bNOT\s+LESS\s+THAN\b", " NOT < "),
    (r"\bIS\s+GREATER\s+THAN\b", " > "),
    (r"\bIS\s+LESS\s+THAN\b", " < "),
    (r"\bIS\s+EQUAL\s+TO\b", " = "),
    (r"\bGREATER\s+THAN\b", " > "),
    (r"\bLESS\s+THAN\b", " < "),
    (r"\bEQUAL\s+TO\b", " = "),
    (r"\bEQUALS\b", " = "),
    (r"\bIS\s+NOT\b", " NOT "),
    (r"\bGREATER\b", " > "),
    (r"\bLESS\b", " < "),
    (r"\bEQUAL\b", " = "),
    (r"\bIS\b", " "),
)

# Words a harness may put in front of the condition because it read them off
# the statement. They carry no identity.
_LEADERS = ("IF ", "WHEN ", "UNTIL ", "EVALUATE ", "PERFORM UNTIL ",
            "PERFORM VARYING ", "VARYING ")


def normalize_kind(text: str) -> str:
    key = " ".join(str(text or "").upper().split())
    return _KIND_ALIASES.get(key, key or "IF")


def normalize_condition(text: str) -> str:
    """One spelling for one condition, so both sides can compare them.

    Deliberately syntactic. It upper-cases, unifies quote characters and
    relation spellings, and drops punctuation that COBOL treats as noise. It
    does not evaluate, reorder operands or resolve names - two conditions that
    mean the same thing but are written differently stay different, which is
    the safe direction: a missed match is reported as unmatched and falls
    through to the line, while a wrong match is silent.
    """
    text = str(text or "")
    if not text.strip():
        return ""
    text = text.upper().replace('"', "'")
    text = " ".join(text.split())
    for leader in _LEADERS:
        while text.startswith(leader):
            text = text[len(leader):].lstrip()
    text = text.rstrip(".")
    for pattern, replacement in _RELATIONS:
        text = re.sub(pattern, replacement, text)
    # Parentheses are grouping, and a harness may keep or drop the outermost
    # pair. Inner ones are structure and are left alone.
    text = " ".join(text.split())
    while text.startswith("(") and text.endswith(")") and _balanced(text[1:-1]):
        text = text[1:-1].strip()
    return " ".join(text.split())


def _balanced(text: str) -> bool:
    depth = 0
    for char in text:
        depth += (char == "(") - (char == ")")
        if depth < 0:
            return False
    return depth == 0


def normalize_direction(value) -> list:
    """Which way, as a list so that "unspecified" can mean both.

    A harness that names a decision without naming a direction is saying the
    whole decision is open. Planning both ways is right; picking one is a
    guess that shows up later as a witness on the direction nobody wanted.
    """
    if value is None:
        return [True, False]
    if isinstance(value, bool):
        return [value]
    token = str(value).strip().upper()
    if token in ("T", "TRUE", "Y", "YES", "1", "TAKEN", "THEN", "MATCH"):
        return [True]
    if token in ("F", "FALSE", "N", "NO", "0", "NOT-TAKEN", "NOT_TAKEN",
                 "ELSE", "FALL-THROUGH", "FALLTHROUGH", "NOMATCH", "NO-MATCH"):
        return [False]
    if token in ("", "BOTH", "ANY", "*"):
        return [True, False]
    return [True, False]


@dataclass(frozen=True)
class Match:
    """One branch direction this planner can actually target."""

    key: tuple                  # (PARAGRAPH, ordinal, KIND, direction)
    how: str                    # which field identified it
    entry: int                  # index in the profile's list
    probe: str = ""             # the harness's own id, echoed back untouched


def program_mismatch(capability, program) -> str:
    """Whether this profile was written about some other program.

    Worth a check rather than trust. Paragraph names repeat across a shop's
    programs - every CICS program in the CardDemo corpus has a `MAIN-PARA` -
    so a profile pointed at the wrong source does not fail, it resolves. One
    aimed at `COTRN02C` and run against `COSGN00C` matched 16 of its 40
    entries and exported 7 candidates, all meaningless.

    Names are compared loosely because the two sides have different ideas of
    what a program is called: a file stem, a PROGRAM-ID, a member name, with
    or without an extension. Only a real disagreement is reported.
    """
    stated = str(getattr(capability, "program", "") or "").strip().upper()
    if not stated:
        return ""
    actual = str(getattr(program, "name", "") or "").strip().upper()
    stated = stated.rsplit("/", 1)[-1].rsplit(".", 1)[0]
    actual = actual.rsplit("/", 1)[-1].rsplit(".", 1)[0]
    if not actual or stated == actual:
        return ""
    return ("profile names %s, this is %s - paragraph names repeat across "
            "programs, so a mismatched profile resolves rather than fails"
            % (stated, actual))


@dataclass
class Resolution:
    matches: tuple = ()
    unresolved: tuple = ()
    # how -> count, so a caller can see at a glance whether a profile is
    # being matched on solid ground (condition, line) or on the weak tail
    # (paragraph-wide), which is the difference between targeting a direction
    # and targeting a paragraph and hoping.
    by_method: dict = field(default_factory=dict)
    ambiguous: tuple = ()
    conflicts: tuple = ()

    @property
    def wanted(self) -> set:
        return {m.key for m in self.matches}

    def summary(self) -> dict:
        return {"directions": len(self.wanted),
                "entries_matched": len({m.entry for m in self.matches}),
                "entries_unresolved": len(self.unresolved),
                "by_method": dict(sorted(self.by_method.items())),
                "ambiguous_entries": len(self.ambiguous),
                "ordinal_conflicts": len(self.conflicts)}


def resolve(entries, program, *, trust_ordinals: bool = False) -> Resolution:
    """Turn a harness's work list into decisions this planner can name.

    `trust_ordinals` is the escape hatch for a profile that was produced by
    this tool - `coverage --work-list` writes one - where the ordinals are
    ours and are the most precise identity available. It defaults off because
    a foreign ordinal is not merely useless: it is *plausible*. Specter counts
    per (paragraph, kind) and this tool counts statement position, so their
    third `IF` in a paragraph is our ordinal 3, which usually exists and is
    usually a different decision. Nothing in either program can detect that
    from the number alone.
    """
    from .coverage import branches_of

    by_paragraph: dict = {}
    for branch in branches_of(program):
        by_paragraph.setdefault(branch.paragraph.upper(), []).append(branch)

    matches: list = []
    unresolved: list = []
    ambiguous: list = []
    conflicts: list = []
    by_method: dict = {}

    for index, raw in enumerate(entries or ()):
        if not isinstance(raw, dict):
            unresolved.append({"entry": index, "reason": "not an object"})
            continue
        probe = str(raw.get("probe_id") or raw.get("id") or "")
        paragraph = str(raw.get("paragraph") or "").upper().strip()
        if not paragraph:
            unresolved.append({"entry": index, "probe": probe,
                               "reason": "no paragraph named"})
            continue
        candidates = by_paragraph.get(paragraph)
        if candidates is None:
            unresolved.append({
                "entry": index, "probe": probe, "paragraph": paragraph,
                "reason": "no such paragraph in this program"})
            continue
        if not candidates:
            unresolved.append({
                "entry": index, "probe": probe, "paragraph": paragraph,
                "reason": "paragraph has no decisions"})
            continue

        kind = raw.get("kind")
        pool = candidates
        if kind:
            wanted_kind = normalize_kind(kind)
            narrowed = [b for b in pool if b.kind.upper() == wanted_kind]
            # A kind that matches nothing is more likely a vocabulary gap than
            # a real claim that the paragraph lacks that construct, so it
            # narrows when it can and steps aside when it cannot.
            pool = narrowed or pool

        found, how = _locate(raw, pool, trust_ordinals=trust_ordinals)
        if not found:
            unresolved.append({
                "entry": index, "probe": probe, "paragraph": paragraph,
                "reason": _why_not(raw),
                "decisions_in_paragraph": len(candidates)})
            continue

        if len(found) > 1:
            ambiguous.append({"entry": index, "probe": probe,
                              "paragraph": paragraph, "how": how,
                              "matched": len(found),
                              "ordinals": [b.ordinal for b in found]})

        # An ordinal that disagrees with what the text matched is worth
        # saying out loud: it is the signature of two tools counting
        # differently, and it is silent otherwise.
        stated = _int_or_none(raw.get("ordinal"))
        if (stated is not None and how not in ("ordinal", "paragraph")
                and stated not in [b.ordinal for b in found]):
            conflicts.append({"entry": index, "probe": probe,
                              "paragraph": paragraph, "stated_ordinal": stated,
                              "resolved_ordinals": [b.ordinal for b in found],
                              "matched_by": how})

        for branch in found:
            for direction in normalize_direction(raw.get("direction")):
                matches.append(Match((branch.paragraph.upper(), branch.ordinal,
                                      branch.kind.upper(), bool(direction)),
                                     how, index, probe))
        by_method[how] = by_method.get(how, 0) + 1

    return Resolution(tuple(matches), tuple(unresolved), by_method,
                      tuple(ambiguous), tuple(conflicts))


def _locate(raw: dict, pool: list, *, trust_ordinals: bool) -> tuple:
    """Find the decisions an entry names, best evidence first.

    Order matters and is not arbitrary. Condition and line are read off the
    COBOL, so both tools see the same value; an ordinal is each tool's own
    bookkeeping. Text first, counting last.
    """
    line = _int_or_none(raw.get("line") or raw.get("line_start"))
    ordinal = _int_or_none(raw.get("ordinal"))
    condition = normalize_condition(raw.get("condition")
                                    or raw.get("text") or "")

    if trust_ordinals and ordinal is not None:
        exact = [b for b in pool if b.ordinal == ordinal]
        if exact:
            return exact, "ordinal"

    if condition:
        hits = [b for b in pool if normalize_condition(b.condition) == condition]
        if len(hits) == 1:
            return hits, "condition"
        if len(hits) > 1:
            if line is not None:
                narrowed = [b for b in hits if b.line == line]
                if len(narrowed) == 1:
                    return narrowed, "condition+line"
                if narrowed:
                    return narrowed, "condition+line"
            return hits, "condition-ambiguous"
        # Nothing matched exactly. A harness may quote more of the statement
        # than the parser kept - an EVALUATE arm reported as `SUBJECT = 'Y'`
        # against a stored `'Y'`, for instance - so containment is tried, and
        # is reported under its own name because it is a weaker claim.
        loose = [b for b in pool
                 if _contains(normalize_condition(b.condition), condition)]
        if len(loose) == 1:
            return loose, "condition-approximate"
        if loose and line is not None:
            narrowed = [b for b in loose if b.line == line]
            if narrowed:
                return narrowed, "condition-approximate+line"

    if line is not None:
        hits = [b for b in pool if b.line == line]
        if len(hits) == 1:
            return hits, "line"
        if len(hits) > 1:
            return hits, "line-ambiguous"

    if ordinal is not None and not trust_ordinals:
        # Deliberately *not* used as an identity. Falling back to it here
        # would reintroduce exactly the silent mismatch this module exists to
        # prevent, so an entry carrying only a foreign ordinal is treated as
        # naming its paragraph and nothing finer.
        pass

    if raw.get("paragraph"):
        return list(pool), "paragraph"
    return [], ""


def _contains(stored: str, offered: str) -> bool:
    if not stored or not offered:
        return False
    return stored in offered or offered in stored


def _why_not(raw: dict) -> str:
    if raw.get("condition") or raw.get("text"):
        return "condition did not match any decision in this paragraph"
    if raw.get("line") or raw.get("line_start"):
        return "no decision on that line in this paragraph"
    return "nothing in the entry identifies a decision"


def _int_or_none(value):
    try:
        number = int(value)
    except (TypeError, ValueError):
        return None
    return None if number < 0 else number
