"""Spend the free values on exposing divergence.

When a constraint fixes only a *relationship* - the rendezvous case, and its
relatives for `!=`, `<`, `>` - the value itself is a free variable of the
path condition.  Reachability is invariant under any assignment to it.
Whether a migrated program *differs* from the original is not.

That freedom is currently spent on `'AAAA'`, `'BBBB'` and `4111111111111111`,
which is the one choice guaranteed to reveal nothing.  This module turns each
free slot into a set of candidate values, each chosen because some real
migration gets it wrong, and each still satisfying the constraint that made
the slot free.

The categories come from data the parser already extracts and the planner
currently ignores: PIC clauses give width, sign and scale; level-88s give a
ready-made equivalence partition; harvested comparison literals give the
values the program itself cares about.

Collation deserves its own note, because it is the only category that changes
*control flow* rather than data.  z/OS is EBCDIC and essentially every
migration target is ASCII, and the two disagree on ordering for exactly three
class pairs - digit/upper, digit/lower, upper/lower - as verified against
GnuCOBOL under both collating sequences.  An ordering constraint witnessed by
two values from the same class holds identically on both platforms and proves
nothing; one witnessed across a class boundary holds on one and flips on the
other, so a migration that got collation wrong takes a visibly different path.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from .ir import holds

# Ordering disagrees between EBCDIC and ASCII for these class pairs, and only
# these. Verified empirically, not assumed: see conformance/ for the harness.
#   ASCII : space < digit < upper < lower
#   EBCDIC: space < lower < upper < digit
UNSTABLE_CLASS_PAIRS = {("digit", "upper"), ("digit", "lower"),
                        ("upper", "lower")}
CLASS_SAMPLE = {"digit": "5", "upper": "M", "lower": "m", "space": " "}


@dataclass(frozen=True)
class Candidate:
    value: object
    category: str
    why: str


def _pic_parts(spec: str):
    """(is_text, width, signed, decimals) from a PIC clause."""
    spec = (spec or "").upper()
    if not spec:
        return True, 8, False, 0
    text = "X" in spec or "A" in spec
    signed = spec.startswith("S")
    m = re.search(r"[XA9]\((\d+)\)", spec)
    if m:
        width = int(m.group(1))
    else:
        width = len(re.sub(r"[^XA9]", "", spec)) or 8
    dec = 0
    d = re.search(r"V9+|V9\((\d+)\)", spec)
    if d:
        dec = int(d.group(1)) if d.group(1) else len(d.group(0)) - 1
    return text, max(1, width), signed, dec


def boundary_candidates(pic: str) -> list:
    """Values that sit on a representation boundary.

    These are the points where COBOL and a port most often part company:
    storing into a narrower field truncates high-order digits silently,
    a field one byte too long loses its tail, and the figurative constants
    are three distinct states that a port usually collapses into one.
    """
    text, width, signed, dec = _pic_parts(pic)
    out: list = []
    if text:
        out += [
            Candidate(" " * width, "spaces", "all spaces"),
            Candidate("\x00" * width, "low-values",
                      "LOW-VALUES; ports often collapse this into empty/null"),
            Candidate("\xff" * width, "high-values", "HIGH-VALUES"),
            Candidate("A" * width, "width-exact", "fills the field exactly"),
            Candidate("A" * (width - 1) + " ", "trailing-space",
                      "value then padding; COBOL pads, String.equals does not"),
            Candidate("A" * (width + 1), "over-width",
                      "one byte too long; COBOL truncates the tail silently"),
        ]
    else:
        digits = width - dec
        top = 10 ** max(1, digits) - 1
        out += [
            Candidate(0, "zero", "zero"),
            Candidate(top, "all-nines", "largest value the field holds"),
            Candidate(top + 1, "overflow",
                      "one past the field; COBOL drops the high-order digit"),
        ]
        if signed:
            out += [
                Candidate(-top, "negative-max", "largest negative"),
                Candidate(-0, "negative-zero",
                          "minus zero; equal arithmetically, different bytes"),
            ]
        if dec:
            out.append(Candidate(
                float("0." + "0" * dec + "5"), "sub-scale",
                "one digit finer than the field; truncate vs round differ"))
    return out


def char_class(value) -> str | None:
    if not isinstance(value, str) or not value:
        return None
    ch = value[0]
    if ch.isdigit():
        return "digit"
    if ch.isupper():
        return "upper"
    if ch.islower():
        return "lower"
    if ch == " ":
        return "space"
    return None


def collation_pairs(width: int) -> list:
    """Ordered pairs whose ordering differs between EBCDIC and ASCII.

    Returned largest-first so the caller can use them for either direction:
    each pair satisfies `a > b` on one platform and `a < b` on the other.
    """
    out = []
    for left, right in UNSTABLE_CLASS_PAIRS:
        a = CLASS_SAMPLE[left] * width
        b = CLASS_SAMPLE[right] * width
        out.append((Candidate(b, "collation-crossover",
                              "%s vs %s: ordering flips between EBCDIC and ASCII"
                              % (right, left)),
                    Candidate(a, "collation-crossover",
                              "%s vs %s: ordering flips between EBCDIC and ASCII"
                              % (left, right))))
    return out


def candidates_for(var: str, op: str, other, model, literals: set,
                   condition_names: dict) -> list:
    """Every value worth trying in a free slot, still satisfying its constraint.

    A candidate that breaks the constraint would change which path runs, so
    the plan would no longer reach its target - the whole point is to vary
    what cannot affect reachability.
    """
    pic = model.pic.get(var, "")
    text, width, _signed, _dec = _pic_parts(pic)
    out: list = list(boundary_candidates(pic))

    # Values the program itself compares this variable against are, by
    # construction, the ones its logic distinguishes.
    for lit in sorted(literals or (), key=repr):
        out.append(Candidate(lit, "program-literal",
                             "a literal this variable is compared against"))

    # A level-88 group is an equivalence partition the programmer wrote down.
    for name, (parent, values) in (condition_names or {}).items():
        if parent.upper() != var.upper():
            continue
        for raw in values:
            from .ir import parse_term
            term = parse_term(raw)
            if term.kind == "const":
                out.append(Candidate(term.value, "88-value",
                                     "value of condition-name %s" % name))

    if text and op in (">", "<", ">=", "<="):
        for low, high in collation_pairs(width):
            out.extend([low, high])

    seen, kept = set(), []
    for cand in out:
        key = repr(cand.value)
        if key in seen:
            continue
        seen.add(key)
        if other is not None and not holds(cand.value, op, other):
            continue
        kept.append(cand)
    return kept


def family(free_slots: list, limit: int = 12) -> list:
    """One-factor-at-a-time variants over the free slots.

    Varying a single slot per member keeps every member's failure
    attributable to one value, which is what makes a divergence report
    actionable. It is also linear rather than exponential in the number of
    slots, which matters when a plan has thirteen of them.
    """
    out = []
    for slot, cands in free_slots:
        for cand in cands:
            out.append((slot, cand))
            if len(out) >= limit:
                return out
    return out
