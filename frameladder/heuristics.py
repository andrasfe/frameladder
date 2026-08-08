"""Values that look like what the field is for.

Two different jobs need two different kinds of value, and conflating them is
why a generator can have perfect constraint solving and still never reach
anything interesting.

*Shape* comes from class conditions. ``IF WS-X IS NUMERIC`` does not compare
anything - it asks whether the bytes are digits - so the obligation is on the
form of the value, and the PIC clause says what form satisfies it.

*Plausibility* is harder, and the order it is sought in matters more than the
sources themselves.

**Evidence from the program comes first.** If a field is compared against
literals anywhere in the source, those literals are what its own logic
distinguishes - and they are facts about this program rather than guesses
about programs in general. This works whatever language the field names are
in.

**Convention is the fallback.** Only when the program says nothing does the
name get consulted: a field called ``ACCT-OPEN-DATE`` holding ``'AAAAAAAA'``
fails at the first edit paragraph and never reaches the target. But a name
table is a *convention pack*, not a law - the built-in one is English and
US-shaped, and an estate whose fields are called ``GEB-DAT`` or ``VERS-NR``
should supply its own rather than be silently served nothing. Hence
:func:`load_pack`.

Both are only ever applied to *free* slots - where a constraint fixed a
relationship and left the value open - so a heuristic can never contradict
something the program actually requires. Where the two compete, shape wins:
a plausible value that fails the class test is worse than a dull one that
passes.
"""

from __future__ import annotations

import re

# Suffixes are matched longest-first so ACCT-EXPIRAION-DATE reads as a date
# rather than as whatever its earlier tokens suggest.
_ROLES = [
    ("date", ("DATE", "DT", "DOB", "BIRTH")),
    ("timestamp", ("TIMESTAMP", "TS", "TIME", "ORIG-TS", "PROC-TS")),
    ("amount", ("AMT", "AMOUNT", "BAL", "BALANCE", "LIMIT", "CREDIT", "DEBIT",
                "TOTAL", "FEE", "INTEREST")),
    ("rate", ("RATE", "PCT", "PERCENT")),
    ("card", ("CARD-NUM", "CARDNUM", "PAN")),
    ("account", ("ACCT-ID", "ACCTID", "ACCOUNT-ID")),
    ("identifier", ("ID", "NUM", "NUMBER", "KEY", "SEQ")),
    ("name", ("NAME", "FNAME", "LNAME", "MIDDLE")),
    ("address", ("ADDR", "ADDRESS", "STREET", "CITY")),
    ("zip", ("ZIP", "POSTAL", "ZIPCODE")),
    ("state", ("STATE", "STATE-CD", "PROVINCE")),
    ("country", ("COUNTRY", "CTRY")),
    ("phone", ("PHONE", "TEL", "MOBILE")),
    ("status", ("STATUS", "RC", "RETURN-CODE", "SQLCODE", "RESP")),
    ("flag", ("FLAG", "FLG", "SW", "SWITCH", "IND", "INDICATOR")),
    ("code", ("CODE", "CD", "TYPE", "CAT", "GROUP")),
]

# The built-in pack is en-US by convention and deliberately quarantined here,
# so that swapping it out is a supported operation rather than a fork.
DEFAULT_PACK_NAME = "en-US"
_SAMPLES = {
    "date": {8: "20250115", 10: "2025-01-15", 6: "250115", 7: "2025015"},
    "timestamp": {26: "2025-01-15-12.30.45.000000", 16: "2025-01-15-12.3",
                  14: "20250115123045", 10: "2025-01-15"},
    "card": {16: "4111111111111111"},
    "zip": {5: "12345", 10: "12345-6789"},
    "state": {2: "NY"},
    "country": {2: "US", 3: "USA"},
    "phone": {10: "2125551234", 15: "(212)555-1234"},
    "name": {},
    "address": {},
}

_WORDS = {"name": "JOHN SMITH", "address": "1 MAIN STREET",
          "status": "00", "flag": "Y", "code": "A"}


def load_pack(path: str) -> dict:
    """Replace the built-in naming conventions with a site's own.

    A JSON document of ``{"roles": {role: [tokens]}, "samples": {role:
    {width: value}}, "words": {role: value}}``. Supplying one is how an
    estate whose field names are not English gets the same benefit as one
    whose names are.
    """
    import json
    with open(path, "r", errors="replace") as fh:
        pack = json.load(fh)
    if pack.get("roles"):
        _ROLES.clear()
        _ROLES.extend((role, tuple(t.upper() for t in tokens))
                      for role, tokens in pack["roles"].items())
    for role, table in (pack.get("samples") or {}).items():
        _SAMPLES[role] = {int(w): v for w, v in table.items()}
    _WORDS.update(pack.get("words") or {})
    return pack


def _fits(value, pic: str) -> bool:
    """Would this value survive being stored in the field?"""
    text, width, _signed, _dec = _pic(pic)
    if not width:
        return True
    if text:
        return isinstance(value, str) and len(value) <= width
    return not isinstance(value, str)


def from_evidence(evidence, pic: str):
    """A value the program itself compares this field against.

    Preferred over any naming convention: these are facts about this source
    rather than assumptions about how fields are usually named, so they carry
    over to an estate written in any language.
    """
    usable = [v for v in evidence or () if _fits(v, pic)]
    if not usable:
        return None
    # Longest first: a value that fills the field exercises more of it than a
    # one-character flag that happens to sort first.
    return sorted(usable, key=lambda v: (-len(str(v)), repr(v)))[0]


def role_of(name: str) -> str | None:
    """What a field is probably for, from its name."""
    upper = (name or "").upper()
    tokens = upper.split("-")
    best, best_len = None, 0
    for role, needles in _ROLES:
        for needle in needles:
            parts = needle.split("-")
            hit = (upper.endswith(needle) or upper.startswith(needle + "-")
                   or all(p in tokens for p in parts))
            if hit and len(needle) > best_len:
                best, best_len = role, len(needle)
    return best


def _pic(spec: str):
    spec = (spec or "").upper()
    text = "X" in spec or "A" in spec
    signed = spec.startswith("S")
    m = re.search(r"[XA9]\((\d+)\)", spec)
    width = int(m.group(1)) if m else len(re.sub(r"[^XA9]", "", spec)) or 0
    dec = 0
    d = re.search(r"V9\((\d+)\)|V9+", spec)
    if d:
        dec = int(d.group(1)) if d.group(1) else len(d.group(0)) - 1
    return text, width, signed, dec


def conforming_value(pic: str, klass: str, negated: bool = False):
    """A value that satisfies - or deliberately fails - a class condition."""
    text, width, _signed, _dec = _pic(pic)
    width = width or 8
    klass = (klass or "").upper()

    if klass == "NUMERIC":
        if negated:
            # Spaces are the classic way a numeric field fails its own class
            # test, and the case real edit paragraphs are written to catch.
            return " " * width if text else "  "
        return "1" * width if text else int("1" * min(width, 15))
    if klass.startswith("ALPHABETIC"):
        return ("1" * width) if negated else ("A" * width)
    if klass == "POSITIVE":
        return -1 if negated else 1
    if klass == "NEGATIVE":
        return 1 if negated else -1
    if klass == "ZERO":
        return 1 if negated else 0
    return None


def semantic_value(name: str, pic: str, evidence=()):
    """A plausible value for a field, from its name and its declared shape.

    The shape matters as much as the name: a date in ``X(8)`` is ``20250115``
    and the same date in ``X(10)`` is ``2025-01-15``, and a validator will
    reject the other one.
    """
    found = from_evidence(evidence, pic)
    if found is not None:
        return found
    role = role_of(name)
    if role is None:
        return None
    text, width, signed, dec = _pic(pic)
    if not width:
        return None

    if not text:
        if role in ("amount", "rate"):
            whole = max(1, width - dec)
            base = int("1" * min(whole, 12))
            return -base if signed and role == "amount" else base
        if role in ("identifier", "account", "card"):
            return int("1" * min(width, 15))
        if role in ("status", "code", "flag"):
            return 0
        if role == "date" and width in (6, 7, 8):
            return int(_SAMPLES["date"].get(width, "20250115"))
        return None

    table = _SAMPLES.get(role)
    if table is not None:
        exact = table.get(width)
        if exact:
            return exact
        if table:
            longest = max(table.values(), key=len)
            return longest[:width].ljust(width) if width < len(longest) else \
                longest.ljust(width)
    word = _WORDS.get(role)
    if word:
        return word[:width] if width < len(word) else word.ljust(width)
    return None


def preferred_value(name: str, pic: str, klass: str | None = None,
                    negated: bool = False, evidence=()):
    """The value to reach for in a free slot.

    Shape beats plausibility: a realistic date that fails ``IS NUMERIC`` is
    worse than an unrealistic string of digits that passes, because the
    class test is an obligation the program actually stated.
    """
    if klass:
        return conforming_value(pic, klass, negated)
    return semantic_value(name, pic, evidence)
