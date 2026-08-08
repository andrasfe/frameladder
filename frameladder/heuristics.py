"""Values that look like what the field is for.

Two different jobs need two different kinds of value, and conflating them is
why a generator can have perfect constraint solving and still never reach
anything interesting.

*Shape* comes from class conditions. ``IF WS-X IS NUMERIC`` does not compare
anything - it asks whether the bytes are digits - so the obligation is on the
form of the value, and the PIC clause says what form satisfies it.

*Plausibility* comes from the name. Real COBOL guards its deep code with
validation cascades, and much of what they check is not visible in any
condition the ladder can lift: a date is handed to a subprogram, an amount is
run through ``NUMVAL``, an id is looked up. A field called ``ACCT-OPEN-DATE``
holding ``'AAAAAAAA'`` fails at the first edit paragraph and the trace never
gets near the target. Naming conventions are the only signal available about
what a field is for, and in COBOL shops they are unusually reliable.

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


def semantic_value(name: str, pic: str):
    """A plausible value for a field, from its name and its declared shape.

    The shape matters as much as the name: a date in ``X(8)`` is ``20250115``
    and the same date in ``X(10)`` is ``2025-01-15``, and a validator will
    reject the other one.
    """
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
                    negated: bool = False):
    """The value to reach for in a free slot.

    Shape beats plausibility: a realistic date that fails ``IS NUMERIC`` is
    worse than an unrealistic string of digits that passes, because the
    class test is an obligation the program actually stated.
    """
    if klass:
        return conforming_value(pic, klass, negated)
    return semantic_value(name, pic)
