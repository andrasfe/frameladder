"""Fields the platform declares, which application source never does.

A CICS program tests `EIBAID` and `EIBCALEN`; a DB2 program tests `SQLCODE`;
an MQ program tests a completion code. None of them declare those fields,
because they arrive from a copybook that ships with the *product* - the EXEC
Interface Block, the SQLCA, CMQV - and is normally not in an application
repository at all. So the tool sees a name with no PIC: no width, no sign,
no type. `complement_value` has nothing to offer, `solve_variable` has no
shape to fill, and a condition on the most important status field in the
program is decided on an empty default.

Measured across three unrelated codebases (AWS CardDemo, IBM's Global Auto
Mart sample, and a synthetic AML screener), 42% of branch conditions name at
least one undeclared symbol, and the four commonest are EIBAID, SQLCODE,
EIBCALEN and MQCC-OK.

This is the same category as `DFHRESP` and the file-status vocabulary, and
the same rule applies: it is knowledge about the *platform*, fixed by IBM
the way HTTP status codes are fixed, not a guess about how anyone names
anything. The declarations below are therefore facts, but they are still
gated - a program gets the EIB only if it issues `EXEC CICS`, the SQLCA only
if it issues `EXEC SQL`, the MQ constants only if it calls one of the MQ
stubs. A field is offered a type because the source put it in that channel,
never because its name looks like something.

Widths are the standard ones. Where a field is COMP the usage is recorded
too, because that is what decides whether a value serialises as two binary
bytes or four characters - and that is exactly where a migration diverges.
"""

from __future__ import annotations

import re

# --- CICS: the EXEC Interface Block ---------------------------------------
# Only the fields an application actually branches on. The EIB has many more
# and inventing entries nobody reads would just inflate the declared set that
# live-in filtering depends on.
EIB = {
    "EIBAID": ("X(1)", ""),
    "EIBCALEN": ("S9(4)", "COMP"),
    "EIBRESP": ("S9(8)", "COMP"),
    "EIBRESP2": ("S9(8)", "COMP"),
    "EIBFN": ("X(2)", ""),
    "EIBRCODE": ("X(6)", ""),
    "EIBTRNID": ("X(4)", ""),
    "EIBTRMID": ("X(4)", ""),
    "EIBREQID": ("X(8)", ""),
    "EIBDS": ("X(8)", ""),
    "EIBCPOSN": ("S9(4)", "COMP"),
    "EIBDATE": ("S9(7)", "COMP-3"),
    "EIBTIME": ("S9(7)", "COMP-3"),
}

# --- DB2: the SQL communication area --------------------------------------
SQLCA = {
    "SQLCODE": ("S9(9)", "COMP"),
    "SQLSTATE": ("X(5)", ""),
    "SQLERRMC": ("X(70)", ""),
    "SQLERRP": ("X(8)", ""),
    "SQLWARN0": ("X(1)", ""),
    "SQLWARN1": ("X(1)", ""),
    "SQLWARN2": ("X(1)", ""),
}

# --- MQ: completion and the reason codes a program actually tests ---------
# Values rather than widths: CMQV defines these as level-78 constants, so a
# program compares against the *name*, and without the name the comparison is
# against a field nobody sets.
MQ_CONSTANTS = {
    "MQCC-OK": 0, "MQCC-WARNING": 1, "MQCC-FAILED": 2,
    "MQRC-NONE": 0, "MQRC-NO-MSG-AVAILABLE": 2033,
    "MQRC-Q-MGR-NOT-AVAILABLE": 2059, "MQRC-CONNECTION-BROKEN": 2009,
    "MQRC-NOT-AUTHORIZED": 2035, "MQRC-UNKNOWN-OBJECT-NAME": 2085,
    "MQRC-TRUNCATED-MSG-FAILED": 2080, "MQRC-BACKED-OUT": 2003,
}

_USES_CICS = re.compile(r"\bEXEC\s+CICS\b", re.I)
_USES_SQL = re.compile(r"\bEXEC\s+SQL\b", re.I)
_USES_MQ = re.compile(r"\bCALL\s+'MQ[A-Z]+'", re.I)


def declarations_for(source_text: str) -> tuple[dict, dict]:
    """(pic, usage) the platform supplies to a program that uses its API.

    Returns only what the source has earned by issuing the corresponding
    verb, so a pure batch program gets nothing and its declared set stays
    exactly what it wrote.
    """
    pic: dict = {}
    usage: dict = {}
    for used, table in ((_USES_CICS.search(source_text or ""), EIB),
                        (_USES_SQL.search(source_text or ""), SQLCA)):
        if not used:
            continue
        for name, (spec, how) in table.items():
            pic[name] = spec
            if how:
                usage[name] = how
    return pic, usage


def constants_for(source_text: str) -> dict:
    """Named constants the platform defines, for a program that calls it."""
    if not _USES_MQ.search(source_text or ""):
        return {}
    return dict(MQ_CONSTANTS)
