"""What an external operation is allowed to say went wrong.

Outcomes here are chosen by obligation, not by enumeration: the ladder asks
what a guard on the chain requires, walks back to the operation that produces
that variable, and makes it return the required value. That is the right
default, because it only ever generates outcomes the program actually
distinguishes - there is no point returning file status 47 to a program that
never tests it.

It breaks down in one place. When the obligation is a *negation* -
``IF ACCTFILE-STATUS NOT = '00'`` - the program has named the value to avoid
and no value to use instead. With nothing else in evidence the witness picks
an arbitrary string, and an arbitrary string is not a file status: real code
goes on to test it against '10' or '23' and takes neither branch.

So the standard codes belong here. They are not heuristics or guesses about
this program - they are the fixed vocabulary the platform defines, in the same
way that the set of HTTP status codes is fixed. A variable is only offered
them when it is genuinely one of these channels, which is known exactly:
``FILE STATUS IS`` names the file-status field in the SELECT, SQLCODE is
SQLCODE, and a CICS RESP operand names itself.
"""

from __future__ import annotations

# Ordered so that the most useful failure comes first: an operation that
# "worked but found nothing" exercises far more real code than one that
# failed catastrophically, which usually just abends.
FILE_STATUS = ["00", "10", "23", "35", "22", "02", "04", "37", "39",
               "41", "42", "43", "47", "48", "49", "92", "93", "34"]

# DB2. +100 is not-found and is by far the most exercised non-zero value;
# the negatives are the ones real programs have handlers for.
SQLCODE = [0, 100, -911, -803, -805, -811, -904, -180, -305, -501, -104]

# CICS EIBRESP. 0 is NORMAL; the rest are the conditions programs HANDLE.
CICS_RESP = [0, 13, 12, 22, 17, 84, 16, 44, 18, 27, 70, 80]

# DL/I. The DIB status code: two characters, spaces for success. GE is
# segment-not-found, GB end-of-database - the two every retrieval loop
# handles - then the not-open/invalid families programs test explicitly.
# Fixed by IMS the way HTTP status codes are fixed; not a naming guess.
DLI_STATUS = ["  ", "GE", "GB", "II", "AD", "DA", "AM", "GK", "GA"]

_FAMILIES = {"file": FILE_STATUS, "sql": SQLCODE, "cics": CICS_RESP,
             "dli": DLI_STATUS}


def channel_of(var: str, model, op_key: str = "") -> str | None:
    """Which status vocabulary a variable belongs to, if any.

    Deliberately not a naming heuristic: a file-status field is whatever the
    SELECT said it was, and guessing from a name would put codes into fields
    that are not status fields at all.
    """
    upper = (var or "").upper()
    if upper in {s.upper() for s in getattr(model, "file_status", {}).values()}:
        return "file"
    if upper in ("SQLCODE", "SQLSTATE"):
        return "sql"
    if op_key.startswith("EXEC:SQL"):
        return "sql"
    # DIBSTAT is the DL/I interface block's status field, an exact platform
    # name like SQLCODE - every EXEC DLI sets it whether the block names it
    # or not.
    if upper == "DIBSTAT" or op_key.startswith("EXEC:DLI"):
        return "dli"
    # The source names its own response channel in a `RESP(...)` operand.
    # This used to match on a `-RESP` suffix, directly contradicting the
    # docstring above it: a field is a status field because the program put
    # it in that channel, never because of how it is spelled. EIBRESP and
    # EIBRESP2 are exact platform names, which is a different thing from a
    # name-shaped guess - and matched exactly, so `WS-EIBRESP-SAVE` is not
    # swept up with them.
    if upper in getattr(model, "cics_resp", ()) or upper in ("EIBRESP",
                                                             "EIBRESP2"):
        return "cics"
    return None


def codes_for(var: str, model, op_key: str = "") -> list:
    """The vocabulary this variable is drawn from, most useful first."""
    channel = channel_of(var, model, op_key)
    return list(_FAMILIES.get(channel, ()))


def enrich_domain(var: str, model, domain, op_key: str = "") -> list:
    """The candidate values for this variable, best first.

    Order is the whole point and a set destroys it. The program's own
    literals come first, because a value the code actually tests is always
    the better choice; the platform's codes follow in order of how much
    behaviour they unlock, so a negation resolves to "found nothing" or
    "end of file" rather than to "duplicate alternate index".
    """
    ordered = sorted(domain, key=repr)
    for code in codes_for(var, model, op_key):
        if code not in ordered:
            ordered.append(code)
    return ordered
