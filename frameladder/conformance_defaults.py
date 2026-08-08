"""I/O outcomes that match an ordinary environment.

Shared by the coverage runner and the conformance harnesses so both model the
same world: a sequential file opens and immediately hits end-of-file, an
indexed file opened for input is not there.
"""

from __future__ import annotations


def io_defaults(program) -> dict:
    out: dict = {}
    for f, status in program.model.file_status.items():
        indexed = program.model.organization.get(f, "").startswith("INDEX")
        missing = "35" if indexed else "00"
        for verb, value in (("OPEN-INPUT", missing), ("OPEN-I-O", missing),
                            ("OPEN-OUTPUT", "00"), ("OPEN-EXTEND", "00"),
                            ("OPEN", missing), ("CLOSE", "00"), ("WRITE", "00"),
                            ("REWRITE", "00"), ("START", "00"),
                            ("READ", missing if indexed else "10")):
            out["%s:%s" % (verb, f)] = {status: value}
    return out
