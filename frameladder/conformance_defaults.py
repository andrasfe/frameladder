"""I/O outcomes that match an ordinary environment.

Shared by the coverage runner and the conformance harnesses so both model the
same world.

There is more than one honest world, though, and the choice decides how much
of a batch program is reachable at all. A file program's first act is to open
its files and abend if that failed, so a world where the files are absent
stops the run at the first paragraph - correct, and useless for coverage. A
world where they open and return records reaches the processing loops but
never their end-of-file exits. Neither is wrong; each is partial.

So the worlds are named and enumerated, and the coverage runner draws from
all of them. `bare` stays the default because the conformance harnesses
compare against GnuCOBOL running with no data files present, and they must
keep modelling exactly that.
"""

from __future__ import annotations

WORLDS = ("bare", "populated", "empty")


def io_defaults(program, world: str = "bare") -> dict:
    """Per-operation status codes for one of :data:`WORLDS`.

    ``bare``       - the files are not there. An indexed OPEN INPUT gives 35.
    ``populated``  - everything opens and every READ delivers a record.
    ``empty``      - everything opens and every READ is immediately at end.
    """
    out: dict = {}
    for f, status in program.model.file_status.items():
        indexed = program.model.organization.get(f, "").startswith("INDEX")
        if world == "bare":
            opened = "35" if indexed else "00"
            read = "35" if indexed else "10"
        else:
            opened = "00"
            read = "00" if world == "populated" else "10"
        for verb, value in (("OPEN-INPUT", opened), ("OPEN-I-O", opened),
                            ("OPEN-OUTPUT", "00"), ("OPEN-EXTEND", "00"),
                            ("OPEN", opened), ("CLOSE", "00"), ("WRITE", "00"),
                            ("REWRITE", "00"), ("START", "00"),
                            ("READ", read)):
            out["%s:%s" % (verb, f)] = {status: value}
    return out
