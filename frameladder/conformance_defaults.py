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

The worlds used to speak only about files, which left most of the corpus with
nothing to say: 120 of the 218 external operations on CardDemo are `EXEC`,
and 19 of its 29 programs declare no `SELECT` at all, so `io_defaults`
returned an empty dict and all three worlds were the identical run. The
non-`bare` worlds therefore also answer the EXEC axis, from evidence only - a
variable is offered a status code when `faults.channel_of` finds the *source*
put it in that channel (a `FILE STATUS IS`, a `RESP` operand, `SQLCODE`),
never because of how it is spelled. Measured on CardDemo that is worth +10
verified directions on its own and it is the only part of the mechanism that
can reach a program whose I/O is all SQL or DL/I.
"""

from __future__ import annotations

WORLDS = ("bare", "populated", "empty")

# Per status channel, the code meaning "it worked" and the code meaning "it
# ran and found nothing" - the two outcomes the worlds are named after. Both
# are read out of `faults`, which holds them as fixed platform vocabulary
# rather than as a guess about any one program.
_CHANNEL_OK = {"file": "00", "sql": 0, "cics": 0, "dli": "  "}
_CHANNEL_NIL = {"file": "10", "sql": 100, "cics": 13, "dli": "GB"}


def exec_channels(program) -> dict:
    """``op_key -> {status variable: channel}`` for operations no SELECT
    speaks for.

    Computed once per program and cached on it, the same way `analyse` and
    `external_reach` are: a sweep asks for this once per direction and
    rebuilding the provenance index each time is the difference between a
    seconds-long job and a minutes-long one.
    """
    cached = getattr(program, "_exec_channels", None)
    if cached is not None:
        return cached
    from .faults import channel_of
    from .ladder import analyse

    spoken_for = set(_file_defaults(program, "bare"))
    out: dict = {}
    try:
        _graph, prov = analyse(program)
    except Exception:                                            # noqa: BLE001
        prov = None
    for var, writers in (getattr(prov, "writers", {}) or {}).items():
        for w in writers:
            key = (getattr(w, "op_key", "") or "").upper()
            if getattr(w, "kind", "") != "STUB" or not key:
                continue
            if key in spoken_for:
                continue
            channel = channel_of(var, program.model, key)
            if channel:
                out.setdefault(key, {})[var.upper()] = channel
    try:
        program._exec_channels = out
    except AttributeError:
        pass
    return out


def io_defaults(program, world: str = "bare") -> dict:
    """Per-operation status codes for one of :data:`WORLDS`.

    ``bare``       - the files are not there. An indexed OPEN INPUT gives 35,
                     and the EXEC axis is left alone, because that is what the
                     conformance harnesses compare against.
    ``populated``  - everything opens, every READ delivers a record, and every
                     EXEC reports success.
    ``empty``      - everything opens, every READ is immediately at end, and
                     every EXEC reports that it found nothing.
    """
    out = _file_defaults(program, world)
    if world == "bare":
        return out
    table = _CHANNEL_OK if world == "populated" else _CHANNEL_NIL
    for key, channels in exec_channels(program).items():
        slot = dict(out.get(key, {}))
        for var, channel in channels.items():
            slot[var] = table[channel]
        out[key] = slot
    return out


def _file_defaults(program, world: str) -> dict:
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
