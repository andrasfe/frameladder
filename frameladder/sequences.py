"""What an operation returns is a *sequence*, and nothing was deriving one.

`ir.Plan` has carried ordered outcomes and a terminal since the beginning:
`stub_plan()` hands the interpreter a list per operation and `terminals` says
what happens once they run out, and `interpreter._external` delivers them in
order.  The data structure was there; the derivation was not.  Every world the
tool could actually describe fixed one outcome and repeated it for ever -
`conformance_defaults.io_defaults` gives a file's READ a single status, so
`populated` means "records without end" and `empty` means "no records at all".

Neither is what a batch program is written against, and the gap is not the
length of the loop.  The interpreter caps a loop at `MAX_LOOP` iterations, so
"records without end" already falls out of the loop and runs the code after
it; measured across both corpora, exactly one program in forty-six reaches a
runaway in any world.  The gap is that **every one of those iterations processes the
same record**, because a READ writes nothing into the record area at all and
the area therefore keeps its entry value from the first iteration to the last.

That is what makes a whole class of guard unreachable rather than merely
unlucky:

* a control break - `IF THIS-KEY NOT = PREVIOUS-KEY` - has one reachable
  direction when every record is identical, and it is the direction that says
  "no break", so the break-handling half of a report program is dark;
* a validation that fails on some records and not others is evaluated once
  per record against one record;
* anything counting distinct values gets one.

So a sequence is derived here as an ordered list of payloads, one per call,
ending in end-of-file.  Three decisions, all bounded and all evidence-based:

**How many.** Two records already separate "first" from "not first", which is
what a control break turns on; three separate "first", "middle" and "last".
Past that the extra records are the same shape as the ones before them and
buy nothing, so the default stops at three and the length is a flag rather
than a constant.

**Which payload on which call.** The values are the literals the program
itself compares those record fields against - the same evidence
`coverage --sample` draws on - plus the complement of that set, so a field the
program only ever tests for one value still has a second reachable state.
Consecutive calls rotate through them independently per field, so record *i*
differs from record *i-1* in every field that has more than one candidate.
That is the cheapest arrangement that makes "the third record is the bad one"
expressible, and it needs no guess about which field means what.

**Which operations.** Only those the source has put in a status channel: a
file with `FILE STATUS IS`, whose READ the standard says returns '00' and then
'10'. That is platform vocabulary, not a naming heuristic. CICS browse
sequences (READNEXT to ENDFILE) are the same shape through RESP and are not
built here, because none of the programs measured against issue one.

The result composes with `lift`: a sequence fixes the outside world and the
frontier search then solves the guards *inside* it, from a state that only a
finished read loop can produce.  Nothing here is sampled - the payload
rotation is positional and the literals are sorted - so the same program gives
the same sequences on every run.
"""

from __future__ import annotations

from .heuristics import complement_value

# Enough to tell first from last with a middle in between. Measured rather
# than assumed: see the README table for what the fourth record buys.
DEFAULT_LENGTHS = (1, 2, 3)

# A record can have hundreds of fields and setting all of them costs a dict
# entry per call. Only those the program compares against something can move a
# decision, so the rest are left holding whatever the entry state gave them.
MAX_FIELDS = 12

# The status a sequential READ returns for a record and for end-of-file. Fixed
# by the standard the way an HTTP status code is fixed.
RECORD = "00"
END_OF_FILE = "10"


def record_fields(program, file_name: str) -> list:
    """The elementary fields a READ on this file fills.

    A file with no `FD`/`01` association contributes nothing rather than
    guessing at a record area: writing to the wrong group would overwrite
    fields the program set itself.
    """
    out: list = []
    model = program.model
    for record in model.fd_records.get(file_name, []):
        children = [c for c in model.descendants(record) if model.pic_of(c)]
        out.extend(children or ([record] if model.pic_of(record) else []))
    return list(dict.fromkeys(out))


def read_targets(program, file_name: str) -> list:
    """The record areas a READ on this file writes, from the source.

    ``READ f INTO ws-record`` names the area in the statement; the operand is
    read the same way `provenance.stub_outputs` reads it, so the two agree
    about what the operation writes.
    """
    from .ir import norm
    from .provenance import op_key, stub_outputs
    key = read_key(file_name)
    out: list = []

    def visit(stmt):
        if stmt.get("type") == "READ":
            text = norm(stmt.get("text", ""))
            if op_key(text) == key:
                out.extend(name.upper() for name in stub_outputs(text)
                           if name.upper() != file_name.upper())
        for child in stmt.get("children") or []:
            visit(child)

    for para in program.paragraphs:
        for stmt in para.get("statements", []):
            visit(stmt)
    return list(dict.fromkeys(out))


def fill_layouts(program, prov, file_name: str) -> list:
    """``[(record area a READ fills, group whose layout describes it)]``.

    Batch COBOL almost never declares the record's fields under the `FD`.
    The area there is one long alphanumeric item, and the layout the program
    compares against is somewhere else - reached either by `READ ... INTO
    ws-record`, which names it in the statement, or by `MOVE FD-AREA TO
    ws-record` immediately afterwards, which `provenance.stub_fills` already
    records.

    Both idioms have to be followed, because a payload written into the two
    fields under the FD lands in a group the program never compares anything
    against, and none of it reaches a decision. That is not a small
    difference: on the batch programs measured here *every* file takes one of
    these two routes and none declares its fields under the FD.
    """
    out: list = []
    for area in read_targets(program, file_name):
        out.append((area, area))
    fills = getattr(prov, "stub_fills", {}) or {}
    for record in program.model.fd_records.get(file_name, []):
        moved = sorted(base for base, writer in fills.items()
                       if (getattr(writer, "source", "") or "").upper()
                       == record.upper())
        out.append((record, moved[0] if moved else record))
    seen, unique = set(), []
    for area, root in out:
        if area in seen:
            continue
        seen.add(area)
        unique.append((area, root))
    return unique


def render_record(model, root: str, values: dict) -> str:
    """The bytes of one record: the given fields placed, the rest at their
    category's zero.

    `layout.render` blanks everything it was not given, which turns every
    numeric field in the record into spaces - a record no file can contain
    and one whose every numeric comparison then goes the same way. Zero-fill
    is what an unset numeric field holds.
    """
    from .layout import record_layout
    try:
        laid = record_layout(model, root)
    except Exception:                                        # noqa: BLE001
        return ""
    fields = [f for f in laid[1:]
              if f.length and not model.descendants(f.name)]
    size = max((f.offset + f.length for f in fields), default=0)
    if not size:
        return ""
    buffer = [" "] * size
    for f in fields:
        if (f.usage or "DISPLAY").upper() not in ("DISPLAY", ""):
            # Packed and binary need real encoding rather than text, and a
            # plausible-looking wrong byte pattern is worse than none.
            continue
        spec = (f.pic or "").upper()
        numeric = "9" in spec and "X" not in spec and "A" not in spec
        raw = values.get(f.name)
        if raw is None:
            text = ("0" if numeric else " ") * f.length
        elif numeric:
            digits = str(raw).strip().lstrip("+-").split(".")[0]
            text = (digits or "0").rjust(f.length, "0")[-f.length:]
        else:
            text = str(raw).ljust(f.length)[:f.length]
        buffer[f.offset:f.offset + f.length] = list(text)
    return "".join(buffer)


def field_values(program, literals: dict, name: str) -> list:
    """The values this field is known to be able to hold, in a fixed order."""
    values = sorted(literals.get(name) or [], key=repr)
    if not values:
        return []
    other = complement_value(name, program.model.pic_of(name), values)
    if other is not None and other not in values:
        values = values + [other]
    return values


def distinct_values(model, name: str, count: int) -> list:
    """``count`` values of the field's own shape that differ from each other.

    Measured before it was written, because it is the part of this that is not
    evidence: across both corpora only 0-2 fields *per program* under a record
    area are ever compared against a literal, so a payload built from literals
    alone is empty and the sequence delivers the same record every time. What
    the programs do compare a record field against is another field - the
    previous record's key, the matching record from another file - and those
    guards do not turn on which value it is, only on whether it changed.

    So this supplies difference rather than meaning: successive values of the
    field's own category, which is a fact about files (records differ) and not
    a guess about what the field is for. Where the program *has* named values,
    `field_values` is used instead and this is not consulted.
    """
    from .layout import byte_length
    pic = (model.pic_of(name) or "").upper()
    if not pic:
        return []
    if "9" in pic and "X" not in pic and "A" not in pic:
        # Ascending, which is the order a sorted input file arrives in and the
        # order a sequence check is written against.
        return list(range(1, count + 1))
    try:
        width = byte_length(pic, model.usage_of(name),
                            model.look(model.sign, name, "") or "")
    except Exception:                                        # noqa: BLE001
        width = 0
    width = min(max(width, 1), 8)
    return [chr(ord("A") + index) * width for index in range(count)]


def record_plan(program, literals: dict, root: str, count: int,
                max_fields: int = MAX_FIELDS) -> list:
    """``[(field, [values])]`` for every elementary field of a record area.

    A field the program names values for takes those values, ranked so the
    most-distinguished fields come first; every other field takes distinct
    values of its own shape, so the records differ. The cap applies only to
    the evidence-derived fields, because those are the ones whose value
    choice is a claim about the program.
    """
    model = program.model
    named, plain = [], []
    for name in model.descendants(root):
        if not model.pic_of(name) or model.descendants(name):
            continue
        values = field_values(program, literals, name)
        if len(values) > 1:
            named.append((name, values))
        else:
            generic = distinct_values(model, name, count)
            if generic:
                plain.append((name, values + generic if values else generic))
    named.sort(key=lambda kv: (-len(kv[1]), kv[0]))
    return named[:max_fields] + plain


def payloads(program, prov, literals: dict, file_name: str, length: int,
             max_fields: int = MAX_FIELDS) -> list:
    """One ``{record area: bytes}`` map per call, consecutive calls differing.

    The rotation is per field and positional: field *f* takes its *i*-th
    candidate on the *i*-th record, so two consecutive records differ in every
    field that has more than one candidate. That is what a control break needs
    - the guard `IF THIS-KEY NOT = PREVIOUS-KEY` has no reachable true
    direction when every record is the same - and it needs no guess about
    which field is a key.
    """
    model = program.model
    plans = []
    for area, root in fill_layouts(program, prov, file_name):
        fields = record_plan(program, literals, root, length, max_fields)
        if fields:
            plans.append((area, root, fields))
    out = []
    for index in range(length):
        record: dict = {}
        for area, root, fields in plans:
            values = {name: choices[index % len(choices)]
                      for name, choices in fields}
            image = render_record(model, root, values)
            if image:
                record[area] = image
        out.append(record)
    return out


def read_key(file_name: str) -> str:
    return "READ:%s" % file_name.upper()


def file_operations(program) -> dict:
    """``file -> [op key]`` for every operation the source issues on it.

    Taken from the statements rather than from a list of verbs the file
    *could* take: an operation nobody issues cannot fail, and a world that
    makes it fail is a run spent proving that.
    """
    from .ir import norm
    from .provenance import STUB_KINDS, op_key
    # `WRITE FD-ACCTFILE-REC` names the *record*, not the file - the standard
    # requires it - so the operation's key is `WRITE:FD-ACCTFILE-REC` while
    # the status field belongs to `ACCTFILE-FILE`. Without this the two never
    # meet, and no world can make a WRITE fail: `conformance_defaults` builds
    # `WRITE:<file>` keys that match nothing the program ever issues.
    belongs = {}
    for name, records in (program.model.fd_records or {}).items():
        for record in records:
            belongs[record.upper()] = name.upper()
    out: dict = {}

    def visit(stmt):
        if stmt.get("type") in STUB_KINDS:
            key = op_key(norm(stmt.get("text", "")))
            if ":" in key:
                operand = key.rsplit(":", 1)[-1]
                out.setdefault(belongs.get(operand, operand), []).append(key)
        for child in stmt.get("children") or []:
            visit(child)

    for para in program.paragraphs:
        for stmt in para.get("statements", []):
            visit(stmt)
    return {name: sorted(dict.fromkeys(keys)) for name, keys in out.items()}


def fault_codes(program, literals: dict, status: str, op: str,
                count: int) -> list:
    """The non-success outcomes worth giving this operation, best first.

    `faults.enrich_domain` already orders them the right way: values the
    program itself compares the status against come first, because a code the
    code tests is always the better choice, and the platform's own vocabulary
    follows. Nothing here is inferred from a name - the field is a file status
    because the SELECT said `FILE STATUS IS`.
    """
    from .faults import enrich_domain
    ordered = enrich_domain(status, program.model,
                            literals.get(status.upper()) or set(), op)
    out = [code for code in ordered if str(code).strip() not in ("00", "0", "")]
    return out[:max(0, count)]


def sequence_worlds(program, prov, literals: dict, lengths=DEFAULT_LENGTHS,
                    max_fields: int = MAX_FIELDS) -> list:
    """One outside world per sequence length, for every file at once.

    Every file gets the same number of records, which is the arrangement a
    matched read of a master and a transaction file is written against. Giving
    the files different lengths would be a larger space and a different
    hypothesis; this one is the cheap half and it is the half that terminates.
    """
    files = sorted(program.model.file_status)
    if not files:
        return []
    out: list = []
    for length in lengths:
        stubs: dict = {}
        terminals: dict = {}
        for name in files:
            status = program.model.file_status[name]
            if not status:
                continue
            records = payloads(program, prov, literals, name, length,
                               max_fields)
            entries = []
            for index in range(length):
                fields = {status: RECORD}
                fields.update(records[index] if index < len(records) else {})
                entries.append({"when": {}, "set": fields, "seq": index,
                                "inferred": False})
            stubs[read_key(name)] = entries
            # The terminal is what makes the loop end. Without it the planned
            # outcomes run out and the operation falls back to whatever the
            # world's default says, which for a populated world is another
            # record - so the sequence would have no end and the code after
            # the loop would be reached only by the interpreter giving up.
            terminals[read_key(name)] = {status: END_OF_FILE}
        if stubs:
            out.append({"name": "records:%d" % length, "world": "populated",
                        "stubs": stubs, "terminals": terminals})
    return out


# Two positions are enough to separate "it failed straight away" from "it
# failed once the program was underway", and the second is the one a plan
# placed at entry cannot express at all. A third adds a longer prologue to
# the same finding.
FAULT_POSITIONS = (1, 2)
DEFAULT_FAULT_CODES = 3
# Every file times every code times every position is a product, and a
# program with six files and four operations each reaches three figures. The
# cap is a budget, not a claim that the rest are uninteresting.
MAX_FAULT_WORLDS = 60


def fault_worlds(program, prov, literals: dict, length: int = 3,
                 codes: int = DEFAULT_FAULT_CODES,
                 positions=FAULT_POSITIONS,
                 max_worlds: int = MAX_FAULT_WORLDS,
                 max_fields: int = MAX_FIELDS) -> list:
    """Worlds where one operation fails at one point in its sequence.

    This is the same object as a record sequence and the reason to build the
    sequence machinery at all: "the third record is the one that fails" is an
    outcome list, and there was no other way to say it. A world could name one
    status for an operation and repeat it for ever, so a program's reject path
    was reachable only by making the lookup fail on *every* record - which
    takes a different route through the program, or none, because the record
    that would have been rejected was never read successfully in the first
    place.

    The fault is transient: the operation succeeds again afterwards. A
    permanent failure usually ends the run at the handler, so everything the
    program does with the records after it stays dark, and the two are
    different tests rather than one being weaker.
    """
    base = sequence_worlds(program, prov, literals, lengths=(length,),
                           max_fields=max_fields)
    if not base:
        return []
    template = base[0]
    operations = file_operations(program)
    out: list = []
    for name in sorted(program.model.file_status):
        status = program.model.file_status[name]
        if not status:
            continue
        for op in operations.get(name.upper(), []):
            for rank, code in enumerate(
                    fault_codes(program, literals, status, op, codes)):
                # Only a repeated operation has a position; a CLOSE happens
                # once and "fails on the second CLOSE" is not a world.
                spots = positions if op.startswith("READ") else (1,)
                for spot in spots:
                    world = _with_fault(template, op, status, code, spot)
                    if world is not None:
                        out.append(((rank, spot, name, op), world))
    # The cap has to fall evenly. Ordered file by file it would spend the
    # whole budget on the first two, and a program's last file is as likely to
    # be the one guarding the dark half as its first; ordered by rank it takes
    # every operation's most-likely status before any operation's second.
    out.sort(key=lambda pair: pair[0])
    return [world for _rank, world in out[:max_worlds]]


def _with_fault(template: dict, op: str, status: str, code, spot: int):
    """A copy of the base sequence in which ``op`` returns ``code`` on its
    ``spot``-th call and succeeds on the others."""
    import copy
    stubs = copy.deepcopy(template["stubs"])
    terminals = dict(template["terminals"])
    entries = stubs.get(op)
    if entries is None:
        # An operation with no sequence of its own - an OPEN, a CLOSE - gets
        # one, so the fault has somewhere to sit. Its terminal is success, so
        # a program that issues it more often than planned carries on.
        entries = [{"when": {}, "set": {status: RECORD}, "seq": index,
                    "inferred": False} for index in range(max(spot, 1))]
        stubs[op] = entries
        terminals[op] = {status: RECORD}
    while len(entries) < spot:
        entries.append({"when": {}, "set": {status: RECORD},
                        "seq": len(entries), "inferred": False})
    entries[spot - 1] = dict(entries[spot - 1])
    fields = dict(entries[spot - 1].get("set") or {})
    fields[status] = code
    entries[spot - 1]["set"] = fields
    return {"name": "%s=%s@%d" % (op, code, spot), "world": "populated",
            "stubs": stubs, "terminals": terminals}
