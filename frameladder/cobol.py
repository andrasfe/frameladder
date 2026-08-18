"""Read COBOL source into the intermediate form the ladder works on.

The repository is meant to run on code handed to it directly, so the
parser lives here rather than being a dependency.  It covers the subset
the ladder actually reasons about - control flow, data movement, calls
and the data division's record layout - and deliberately does not try to
be a compiler.  Anything it cannot classify becomes an opaque statement,
which the ladder already knows how to treat as an unknown.

A pre-parsed AST (the ``cobalt`` JSON that Specter consumes) can be
loaded instead; :func:`load_program` accepts either and normalises both
to the same shape.
"""

from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass, field
from typing import Any, Iterable

from .ir import _QUOTED_RUN

# --------------------------------------------------------------------------
# Source reading
# --------------------------------------------------------------------------

_COMMENT = ("*", "/")


@dataclass
class Line:
    number: int
    text: str


def read_lines(path: str) -> list[Line]:
    """Strip sequence numbers, indicator column and identification area.

    Free-format source has none of those, so a line that is not long
    enough to have a column 7 is taken as-is.
    """
    out: list[Line] = []
    with open(path, "r", errors="replace") as fh:
        for n, raw in enumerate(fh.read().splitlines(), 1):
            stripped = raw.rstrip()
            if not stripped:
                continue
            if len(stripped) > 6 and stripped[6] in _COMMENT:
                continue
            if stripped.lstrip().startswith("*"):
                continue
            body = stripped[6:72] if len(stripped) > 6 else stripped
            if body.strip():
                out.append(Line(n, body))
    return out


# --------------------------------------------------------------------------
# Data division
# --------------------------------------------------------------------------

_DECL = re.compile(r"^\s*(\d\d)\s+([A-Z0-9][A-Z0-9-]*)\b(.*)$", re.I)
_PIC_IN = re.compile(r"\bPIC(?:TURE)?\s+(?:IS\s+)?(\S+)", re.I)
# `VALUE ALL '-'` fills the field with that character, however wide it is.
# Matched as a bare word the initial value becomes the three letters "ALL",
# so a field the program compares against a row of dashes never holds one.
_VALUE_IN = re.compile(
    r"\bVALUE\s+(?:IS\s+)?(ALL\s+'[^']*'|ALL\s+\"[^\"]*\"|'[^']*'|\"[^\"]*\"|"
    r"[A-Z0-9+-]+)", re.I)
_VALUE_ALL = re.compile(r"^ALL\s+(.*)$", re.I)
# JUSTIFIED aligns a move on the right of the receiver, so the padding lands
# in front of the data and a long sending item loses its *left* end. Ignored,
# both go the other way and a right-aligned field never matches. A hyphen is
# a word character in a COBOL name, so `\b` would find JUST inside
# `WS-JUST-PAID`; the clause is only the bare word.
_JUSTIFIED = re.compile(r"(?<![A-Z0-9-])(?:JUSTIFIED|JUST)(?![A-Z0-9-])", re.I)
# `OCCURS 1 TO 50 TIMES DEPENDING ON N` reserves fifty entries; the counter
# decides how many are *current*, not how many exist. Reading the first
# number gives the table one element, so every reference past the first is
# out of range and every offset after the table is wrong by the difference.
_OCCURS = re.compile(r"\bOCCURS\s+(\d+)(?:\s+TO\s+(\d+))?", re.I)
# A table's KEY clause is what makes `SEARCH ALL` a binary search rather than
# a scan: it names the fields the occurrences are ordered on and which way.
# Without it the verb has nothing to bisect on, so every SEARCH ALL either
# falls out at AT END or matches by accident, and both are wrong in a way that
# looks like a coverage result rather than like a missing feature.
_KEY_CLAUSE = re.compile(r"\b(ASCENDING|DESCENDING)(?:\s+KEY)?(?:\s+IS)?\s+", re.I)
_INDEXED_BY = re.compile(r"\bINDEXED\s+BY\s+", re.I)
_NAME_RUN = re.compile(r"[A-Z0-9][A-Z0-9-]*", re.I)
# Words that end a run of names inside an OCCURS clause.
_OCCURS_STOP = {"ASCENDING", "DESCENDING", "INDEXED", "KEY", "IS", "BY",
                "OCCURS", "TIMES", "DEPENDING", "ON", "PIC", "PICTURE",
                "VALUE", "USAGE", "REDEFINES", "SIGN", "COMP", "COMP-3",
                "DISPLAY", "BINARY", "PACKED-DECIMAL", "SYNCHRONIZED",
                "SYNC", "JUSTIFIED", "JUST", "BLANK", "WHEN", "ZERO"}

# USAGE decides the *representation*, which PIC does not. S9(4) COMP is two
# binary bytes truncated to four decimal digits; S9(4) COMP-3 is three packed
# bytes with a sign nibble; S9(4) DISPLAY is four characters with an
# overpunched sign. They compare equal and serialise completely differently,
# which is exactly where a migration diverges.
_USAGE = re.compile(r"\b(?:USAGE\s+(?:IS\s+)?)?(COMP-[1-5]|COMPUTATIONAL-[1-5]|"
                    r"COMP|COMPUTATIONAL|BINARY|PACKED-DECIMAL|DISPLAY|"
                    r"INDEX|POINTER)\b", re.I)
_REDEFINES = re.compile(r"\bREDEFINES\s+([A-Z0-9][A-Z0-9-]*)", re.I)
_SIGN = re.compile(r"\bSIGN\s+(?:IS\s+)?(LEADING|TRAILING)"
                   r"(\s+SEPARATE)?", re.I)

_USAGE_CANON = {"COMPUTATIONAL": "COMP", "COMPUTATIONAL-1": "COMP-1",
                "COMPUTATIONAL-2": "COMP-2", "COMPUTATIONAL-3": "COMP-3",
                "COMPUTATIONAL-4": "COMP-4", "COMPUTATIONAL-5": "COMP-5",
                "PACKED-DECIMAL": "COMP-3"}
_LEVEL88 = re.compile(r"^\s*88\s+([A-Z0-9][A-Z0-9-]*)\s+VALUES?\s+(?:ARE\s+|IS\s+)?(.*)$", re.I)
_88_VALUE = re.compile(r"'[^']*'|\"[^\"]*\"|[^\s,]+")


def _names_after(rest: str, start: int) -> list:
    """Identifiers following an OCCURS sub-clause, up to the next keyword."""
    out = []
    for m in _NAME_RUN.finditer(rest, start):
        word = m.group(0).upper()
        if word in _OCCURS_STOP:
            break
        out.append(word)
    return out


def occurs_keys(rest: str) -> list:
    """``[(ASCENDING|DESCENDING, field), ...]`` in the order written.

    Order is meaning here: a compound key is compared most-significant first,
    so a set would silently re-sort it and the bisection would step the wrong
    way on every table with more than one key.
    """
    out = []
    for m in _KEY_CLAUSE.finditer(rest):
        for name in _names_after(rest, m.end()):
            out.append((m.group(1).upper(), name))
    return out


def indexed_by(rest: str) -> list:
    m = _INDEXED_BY.search(rest)
    return _names_after(rest, m.end()) if m else []


def _split_sentences(text: str) -> list:
    """Split a data-division buffer on periods that are not inside a literal.

    `01 WS-EDIT-MASK PIC X(8) VALUE '........'.` is one declaration whose
    VALUE happens to be eight periods. Splitting on every period cuts it into
    nine fragments, none of which parses, so the field silently loses its
    VALUE - it keeps its PIC, which is what makes the loss hard to notice.
    A filler or mask made of dots is ordinary in report and edit layouts.
    """
    out, buf, quote = [], [], ""
    for ch in text:
        if quote:
            buf.append(ch)
            if ch == quote:
                quote = ""
            continue
        if ch in "'\"":
            quote = ch
            buf.append(ch)
            continue
        if ch == ".":
            out.append("".join(buf))
            buf = []
            continue
        buf.append(ch)
    out.append("".join(buf))
    return out


def _split_88_values(text: str) -> list:
    """The values of a condition-name, without breaking quoted literals.

    ``88 FLG-BLANK VALUE ' '`` is one value - a space - and splitting on
    whitespace turns it into two lone quotes, which then resolve to nothing.
    Since a level-88 is how COBOL names most of its states, that quietly
    disables a large share of them.
    """
    out: list = []
    pending_range = False
    for m in _88_VALUE.finditer(text or ""):
        token = m.group(0).strip()
        if not token:
            continue
        if token.upper() in ("THRU", "THROUGH"):
            pending_range = True
            continue
        token = token.rstrip(".")
        if pending_range and out:
            # `VALUES 1 THRU 12` names twelve states, not two. Keeping only
            # the endpoints makes the condition-name false for every value in
            # between - which is most of them - and setting it picks an
            # endpoint that the program may never otherwise produce.
            out.extend(_expand_range(out[-1], token))
            pending_range = False
            continue
        out.append(token)
    return out


# A range is enumerated so that everything downstream - the interpreter, SET,
# and the ladder's choice of a value - keeps working on a plain list. Wide
# ranges are left as their endpoints rather than blowing up the table.
_RANGE_LIMIT = 1024


def _expand_range(low: str, high: str) -> list:
    def number(token):
        try:
            return int(token.strip("'\""))
        except (TypeError, ValueError):
            return None
    a, b = number(low), number(high)
    if a is None or b is None or not 0 <= b - a < _RANGE_LIMIT:
        return [high]
    return [str(v) for v in range(a + 1, b + 1)]


_SELECT = re.compile(r"\bSELECT\s+(?:OPTIONAL\s+)?([A-Z0-9][A-Z0-9-]*)", re.I)
_FILE_STATUS = re.compile(r"\bFILE\s+STATUS\s+(?:IS\s+)?([A-Z0-9][A-Z0-9-]*)", re.I)
_ORGANIZATION = re.compile(r"\bORGANIZATION\s+(?:IS\s+)?([A-Z-]+)", re.I)


_FD = re.compile(r"^\s*FD\s+([A-Z0-9][A-Z0-9-]*)", re.I)
_O1 = re.compile(r"^\s*01\s+([A-Z0-9][A-Z0-9-]*)", re.I)


def parse_fd_records(path: str) -> dict:
    """Map each file to the record areas an I/O statement fills.

    ``FD EXPORT-INPUT`` followed by ``01 EXPORT-INPUT-RECORD`` means a READ
    on that file writes that record.  Without it the record's fields look
    like program inputs, and a field holding one value for this record and
    a different one for the next reads as a contradiction rather than as
    two reads.
    """
    out: dict = {}
    current = None
    for line in read_lines(path):
        if re.search(r"\bPROCEDURE\s+DIVISION\b", line.text, re.I):
            break
        fd = _FD.match(line.text)
        if fd:
            current = fd.group(1).upper()
            out.setdefault(current, [])
            continue
        if current:
            rec = _O1.match(line.text)
            if rec:
                out[current].append(rec.group(1).upper())
            elif re.match(r"^\s*(FD|SD|WORKING-STORAGE|LOCAL-STORAGE|LINKAGE)\b",
                          line.text, re.I):
                current = None
    return out


def parse_file_control(path: str) -> dict:
    """Map each file to the variable its I/O status lands in.

    ``SELECT ACCTFILE-FILE ... FILE STATUS IS ACCTFILE-STATUS`` makes that
    variable an *output* of every READ, WRITE, OPEN and CLOSE on the file.
    Miss it and the status field looks like a plain input, which makes
    "the read succeeded, then hit end-of-file" read as a contradiction
    instead of as two outcomes of one operation.
    """
    out: dict = {}
    organizations = out.setdefault("__organizations__", {})
    current = None
    buffer = ""
    for line in read_lines(path):
        text = line.text
        if re.search(r"\bPROCEDURE\s+DIVISION\b", text, re.I):
            break
        buffer += " " + text.strip()
        m = _SELECT.search(buffer)
        if m:
            current = m.group(1).upper()
        st = _FILE_STATUS.search(buffer)
        if st and current:
            out[current] = st.group(1).upper()
        org = _ORGANIZATION.search(buffer)
        if org and current:
            organizations[current] = org.group(1).upper()
        if "." in text:
            buffer = ""
            if st:
                current = None
    return out


@dataclass
class DataModel:
    """Record layout: what contains what, and how wide each field is."""
    pic: dict = field(default_factory=dict)
    initial: dict = field(default_factory=dict)
    occurs: dict = field(default_factory=dict)
    keys: dict = field(default_factory=dict)      # table -> [(direction, field)]
    indexes: dict = field(default_factory=dict)   # table -> [index-name]
    children: dict = field(default_factory=dict)     # group -> all descendants
    parent: dict = field(default_factory=dict)
    declared: set = field(default_factory=set)
    condition_names: dict = field(default_factory=dict)   # 88 name -> (parent, values)
    usage: dict = field(default_factory=dict)             # field -> COMP-3/BINARY/...
    redefines: dict = field(default_factory=dict)         # field -> field it overlays
    sign: dict = field(default_factory=dict)              # field -> LEADING/TRAILING[ SEPARATE]
    justified: set = field(default_factory=set)           # fields aligned on the right
    origin: dict = field(default_factory=dict)            # field -> file it was declared in
    copybooks: list = field(default_factory=list)         # members actually COPYed
    file_status: dict = field(default_factory=dict)       # file -> status variable
    fd_records: dict = field(default_factory=dict)        # file -> record areas
    organization: dict = field(default_factory=dict)      # file -> SEQUENTIAL/INDEXED
    # Fields the source itself put in a CICS RESP/RESP2 operand. Evidence,
    # not inference: the program named them as its response channel.
    cics_resp: set = field(default_factory=set)

    def look(self, table: dict, name: str, default=None):
        """Read a per-field table, seeing through qualification.

        `ACSHLIMI OF CACTUPAI` is a distinct reference but the declaration it
        points at is `ACSHLIMI`, so identity and lookup want different keys.
        """
        upper = (name or "").upper()
        if upper in table:
            return table[upper]
        from .ir import base_name
        return table.get(base_name(upper), default)

    def pic_of(self, name: str) -> str:
        return self.look(self.pic, name, "") or ""

    def usage_of(self, name: str) -> str:
        return self.look(self.usage, name, "") or ""

    def knows(self, name: str) -> bool:
        from .ir import base_name
        upper = (name or "").upper()
        return upper in self.declared or base_name(upper) in self.declared

    def descendants(self, group: str) -> list[str]:
        return self.children.get(group.upper(), [])

    def merge(self, other: "DataModel") -> "DataModel":
        self.pic.update(other.pic)
        self.initial.update(other.initial)
        self.occurs.update(other.occurs)
        self.keys.update(other.keys)
        self.indexes.update(other.indexes)
        self.parent.update(other.parent)
        self.declared |= other.declared
        self.usage.update(other.usage)
        self.redefines.update(other.redefines)
        self.sign.update(other.sign)
        self.justified.update(other.justified)
        self.origin.update(other.origin)
        self.condition_names.update(other.condition_names)
        self.file_status.update(other.file_status)
        self.organization.update(other.organization)
        self.cics_resp |= other.cics_resp
        for f, recs in other.fd_records.items():
            self.fd_records.setdefault(f, []).extend(recs)
        for group, kids in other.children.items():
            self.children.setdefault(group, []).extend(kids)
        return self


def _source_tag(path: str) -> str:
    """A stable, upper-case, punctuation-free tag for one source file.

    Every table in the model is keyed by an upper-case name and read back
    with `.upper()`, so a tag carrying a lower-case extension would be
    written under one key and looked up under another.
    """
    return re.sub(r"[^A-Z0-9]", "", os.path.basename(path).upper())


def parse_data_division(path: str) -> DataModel:
    model = DataModel()
    control = parse_file_control(path)
    model.organization.update(control.pop("__organizations__", {}))
    model.file_status.update(control)
    model.fd_records.update(parse_fd_records(path))
    stack: list[tuple[int, str]] = []
    buffer = ""
    fillers = 0
    in_procedure = False

    for line in read_lines(path):
        if re.search(r"\bPROCEDURE\s+DIVISION\b", line.text, re.I):
            in_procedure = True
        if in_procedure:
            break
        buffer += " " + line.text.strip()
        if "." not in line.text:
            continue
        for chunk in _split_sentences(buffer):
            if not chunk.strip():
                continue
            m88 = _LEVEL88.match(chunk)
            if m88 and stack:
                values = _split_88_values(m88.group(2))
                model.condition_names[m88.group(1).upper()] = (stack[-1][1], values)
                continue
            m = _DECL.match(chunk)
            if not m:
                continue
            level, name, rest = int(m.group(1)), m.group(2).upper(), m.group(3)
            if level in (66, 88):
                continue
            if name == "FILLER":
                # Unreferenceable, but it occupies bytes: leave it out of the
                # declared set so nothing can bind it, and give it a unique
                # name so the record layout still adds up.
                fillers += 1
                # Unique across the whole program, not just this file. A
                # model is merged from the program and every copybook it
                # COPYs, and `merge` is a dict update - so a per-file counter
                # makes the sixth copybook's FILLER#1 overwrite the first
                # copybook's, reparenting those bytes into another record.
                # The name is synthetic and unreferenceable either way; what
                # matters is that it stays distinct after the merge, because
                # everything after a lost FILLER sits at the wrong offset.
                name = "FILLER#%s#%d" % (_source_tag(path), fillers)
            while stack and stack[-1][0] >= level:
                stack.pop()
            if not name.startswith("FILLER#"):
                model.declared.add(name)
            if stack:
                model.parent[name] = stack[-1][1]
                for _lvl, ancestor in stack:
                    model.children.setdefault(ancestor, []).append(name)
            p = _PIC_IN.search(rest)
            if p:
                model.pic[name] = p.group(1).rstrip(".")
            v = _VALUE_IN.search(rest)
            if v:
                # `VALUE LOW-VALUES` names a figurative constant, not a field
                # containing the ten letters "LOW-VALUES". Storing the text
                # makes every later comparison against it false.
                from .ir import parse_term as _pt
                raw = v.group(1)
                repeat = _VALUE_ALL.match(raw)
                if repeat:
                    unit = _pt(repeat.group(1))
                    body = "" if unit.value is None else str(unit.value)
                    from .layout import byte_length
                    try:
                        width = byte_length(model.pic.get(name, ""))
                    except Exception:                            # noqa: BLE001
                        width = 0
                    model.initial[name] = ((body * width)[:width]
                                           if width and body else body)
                else:
                    term = _pt(raw)
                    model.initial[name] = (term.value if term.kind == "const"
                                           else raw.strip("'\""))
            o = _OCCURS.search(rest)
            if o:
                model.occurs[name] = int(o.group(2) or o.group(1))
                found = occurs_keys(rest)
                if found:
                    model.keys[name] = found
                names = indexed_by(rest)
                if names:
                    # An index-name is not a data item and must not join
                    # `declared`: nothing may bind it as a program input, and
                    # the only thing that moves it is SET or a SEARCH.
                    model.indexes[name] = names
            u = _USAGE.search(rest)
            if u:
                raw = u.group(1).upper()
                model.usage[name] = _USAGE_CANON.get(raw, raw)
            rd = _REDEFINES.search(rest)
            if rd:
                model.redefines[name] = rd.group(1).upper()
            # A VALUE literal can contain the word too, and it is data there.
            if _JUSTIFIED.search(_QUOTED_RUN.sub("''", rest)):
                model.justified.add(name)
            sg = _SIGN.search(rest)
            if sg:
                model.sign[name] = (sg.group(1).upper()
                                    + (" SEPARATE" if sg.group(2) else "")).strip()
            model.origin[name] = os.path.basename(path)
            stack.append((level, name))
        buffer = ""

    # Fields the platform declares and the application never does: the EXEC
    # Interface Block, the SQLCA, the MQ constants. Only what the source has
    # earned by issuing the corresponding verb, and only where it did not
    # declare the name itself - a program that ships its own copy wins.
    from .platform_decls import declarations_for, constants_for
    try:
        with open(path, "r", errors="replace") as fh:
            text = fh.read()
    except OSError:
        text = ""
    # `EXEC CICS ... RESP(WS-RC)` is the program declaring its own response
    # channel. That is source evidence, and it is the only thing that makes a
    # field a RESP field - a name ending in -RESP is a guess about how someone
    # writes COBOL, which this repository does not do.
    for m in re.finditer(r"\bRESP2?\s*\(\s*([A-Z0-9][A-Z0-9-]*)\s*\)", text, re.I):
        model.cics_resp.add(m.group(1).upper())

    supplied, usage = declarations_for(text)
    for name, spec in supplied.items():
        if name not in model.pic:
            model.pic[name] = spec
            model.declared.add(name)
            model.origin[name] = "<platform>"
    for name, how in usage.items():
        model.usage.setdefault(name, how)
    for name, value in constants_for(text).items():
        if name not in model.pic:
            model.pic[name] = "S9(9)"
            model.initial[name] = value
            model.declared.add(name)
            model.origin[name] = "<platform>"
    return model


# --------------------------------------------------------------------------
# Procedure division
# --------------------------------------------------------------------------

VERBS = {
    "ACCEPT", "ADD", "ALTER", "CALL", "CANCEL", "CLOSE", "COMPUTE", "CONTINUE",
    "DELETE", "DISPLAY", "DIVIDE", "ENTRY", "EVALUATE", "EXEC", "EXIT", "GO",
    "GOBACK", "IF", "INITIALIZE", "INSPECT", "MERGE", "MOVE", "MULTIPLY",
    "OPEN", "PERFORM", "READ", "RELEASE", "RETURN", "REWRITE", "SEARCH", "SET",
    "SORT", "START", "STOP", "STRING", "SUBTRACT", "UNSTRING", "WRITE",
}
_SCOPE_ENDS = {
    "END-IF", "END-EVALUATE", "END-PERFORM", "END-READ", "END-CALL",
    "END-STRING", "END-UNSTRING", "END-SEARCH", "END-ADD", "END-SUBTRACT",
    "END-MULTIPLY", "END-DIVIDE", "END-COMPUTE", "END-EXEC", "END-WRITE",
    "END-DELETE", "END-START", "END-RETURN", "END-REWRITE", "END-ACCEPT",
    "END-DISPLAY", "END-INSPECT",
}
_BOUNDARY = VERBS | _SCOPE_ENDS | {"ELSE", "WHEN", "."}

# The conditional phrases an I/O or arithmetic statement can carry. Each is a
# *decision*: `READ ... AT END <stmts>` runs those statements only when the
# read hit end-of-file. Parsed as plain siblings - which is what happens when
# the keywords are not scope boundaries - the handler runs unconditionally, so
#
#     READ TR-RECORD ... AT END MOVE 'Y' TO LASTREC END-READ
#     PERFORM UNTIL LASTREC = 'Y' ... END-PERFORM
#
# sets the end-of-file flag on the first pass and the whole loop body becomes
# unreachable. Every COBOL read loop is written this way, so this is not an
# edge case; it is the shape of batch COBOL.
_PHRASES = {
    ("AT", "END"): "at_end",
    ("NOT", "AT", "END"): "not_at_end",
    ("INVALID", "KEY"): "invalid_key",
    ("NOT", "INVALID", "KEY"): "not_invalid_key",
    ("ON", "SIZE", "ERROR"): "on_size_error",
    ("NOT", "ON", "SIZE", "ERROR"): "not_on_size_error",
    ("ON", "OVERFLOW"): "on_overflow",
    ("NOT", "ON", "OVERFLOW"): "not_on_overflow",
    ("ON", "EXCEPTION"): "on_exception",
    ("NOT", "ON", "EXCEPTION"): "not_on_exception",
}
_PHRASE_HEADS = {"AT", "NOT", "ON", "INVALID"}

_WORD = re.compile(r"'[^']*'|\"[^\"]*\"|[^\s]+")


@dataclass
class Token:
    word: str
    line: int


def tokenize(lines: Iterable[Line]) -> list[Token]:
    """Words, with a trailing sentence period split off as its own token."""
    tokens: list[Token] = []
    for line in lines:
        for raw in _WORD.findall(line.text):
            if raw.startswith(("'", '"')):
                tokens.append(Token(raw, line.number))
                continue
            while raw.endswith(".") and not re.match(r"^[\d.]+$", raw):
                tokens.append(Token(raw[:-1], line.number)) if raw[:-1] else None
                tokens.append(Token(".", line.number))
                raw = ""
            if raw:
                tokens.append(Token(raw, line.number))
    return [t for t in tokens if t.word]


# The separator period may be preceded by space: `1000-INIT .` and
# `DATE-CONV SECTION .` are both legal and both appear in real source.
# Requiring the period to touch the name loses the paragraph entirely - not
# as an error, but as statements silently absorbed into whichever paragraph
# came before, so its label is unreachable and its body is attributed to a
# neighbour.
_PARA_HEADER = re.compile(r"^([A-Z0-9][A-Z0-9-]*)\s*\.\s*$", re.I)
# `B1. ADD 1 TO WS-C1.` - a label sharing its line with the first sentence.
_PARA_INLINE = re.compile(r"^([A-Z0-9][A-Z0-9-]*)\s*\.\s+(\S.*)$", re.I)
# Words that end a sentence on their own and are not labels, so a line like
# `EXIT. MOVE A TO B` is not read as a paragraph called EXIT. Verbs, not
# names: a paragraph may legally be called anything else.
_RESERVED_SENTENCE = re.compile(
    r"^(?:EXIT|CONTINUE|GOBACK|STOP|NEXT|END-IF|END-EVALUATE|END-PERFORM|"
    r"ELSE|WHEN|THEN)$", re.I)
_SECTION = re.compile(r"^([A-Z0-9][A-Z0-9-]*)\s+SECTION\s*\.\s*$", re.I)


def _procedure_lines(lines: list[Line]) -> list[Line]:
    for i, line in enumerate(lines):
        if re.search(r"\bPROCEDURE\s+DIVISION\b", line.text, re.I):
            rest = lines[i:]
            # The DIVISION header itself may carry a USING clause and a period.
            while rest and "." not in rest[0].text:
                rest = rest[1:]
            return rest[1:]
    return []


ENTRY_PARAGRAPH = "_ENTRY_"


def split_paragraphs(lines: list[Line]) -> list[tuple[str, list[Line]]]:
    """Area-A labels start paragraphs; everything after one belongs to it.

    Statements can also sit directly under ``PROCEDURE DIVISION`` with no
    label at all, and that unnamed run is where the program *starts*.
    Dropping it - as any parser that waits for the first label does - hides
    the real entry point and makes the first named paragraph look like the
    mainline, which is usually a subroutine.  It is collected here under a
    synthetic name that cannot collide with a COBOL identifier, and which
    nothing can PERFORM, because nothing can.
    """
    paragraphs: list[tuple[str, list[Line]]] = []
    current_name: str | None = None
    current: list[Line] = []
    for line in lines:
        stripped = line.text.strip()
        indent = len(line.text) - len(line.text.lstrip())
        header = _PARA_HEADER.match(stripped) or _SECTION.match(stripped)
        if header and indent <= 4:
            if current_name is not None:
                paragraphs.append((current_name, current))
            current_name, current = header.group(1).upper(), []
            continue
        # A label may share its line with the sentence that follows it -
        # `B1. ADD 1 TO WS-C1.` is one paragraph, not one statement. Requiring
        # the label to own the line loses the paragraph silently: nothing can
        # PERFORM it, so every call to it does nothing at all and the body is
        # attributed to whichever paragraph came before. Only Area A is
        # considered, where a bare word followed by a period is a label by
        # position rather than by guesswork.
        inline = _PARA_INLINE.match(stripped) if indent <= 4 else None
        if inline and not _RESERVED_SENTENCE.match(inline.group(1)):
            if current_name is not None:
                paragraphs.append((current_name, current))
            current_name = inline.group(1).upper()
            current = [Line(line.number,
                            " " * 11 + inline.group(2))]
            continue
        if current_name is None:
            current_name = ENTRY_PARAGRAPH
        current.append(line)
    if current_name is not None and current:
        paragraphs.append((current_name, current))
    return paragraphs


def node(kind: str, tokens: list[Token], attributes: dict | None = None,
         children: list | None = None) -> dict:
    text = " ".join(t.word for t in tokens)
    return {
        "type": kind,
        "text": text,
        "line_start": tokens[0].line if tokens else 0,
        "line_end": tokens[-1].line if tokens else 0,
        "attributes": attributes or {},
        "children": children or [],
    }


class _Parser:
    def __init__(self, tokens: list[Token]):
        self.t = tokens
        self.i = 0

    def peek(self, ahead: int = 0) -> str:
        at = self.i + ahead
        return self.t[at].word.upper() if at < len(self.t) else ""

    def done(self) -> bool:
        return self.i >= len(self.t)

    def take_until_boundary(self, stop_at_phrase: bool = False) -> list[Token]:
        start = self.i
        while not self.done() and self.peek() not in _BOUNDARY:
            if stop_at_phrase and self.phrase_at(self.i):
                break
            self.i += 1
        return self.t[start:self.i]

    def phrase_at(self, index: int):
        """``(phrase, word count)`` if a conditional phrase starts here.

        A phrase can only *begin* a clause, so recognising it by position is
        safe where recognising it by keyword would not be: `IF A NOT = B` has
        a NOT that belongs to the condition, and conditions are never read
        with this on.
        """
        if index >= len(self.t):
            return None
        if self.t[index].word.upper() not in _PHRASE_HEADS:
            return None
        words = [t.word.upper() for t in self.t[index:index + 4]]
        for length in (4, 3, 2):
            if tuple(words[:length]) in _PHRASES:
                return _PHRASES[tuple(words[:length])], length
        return None

    def take_phrase(self):
        """Consume a conditional phrase at the cursor, and name it.

        The phrase has to be found *before* the statement it guards is parsed,
        not peeled off the end afterwards. Peeling works for the first phrase
        of a statement and fails for the second: in

            READ F INVALID KEY PERFORM A NOT INVALID KEY PERFORM B

        the inner `PERFORM A` runs to the next verb, so it swallows
        `NOT INVALID KEY` as part of its own operand list, the second phrase
        disappears, and `PERFORM B` ends up inside the *first* arm - running
        on the outcome it was written to exclude. Both arms then fire on the
        same outcome and neither direction of the decision is what the
        compiler produces.
        """
        found = self.phrase_at(self.i)
        if not found:
            return None
        phrase, length = found
        self.i += length
        return phrase

    def statements(self, stop: set) -> list[dict]:
        out: list[dict] = []
        while not self.done():
            word = self.peek()
            if word in stop:
                break
            if word == ".":
                self.i += 1
                if "." in stop:
                    break
                continue
            if word in _SCOPE_ENDS:
                self.i += 1
                continue
            stmt = self.statement()
            if stmt:
                out.append(stmt)
        return out

    def statement(self) -> dict | None:
        word = self.peek()
        # `EXIT PERFORM` is one statement whose second word is also a verb, so
        # the boundary rule splits it into a bare EXIT followed by an inline
        # PERFORM that swallows the rest of the loop body. Everything after
        # the early exit then runs inside a loop of its own.
        if word == "EXIT" and self.peek(1) == "PERFORM":
            head = self.t[self.i]
            self.i += 2
            cycle = self.peek() == "CYCLE"
            if cycle:
                self.i += 1
            return node("EXIT_PERFORM_CYCLE" if cycle else "EXIT_PERFORM",
                        [head], {}, [])
        if word == "IF":
            return self.if_statement()
        if word == "EVALUATE":
            return self.evaluate_statement()
        if word == "PERFORM":
            return self.perform_statement()
        if word == "GO":
            return self.go_statement()
        if word == "SEARCH":
            return self.search_statement()
        return self.simple_statement()

    # -- individual forms --------------------------------------------------
    def if_statement(self) -> dict:
        head = self.t[self.i]
        self.i += 1
        condition = self.take_until_boundary()
        if self.peek() == "THEN":
            self.i += 1
        body = self.statements({"ELSE", "END-IF", "."})
        children = list(body)
        if self.peek() == "ELSE":
            else_head = self.t[self.i]
            self.i += 1
            else_body = self.statements({"END-IF", "."})
            children.append(node("ELSE", [else_head], {}, else_body))
        if self.peek() == "END-IF":
            self.i += 1
        text = "IF " + " ".join(t.word for t in condition)
        return {"type": "IF", "text": text, "line_start": head.line,
                "line_end": head.line,
                "attributes": {"condition": " ".join(t.word for t in condition)},
                "children": children}

    def evaluate_statement(self) -> dict:
        head = self.t[self.i]
        self.i += 1
        subject = self.take_until_boundary()
        arms: list[dict] = []
        while self.peek() == "WHEN":
            when_head = self.t[self.i]
            self.i += 1
            value = self.take_until_boundary()
            body = self.statements({"WHEN", "END-EVALUATE", "."})
            arms.append({"type": "WHEN",
                         "text": "WHEN " + " ".join(t.word for t in value),
                         "line_start": when_head.line, "line_end": when_head.line,
                         "attributes": {"value": " ".join(t.word for t in value)},
                         "children": body})
        if self.peek() == "END-EVALUATE":
            self.i += 1
        # Consecutive WHENs share the body that follows them:
        #     WHEN A
        #     WHEN B
        #        do-it
        # is `A OR B` guarding one body, not an arm A that does nothing.
        # Left uncorrected, arm A is a hole - taking it exits the EVALUATE,
        # and every branch inside the body becomes unreachable by that route.
        # `shared` is deliberately the same list object, so the statements
        # keep one identity; callers that count branches must key by
        # position rather than by object.
        for index in range(len(arms) - 2, -1, -1):
            if not arms[index]["children"]:
                arms[index]["children"] = arms[index + 1]["children"]
                arms[index]["attributes"]["shares_body_with"] = \
                    arms[index + 1]["attributes"].get("value", "")
        return {"type": "EVALUATE",
                "text": "EVALUATE " + " ".join(t.word for t in subject),
                "line_start": head.line, "line_end": head.line,
                "attributes": {"subject": " ".join(t.word for t in subject)},
                "children": arms}

    def perform_statement(self) -> dict:
        head = self.t[self.i]
        self.i += 1
        # A PERFORM inside a conditional handler must not run on past the
        # phrase that ends the handler: `PERFORM A NOT INVALID KEY` is one
        # statement and one phrase, not a PERFORM of four words.
        words = self.take_until_boundary(stop_at_phrase=True)
        upper = [w.word.upper() for w in words]
        text = "PERFORM " + " ".join(w.word for w in words)

        # PERFORM <name> [THRU <name>] - a call, unless a loop clause follows.
        # `PERFORM WS-COUNT TIMES` opens with an identifier and is a loop, not
        # a call: read as `PERFORM <paragraph>` the parser goes looking for a
        # paragraph named after the counter, finds none, and the body that
        # followed becomes ordinary statements that run exactly once.
        # `PERFORM A 3 TIMES` and `PERFORM A WS-N TIMES` are out-of-line
        # loops over a named paragraph: TIMES appears at index 2 or later,
        # after the target. `PERFORM WS-N TIMES` is the inline form, where it
        # is at index 1 and the first word is the count. Excluding every
        # statement containing TIMES sent the out-of-line form to the inline
        # parser, which swallowed the target name and ran the following
        # statements once.
        _times_at = upper.index("TIMES") if "TIMES" in upper else -1
        if words and upper[0] not in ("UNTIL", "VARYING", "WITH", "TEST") \
                and not re.match(r"^\d+$", upper[0]) \
                and (_times_at < 0 or _times_at >= 2):
            target = words[0].word.upper()
            attrs: dict[str, Any] = {"target": target}
            if "THRU" in upper or "THROUGH" in upper:
                k = upper.index("THRU") if "THRU" in upper else upper.index("THROUGH")
                if k + 1 < len(words):
                    attrs["target"] = "%s THRU %s" % (target, words[k + 1].word.upper())
            rest = " ".join(w.word for w in words[1:])
            # A loop clause on an out-of-line PERFORM was dropped entirely:
            # `PERFORM A VARYING I FROM 1 BY 1 UNTIL I > 3` kept only the
            # UNTIL, so the induction variable was never initialised and
            # never stepped. With I left at its initial value the condition
            # is decided once and the body runs zero times - not a wrong
            # count, no iterations at all.
            if re.search(r"\bTEST\s+AFTER\b", rest, re.I):
                attrs["test_after"] = True
            if "VARYING" in upper:
                attrs["varying"] = rest[rest.upper().index("VARYING"):]
                return {"type": "PERFORM", "text": text,
                        "line_start": head.line, "line_end": head.line,
                        "attributes": attrs, "children": []}
            if _times_at >= 2:
                attrs["times"] = " ".join(w.word for w in words[1:])
                return {"type": "PERFORM", "text": text,
                        "line_start": head.line, "line_end": head.line,
                        "attributes": attrs, "children": []}
            m = re.search(r"\bUNTIL\b(.*)", rest, re.I)
            if m:
                attrs["condition"] = m.group(1).strip()
                # No inline body. `PERFORM A UNTIL X` loops over paragraph A;
                # COBOL has no form with both a target and an inline body, so
                # reading the following statements as one put whatever came
                # next *inside* the loop. Written without an intervening
                # period the next statement was swallowed - a GOBACK became
                # the loop body, ending the run on the first iteration before
                # the target had run at all.
                return {"type": "PERFORM", "text": text, "line_start": head.line,
                        "line_end": head.line, "attributes": attrs,
                        "children": []}
            return {"type": "PERFORM", "text": text, "line_start": head.line,
                    "line_end": head.line, "attributes": attrs, "children": []}

        # Inline PERFORM: UNTIL / VARYING / n TIMES.
        attrs = {}
        joined = " ".join(w.word for w in words)
        # WITH TEST AFTER makes the loop do-while: the body runs once before
        # the condition is ever evaluated. Dropping it turns a loop that
        # always executes into one that may never execute, and the branch
        # after it sees a counter that was never incremented.
        if re.search(r"\bTEST\s+AFTER\b", joined, re.I):
            attrs["test_after"] = True
        if "VARYING" in upper:
            attrs["varying"] = joined[joined.upper().index("VARYING"):]
        else:
            m = re.search(r"\bUNTIL\b(.*)", joined, re.I)
            if m:
                attrs["condition"] = m.group(1).strip()
            elif re.search(r"\bTIMES\b", joined, re.I):
                attrs["times"] = joined
        body = self.statements({"END-PERFORM", "."})
        if self.peek() == "END-PERFORM":
            self.i += 1
        return {"type": "PERFORM_INLINE", "text": text, "line_start": head.line,
                "line_end": head.line, "attributes": attrs, "children": body}

    def search_statement(self) -> dict:
        """``SEARCH`` and ``SEARCH ALL``: an n-way decision, not a call.

        Both formats carry an optional ``AT END`` and one or more ``WHEN``
        arms, and every one of those is a direction a test can go.  Read as
        an opaque statement - which is what happens when the verb has no rule
        of its own - the arms parse as free-standing statements that run
        unconditionally, so the body of every WHEN executes on every pass and
        AT END executes as well.  That is not a partial model of SEARCH; it
        is a different program.
        """
        head = self.t[self.i]
        self.i += 1
        binary = self.peek() == "ALL"
        if binary:
            self.i += 1
        words = self.take_until_boundary(stop_at_phrase=True)
        phrase = self.take_phrase()
        joined = " ".join(w.word for w in words)
        m = re.search(r"\bVARYING\s+([A-Z0-9][A-Z0-9-]*)", joined, re.I)
        attrs: dict[str, Any] = {
            "table": words[0].word.upper() if words else "",
            "all": binary,
            "varying": m.group(1).upper() if m else "",
        }
        children: list = []
        stop = {"WHEN", "END-SEARCH", "."}
        if phrase == "at_end":
            body = self.statements(stop)
            children.append({"type": "PHRASE", "text": "AT END",
                             "line_start": head.line, "line_end": head.line,
                             "attributes": {"phrase": "at_end"},
                             "children": body})
        while self.peek() == "WHEN":
            when_head = self.t[self.i]
            self.i += 1
            value = self.take_until_boundary()
            body = self.statements(stop)
            children.append({"type": "WHEN",
                             "text": "WHEN " + " ".join(t.word for t in value),
                             "line_start": when_head.line,
                             "line_end": when_head.line,
                             "attributes": {"value":
                                            " ".join(t.word for t in value)},
                             "children": body})
        if self.peek() == "END-SEARCH":
            self.i += 1
        return {"type": "SEARCH",
                "text": "SEARCH " + ("ALL " if binary else "") + joined,
                "line_start": head.line, "line_end": head.line,
                "attributes": attrs, "children": children}

    def go_statement(self) -> dict:
        head = self.t[self.i]
        self.i += 1
        if self.peek() == "TO":
            self.i += 1
        words = self.take_until_boundary()
        joined = " ".join(w.word for w in words)
        target = words[0].word.upper() if words else ""
        m = re.search(r"\bDEPENDING\s+ON\s+([A-Z0-9-]+)", joined, re.I)
        attrs: dict[str, Any] = {"target": target, "depending": bool(m)}
        if m:
            # `GO TO L1 L2 L3 DEPENDING ON K` is a computed jump: K selects
            # the K-th label, one-based, and falls through when K is outside
            # the list. Keeping only the first label turns an n-way switch
            # into an unconditional branch, so n-1 arms become unreachable
            # and the edges to them never appear in the call graph.
            head_part = joined[:m.start()]
            attrs["targets"] = [w.upper() for w in
                                re.findall(r"[A-Z0-9][A-Z0-9-]*", head_part, re.I)
                                if w.upper() not in ("TO", "GO")]
            attrs["selector"] = m.group(1).upper()
        return {"type": "GO_TO",
                "text": "GO TO " + joined,
                "line_start": head.line, "line_end": head.line,
                "attributes": attrs,
                "children": []}

    def simple_statement(self) -> dict:
        head = self.t[self.i]
        verb = self.peek()
        self.i += 1
        if verb == "EXEC":                       # runs to END-EXEC, not a verb
            start = self.i
            while not self.done() and self.peek() != "END-EXEC":
                self.i += 1
            words = self.t[start:self.i]
            if not self.done():
                self.i += 1
            body = " ".join(w.word for w in words)
            return {"type": "EXEC", "text": "EXEC " + body,
                    "line_start": head.line,
                    "line_end": words[-1].line if words else head.line,
                    "attributes": {"body": body}, "children": []}

        # A conditional phrase turns the rest into a guarded handler rather
        # than the next statement, so the scan stops where the phrase begins
        # and the keywords are consumed as a unit.
        words = self.take_until_boundary(stop_at_phrase=True)
        phrase = self.take_phrase()
        text = verb + (" " + " ".join(w.word for w in words) if words else "")
        attrs: dict[str, Any] = {}
        children: list = []
        while phrase:
            body = self.statements(_SCOPE_ENDS | {"."} | _PHRASE_HEADS)
            children.append({"type": "PHRASE", "text": phrase,
                             "line_start": head.line, "line_end": head.line,
                             "attributes": {"phrase": phrase},
                             "children": body})
            phrase = self.take_phrase()
        if children:
            attrs["phrases"] = [c["attributes"]["phrase"] for c in children]
        if verb == "MOVE":
            joined = " ".join(w.word for w in words)
            m = re.split(r"\s+TO\s+", joined, maxsplit=1, flags=re.I)
            if len(m) == 2:
                attrs["source"], attrs["targets"] = m[0].strip(), m[1].strip()
        elif verb == "CALL":
            if words:
                attrs["target"] = words[0].word.strip("'\"").upper()
        elif verb == "ALTER":
            m = re.search(r"([A-Z0-9-]+)\s+TO\s+(?:PROCEED\s+TO\s+)?([A-Z0-9-]+)",
                          " ".join(w.word for w in words), re.I)
            if m:
                attrs["altered"] = m.group(1).upper()
                attrs["destination"] = m.group(2).upper()
        elif verb == "SET":
            joined = " ".join(w.word for w in words)
            # `SET IX UP BY 1` is the only way an index moves without a
            # SEARCH, and `SET A B TO 1` sets both.  Recognising only the
            # single `TO` form leaves an index frozen wherever it was, so
            # every table reference through it reads the same occurrence.
            def _receiver_names(raw: str) -> list:
                names = [n.upper() for n in re.split(r"[,\s]+", raw.strip()) if n]
                # `SET ADDRESS OF X TO ...` is a pointer form whose receiver is
                # not a list of names; taking the last word keeps the previous
                # behaviour rather than inventing two extra variables.
                if all(re.fullmatch(r"[A-Z0-9][A-Z0-9-]*", n) for n in names):
                    return names
                return names[-1:] if names else []

            m = re.match(r"(.+?)\s+(UP|DOWN)\s+BY\s+(\S+)", joined, re.I)
            if m:
                names = _receiver_names(m.group(1))
                attrs["names"] = names
                attrs["name"] = names[0] if names else ""
                attrs["direction"] = m.group(2).upper()
                attrs["amount"] = m.group(3).upper().strip(".")
            else:
                m = re.match(r"(.+?)\s+TO\s+(\S+)", joined, re.I)
                if m:
                    names = _receiver_names(m.group(1))
                    attrs["names"] = names
                    attrs["name"] = names[0] if names else ""
                    attrs["value"] = m.group(2).upper().strip(".")
        kind = {"GOBACK": "GOBACK", "STOP": "STOP", "EXIT": "EXIT"}.get(verb, verb)
        if children:
            return {"type": kind, "text": text, "line_start": head.line,
                    "line_end": words[-1].line if words else head.line,
                    "attributes": attrs, "children": children}
        if kind == "EXIT" and words:
            # A bare `EXIT` is a no-op landing pad. `EXIT PARAGRAPH` and
            # `EXIT SECTION` are control flow - they leave the paragraph the
            # way a GO TO its end would - and `EXIT PROGRAM` ends the run.
            # Reading all three as the no-op means the statements after an
            # early exit look reachable when they are not.
            first = words[0].word.upper()
            if first in ("PARAGRAPH", "SECTION"):
                kind = "EXIT_PARAGRAPH"
            elif first == "PROGRAM":
                kind = "EXIT_PROGRAM"
            elif first == "PERFORM":
                # `EXIT PERFORM` leaves the inline loop and `EXIT PERFORM
                # CYCLE` skips to its next iteration. Read as the no-op both
                # run the rest of the body, so a loop written to stop early
                # runs to its bound and whatever it was accumulating is off.
                kind = ("EXIT_PERFORM_CYCLE"
                        if len(words) > 1 and words[1].word.upper() == "CYCLE"
                        else "EXIT_PERFORM")
        return {"type": kind, "text": text, "line_start": head.line,
                "line_end": words[-1].line if words else head.line,
                "attributes": attrs, "children": []}


def parse_procedure(lines: list[Line]) -> list[dict]:
    paragraphs = []
    for name, body in split_paragraphs(_procedure_lines(lines)):
        parser = _Parser(tokenize(body))
        statements = parser.statements(set())
        _stamp_ordinals(statements)
        paragraphs.append({
            "name": name,
            "line_start": body[0].number if body else 0,
            "line_end": body[-1].number if body else 0,
            "statements": statements,
        })
    return paragraphs


# --------------------------------------------------------------------------
# Program
# --------------------------------------------------------------------------

@dataclass
class Program:
    name: str
    paragraphs: list
    model: DataModel
    source_path: str = ""

    @property
    def paragraph_names(self) -> list[str]:
        return [p["name"] for p in self.paragraphs]

    def paragraph(self, name: str) -> dict | None:
        upper = name.upper()
        for p in self.paragraphs:
            if p["name"] == upper:
                return p
        return None

    @property
    def duplicate_paragraphs(self) -> dict:
        """Names declared more than once, and how many times.

        A COBOL program may legally repeat a paragraph name in different
        sections, and `PERFORM` then means the one in scope. This parser keeps
        a flat list and `paragraph()` returns the first, so every later
        namesake is shadowed: its statements are parsed, indexed, and
        unreachable by name. Nothing about that is visible in a plan - the
        chain simply routes to the wrong body.

        Reported rather than resolved. Resolving needs section-qualified
        identity throughout, and a silent wrong answer is worse than a stated
        limitation: an agent that knows two paragraphs share a name can at
        least distrust the chain that names one.
        """
        counts: dict = {}
        for p in self.paragraphs:
            counts[p["name"]] = counts.get(p["name"], 0) + 1
        return {name: n for name, n in counts.items() if n > 1}


_COPYBOOK_DIRS = ("cpy", "copy", "copybook", "copybooks", "cpylib", "include",
                  "cpy-bms")


# The member name may be quoted - `COPY 'CSUTLDWY'.` is legal, and matching
# only the bare form means the copybook is silently never read: every field
# it declares loses its PIC, its VALUE and its 88-levels, and the conditions
# on them become unplannable.
_COPY = re.compile(r"^\s*COPY\s+[\'\"]?([A-Z0-9][A-Z0-9-]*)", re.I)
_COPY_SUFFIXES = ("", ".cpy", ".CPY", ".cbl", ".CBL", ".cob", ".COB", ".txt")


_COPY_STMT = re.compile(
    r"^\s*COPY\s+[\'\"]?([A-Z0-9][A-Z0-9-]*)[\'\"]?\s*(.*)$", re.I | re.S)
_PSEUDO = re.compile(r"==(.*?)==\s+BY\s+==(.*?)==", re.I | re.S)
_PLAIN_REPL = re.compile(r"(\S+)\s+BY\s+(\S+)", re.I)


def _replacements(clause: str) -> list:
    """The (from, to) pairs of a REPLACING clause.

    Pseudo-text (``==(TESTVAR1)== BY ==CASH-LIMIT==``) is the form that
    matters: it is how one copybook becomes twenty-five paragraphs of
    generated code, and every branch inside those copies is real code that a
    compiler sees and an unexpanded parser does not.
    """
    pairs = [(m.group(1).strip(), m.group(2).strip())
             for m in _PSEUDO.finditer(clause)]
    if pairs:
        return pairs
    body = re.sub(r"^\s*REPLACING\s+", "", clause, flags=re.I)
    return [(m.group(1).strip(), m.group(2).strip())
            for m in _PLAIN_REPL.finditer(body)]


def _stamp_ordinals(statements: list) -> None:
    """Give every statement in a paragraph a distinct position.

    Line numbers do not identify a statement. `COPY ... REPLACING` expands a
    member at the site of the directive, and every line it produces carries
    the directive's own number - so two different IFs from one copybook are
    indistinguishable by (paragraph, line, kind). On COACTUPC that collapsed
    45 of 401 decisions onto another, in the coverage denominator and in the
    hit set alike: covering one scored both.

    The ordinal is assigned in source order, so it is stable across runs, and
    `line_start` is left alone because the COPY site is the right thing to
    show a human.

    Statements shared by consecutive WHEN arms are one object and so take one
    ordinal, which is what makes the shared body count once.
    """
    counter = [0]

    def walk(stmt: dict) -> None:
        if "ordinal" in stmt:            # shared body, already numbered
            return
        stmt["ordinal"] = counter[0]
        counter[0] += 1
        for child in stmt.get("children") or []:
            walk(child)

    for stmt in statements:
        walk(stmt)


def expand_copies(lines: list, directories, depth: int = 0) -> list:
    """Inline COPY members, applying REPLACING, the way a compiler would.

    Without this a paragraph assembled from copies looks nearly empty: its
    conditions are in the member, so they are neither counted nor coverable,
    and the coverage denominator quietly understates the program.
    """
    if depth > 5 or not directories:
        return lines
    out: list = []
    pending = ""
    for line in lines:
        text = line.text
        if pending or re.match(r"^\s*COPY\s", text, re.I):
            pending += " " + text.strip()
            if "." not in text:
                continue
            statement, pending = pending, ""
            m = _COPY_STMT.match(statement.strip().rstrip("."))
            resolved = resolve_member(m.group(1).upper(), directories) if m else None
            if resolved is None:
                continue                       # unresolvable: drop the directive
            body = read_lines(resolved)
            pairs = _replacements(m.group(2) or "")
            for inner in expand_copies(body, directories, depth + 1):
                replaced = inner.text
                for src, dst in pairs:
                    replaced = replaced.replace(src, dst)
                out.append(Line(line.number, replaced))
            continue
        out.append(line)
    return out


def copy_members(source: str) -> list:
    """The copybooks a program actually COPYs.

    Loading every copybook in the directory is over-inclusive: it inflates the
    set of declared names, which is what live-in filtering and record
    association both key off, and on an estate where two copybooks define the
    same name differently it silently picks one. The program says which ones
    it wants.
    """
    out = []
    for line in read_lines(source):
        m = _COPY.match(line.text)
        if m:
            out.append(m.group(1).upper())
    return list(dict.fromkeys(out))


def resolve_member(member: str, directories) -> str | None:
    for directory in directories:
        for suffix in _COPY_SUFFIXES:
            candidate = os.path.join(directory, member + suffix)
            if os.path.isfile(candidate):
                return candidate
            lower = os.path.join(directory, member.lower() + suffix)
            if os.path.isfile(lower):
                return lower
    return None


def find_copybooks(source: str) -> list:
    """Conventional copybook directories beside or just above the source.

    Worth doing automatically rather than on request: a field whose copybook
    is missing has no PIC, and without a PIC there is no width, no sign, no
    boundary value and nothing to check a candidate against. Measured on
    CardDemo, supplying the copybooks resolves 31% of the values the tool
    would otherwise have to ask about - far more than any amount of
    inference from names.
    """
    here = os.path.dirname(os.path.abspath(source))
    found = []
    for base in (here, os.path.dirname(here)):
        # Match the directory name case-insensitively by listing the parent
        # rather than probing a guessed spelling. `COPYBOOK` and `Copybook`
        # are both common, and on a case-sensitive filesystem - which is
        # every Linux box this will ever run on - probing the lower-case
        # spelling silently finds nothing. The result is not an error: the
        # copybooks are simply never read, every field they declare loses
        # its PIC, and coverage is quietly worse.
        try:
            entries = os.listdir(base)
        except OSError:
            continue
        for entry in sorted(entries):
            if entry.lower() in _COPYBOOK_DIRS:
                candidate = os.path.join(base, entry)
                if os.path.isdir(candidate):
                    found.append(candidate)
    return found


_WHEN_TEXT = re.compile(r"^(?:WHEN\s+)+", re.I)


def _reparse_attributes(stmt: dict):
    """Attributes re-derived from a statement's own text, or None.

    An AST producer may type a statement correctly and still record none
    of what it says: in one 35k-line program every ``SET``, ``WHEN``,
    ``GO TO ... DEPENDING`` and ``SEARCH`` arrived with an empty attribute
    map. The handlers read attributes, so each was a silent no-op - 128
    ``SET``s that never set a flag, 41 ``WHEN`` arms that compared against
    the empty string. Re-parsing the text through this module's own parser
    keeps one definition of what a statement means, rather than a second
    approximate one living in the adoption layer.

    Only ever *adds* what was missing: a statement that already carries
    attributes is left alone, and a re-parse that disagrees about the
    statement's type is discarded.
    """
    text = " ".join(str(stmt.get("text") or "").split())
    kind = stmt.get("type")
    if not text or not kind:
        return None
    if kind == "WHEN":
        # A WHEN arm parses only inside its EVALUATE, and its text may
        # repeat the keyword the producer already consumed.
        value = _WHEN_TEXT.sub("", text).strip()
        return {"value": value} if value else None
    try:
        parsed = _Parser(tokenize([Line(stmt.get("line_start", 0) or 0,
                                        text)])).statements(set())
    except Exception:                                        # noqa: BLE001
        return None
    if not parsed or parsed[0].get("type") != kind:
        return None
    return parsed[0].get("attributes") or None


def _adopt_ast(paragraphs: list) -> list:
    """Bring a pre-parsed AST to the shape the parser itself produces.

    Two gaps, both silent when left open. Some AST producers write
    ``PERFORM A THRU B`` as its own statement type, ``PERFORM_THRU``, with
    the range in ``attributes.target``/``attributes.thru`` - but every
    consumer here (interpreter, graph, closures) matches ``PERFORM`` with
    the range in the target text, so the unrecognised type executes as a
    no-op and the program's callees never run: a 1,035-paragraph batch
    program measured 2 reachable. And such ASTs carry no ordinals, so
    every decision of a kind in a paragraph collapses onto one coverage
    key (the same failure `_stamp_ordinals` exists to prevent on COPY
    expansion).
    """
    def adopt(stmt: dict) -> None:
        if not (stmt.get("attributes") or {}) and stmt.get("text"):
            recovered = _reparse_attributes(stmt)
            if recovered:
                stmt["attributes"] = recovered
        if stmt.get("type") == "PERFORM_THRU":
            stmt["type"] = "PERFORM"
            attrs = stmt.get("attributes") or {}
            target = (attrs.get("target") or "").strip()
            thru = (attrs.pop("thru", "") or "").strip()
            if thru:
                attrs["target"] = target + " THRU " + thru
            condition = attrs.get("condition")
            if condition:
                # An inline `*>` comment swallowed into the clause text
                # runs to what was the end of its source line; the clause
                # resumes at the next connective. Best effort - a comment
                # containing OR/AND would survive, none measured did.
                condition = re.sub(r"\*>.*?(?=\bOR\b|\bAND\b|$)", " ",
                                   condition, flags=re.I | re.S)
                condition = condition.strip()
                m = re.match(r"(?:WITH\s+)?TEST\s+AFTER\s+", condition, re.I)
                if m:
                    attrs["test_after"] = True
                    condition = condition[m.end():]
                condition = re.sub(r"^UNTIL\s+", "", condition, flags=re.I)
                attrs["condition"] = " ".join(condition.split())
            stmt["attributes"] = attrs
        for child in stmt.get("children") or []:
            adopt(child)

    for para in paragraphs:
        statements = para.get("statements") or []
        for stmt in statements:
            adopt(stmt)
        _stamp_ordinals(statements)
    return paragraphs


def load_program(path: str, copybooks: str | None = None) -> Program:
    """Load COBOL source, or a pre-parsed cobalt AST, into one shape."""
    model = DataModel()
    if path.endswith(".ast") or path.endswith(".json"):
        with open(path, "r", errors="replace") as fh:
            raw = json.load(fh)
        program = Program(raw.get("program_id", os.path.basename(path)),
                          _adopt_ast(raw["paragraphs"]), model, path)
        sibling = re.sub(r"\.(cbl\.)?ast$", "", path, flags=re.I)
        for candidate in (sibling, sibling + ".cbl", sibling + ".CBL"):
            if os.path.isfile(candidate) and not candidate.endswith(".ast"):
                model.merge(parse_data_division(candidate))
                program.source_path = candidate
                break
    else:
        lines = read_lines(path)
        model = parse_data_division(path)
        program = Program(os.path.splitext(os.path.basename(path))[0],
                          parse_procedure(
                              expand_copies(lines, find_copybooks(path))),
                          model, path)
    directories = find_copybooks(program.source_path or path)
    if copybooks and os.path.isdir(copybooks):
        directories = [copybooks] + directories

    wanted = copy_members(program.source_path or path)
    loaded = []
    for member in wanted:
        resolved = resolve_member(member, directories)
        if resolved:
            model.merge(parse_data_division(resolved))
            loaded.append(member)
    if not wanted:
        # No COPY statements to go on - the AST path, or a program that
        # declares everything inline. Fall back to the directory.
        for directory in directories:
            for entry in sorted(os.listdir(directory)):
                full = os.path.join(directory, entry)
                if os.path.isfile(full):
                    model.merge(parse_data_division(full))
    model.copybooks = loaded
    program.model = model
    return program
