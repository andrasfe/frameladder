"""Where every value comes from, and which knob sets it."""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .conditions import condition_atoms
from .graph import walk_guarded
from .ir import Producer, base_name, move_targets, norm, parse_term

STUB_KINDS = {"CALL", "READ", "OPEN", "CLOSE", "WRITE", "REWRITE", "START",
              "DELETE", "EXEC", "RETURN", "ACCEPT"}
_ARITH = {"ADD", "SUBTRACT", "COMPUTE", "MULTIPLY", "DIVIDE"}


@dataclass
class Writer:
    para: str
    line: int
    kind: str                      # MOVE | STUB | SET | ADD | ...
    source: str = ""
    op_key: str = ""
    guards: tuple = ()
    literals: dict = field(default_factory=dict)

    @property
    def conditional(self) -> bool:
        return bool(self.guards)


def op_key(text: str) -> str:
    # Either quote character is legal, and matching only the apostrophe sent
    # `CALL "CEEDAYS"` to the catch-all EXTERNAL queue - where it shares its
    # outcomes with every other unrecognised operation in the program.
    m = re.search(r"CALL\s+['\"]([^'\"]+)['\"]", text, re.I)
    if m:
        return "CALL:%s" % m.group(1).upper()
    # A dynamic call names a variable holding the program name. Which program
    # that is cannot be read off this statement, but the *site* is still an
    # identity, and one queue per program-name variable is much closer than
    # one queue for the whole program: date conversion, validation, lookup and
    # abend all take their outcomes from the same list otherwise, in call
    # order, and the first wrong answer poisons every later one.
    m = re.search(r"\bCALL\s+([A-Z][A-Z0-9-]*)", text, re.I)
    if m and m.group(1).upper() not in ("USING", "BY", "RETURNING"):
        return "CALL:@%s" % m.group(1).upper()
    m = re.search(r"\bEXEC\s+(CICS|SQL|DLI)\b\s*(\w+)?", text, re.I)
    if m:
        return "EXEC:%s%s" % (m.group(1).upper(),
                              ":" + m.group(2).upper() if m.group(2) else "")
    # `OPEN INPUT ACCTFILE-FILE` names the mode before the file, so the
    # naive "word after the verb" is the mode and every OPEN collapses to
    # one operation called OPEN:INPUT. The mode also decides the outcome -
    # opening a missing file for input fails where opening it for output
    # creates it - so it belongs in the operation's identity.
    m = re.search(r"\b(READ|WRITE|OPEN|CLOSE|REWRITE|START|DELETE)\s+"
                  r"((?:INPUT|OUTPUT|I-O|EXTEND)\s+)?([A-Z0-9-]+)", text, re.I)
    if m:
        verb = m.group(1).upper()
        mode = (m.group(2) or "").strip().upper()
        return "%s%s:%s" % (verb, "-" + mode if mode else "", m.group(3).upper())
    return "EXTERNAL"


# CICS and SQL write their operands in parentheses, not after whitespace, so
# a "word after the keyword" reader finds nothing - or worse, falls through to
# the file-I/O reader and mistakes the keyword DATASET for a variable.
_EXEC_CLAUSE = re.compile(r"\b([A-Z][A-Z0-9]*)\s*\(\s*([^)]*?)\s*\)", re.I)

# What a CICS command hands *back*. RESP and RESP2 are CICS's FILE STATUS:
# the same "how did the operation go" channel that makes file I/O planable.
_CICS_OUTPUTS = {"INTO", "RESP", "RESP2", "LENGTH", "FLENGTH", "COMMAREA",
                 "SET", "RIDFLD", "COUNTER", "ITEM"}
# What a command *selects* - which file, which map, which program. These tell
# two invocations of one verb apart, exactly as a DD name does for a CALL.
_CICS_SELECTORS = {"DATASET", "FILE", "PROGRAM", "MAPSET", "MAP", "QUEUE",
                   "TRANSID", "SYSID", "TABLE"}
_HOST_VAR = re.compile(r":\s*([A-Z][A-Z0-9-]*)", re.I)

# Where a USING list stops. RETURNING/GIVING is an output but not a parameter,
# and the handlers are statements rather than operands.
_USING_END = re.compile(r"\b(RETURNING|GIVING|ON\s+EXCEPTION|NOT\s+ON\s+EXCEPTION"
                        r"|ON\s+OVERFLOW|END-CALL)\b", re.I)
# BY CONTENT and BY VALUE hand the callee a copy, so it cannot write back
# through them. BY REFERENCE - the default - it can.
_BY_MODE = re.compile(r"\bBY\s+(REFERENCE|CONTENT|VALUE)\b", re.I)
_OPERAND = re.compile(r"[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*", re.I)
_NOT_OPERAND = {"BY", "REFERENCE", "CONTENT", "VALUE", "ADDRESS", "OF",
                "LENGTH", "OMITTED", "USING", "CALL"}


def call_outputs(flat: str) -> list[str]:
    """Every operand a CALL passes BY REFERENCE.

    COBOL passes BY REFERENCE unless told otherwise, so *every* operand in
    the USING list is somewhere the callee can write. Reading only the first
    name after ``USING`` makes the ones that matter invisible: MQ hands its
    completion and reason codes back in the fifth and sixth operands, and
    DL/I hands its status back inside the PCB in the second. Every arm those
    gate is then unreachable, not because the ladder could not lift the
    obligation but because nothing was recorded as producing the value.
    """
    m = re.search(r"\bUSING\b(.*)$", flat, re.I | re.S)
    if not m:
        return []
    tail = m.group(1)
    stop = _USING_END.search(tail)
    if stop:
        tail = tail[: stop.start()]
    out, mode = [], "REFERENCE"
    pos = 0
    for token in _OPERAND.finditer(tail):
        word = token.group(0).upper()
        by = _BY_MODE.match(tail, token.start()) if word == "BY" else None
        if by:
            mode = by.group(1).upper()
            continue
        if word in _NOT_OPERAND or tail[max(0, token.start() - 1)] in "'\"":
            continue
        if mode == "REFERENCE":
            out.append(word)
        pos = token.end()
    return list(dict.fromkeys(out))


def exec_operands(text: str) -> dict:
    """Clause name -> operand, for an EXEC block."""
    return {m.group(1).upper(): m.group(2).strip()
            for m in _EXEC_CLAUSE.finditer(norm(text))}


def stub_outputs(text: str) -> list[str]:
    flat = norm(text)
    if re.search(r"\bEXEC\s+(CICS|SQL|DLI)\b", flat, re.I):
        out: list[str] = []
        if re.search(r"\bEXEC\s+SQL\b", flat, re.I):
            # Every SQL statement sets SQLCODE whether it mentions it or not;
            # it is the DB2 equivalent of a file status and the thing every
            # generated error path actually tests.
            out.append("SQLCODE")
            m = re.search(r"\bINTO\b(.*?)(\bFROM\b|$)", flat, re.I | re.S)
            if m:
                out.extend(h.group(1).upper() for h in _HOST_VAR.finditer(m.group(1)))
        for clause, operand in exec_operands(flat).items():
            if clause in _CICS_OUTPUTS:
                out.extend(n.upper() for n in re.findall(r"[A-Z][A-Z0-9-]*",
                                                         operand, re.I))
        return list(dict.fromkeys(out))

    out = call_outputs(flat)
    out.extend(m.group(1).upper() for m in
               re.finditer(r"\bINTO\s+([A-Z0-9-]+)", flat, re.I))
    out = list(dict.fromkeys(out))
    if not out:
        out = [m.group(2).upper() for m in
               re.finditer(r"\b(READ|OPEN|CLOSE|RETURN)\s+([A-Z0-9-]+)", flat, re.I)]
    return out


def exec_selectors(text: str) -> dict:
    """Which resource an EXEC command names, as discriminators."""
    out = {}
    for clause, operand in exec_operands(text).items():
        if clause in _CICS_SELECTORS and operand:
            out[clause] = operand.strip("'\"").upper()
    return out


def tokens_of(name: str) -> set:
    return {t for t in name.upper().split("-")
            if t not in ("RECORD", "REC", "AREA", "DATA")}


def associate_field(name: str, candidates) -> str | None:
    """Guess which record an undeclared field belongs to.

    Needed whenever the copybook defining a record is not shipped - common,
    and fatal to provenance if unhandled.  Scored on shared name tokens,
    with a bonus for a matching first token, which is how COBOL shops
    actually prefix record fields.  Every producer built this way is
    marked ``inferred`` so it can be checked rather than trusted.
    """
    want, best, best_score = tokens_of(name), None, 0
    head = name.upper().split("-")[0]
    for cand in candidates:
        score = len(want & tokens_of(cand)) + (2 if cand.upper().startswith(head + "-") else 0)
        if score > best_score:
            best, best_score = cand, score
    return best if best_score >= 2 else None


_CLASS_FILL = {"NUMERIC": "0", "ALPHABETIC": "A", "ALPHABETIC-UPPER": "A",
               "ALPHABETIC-LOWER": "a", "POSITIVE": "1", "NEGATIVE": "1",
               "ZERO": "0"}


def _slice_text(value, length: int, violate: bool = False) -> str:
    """The bytes one slice constraint asks for, or bytes that break it."""
    if isinstance(value, str) and value.upper() in _CLASS_FILL:
        fill = _CLASS_FILL[value.upper()]
        return ("*" if fill.isdigit() else "9") * length if violate \
            else fill * length
    text = (value if isinstance(value, str)
            else str(value)).ljust(length)[:length]
    if not violate:
        return text
    # Anything that is not what the program asked for. A character it can
    # never have been compared against is the safest choice.
    return "".join("#" if c != "#" else "~" for c in text)


class Provenance:
    def __init__(self, program, order: dict | None = None):
        self.program = program
        self.model = program.model
        self.order = order or {}
        self.writers: dict = {}
        self.stub_fills: dict = {}      # record group <- stub payload
        self.call_literals: dict = {}   # op_key -> literals set before each call
        self.selectors: dict = {}       # op_key -> discriminating fields
        self.literals: dict = {}        # var -> literals it is compared against
        self.slices: dict = {}          # var -> (start, length, value) facts
        self.payloads: set = set()
        self.operations: dict = {}      # paragraph -> external ops performed
        self.spellings: dict = {}       # base name -> every way it is written
        self._index()
        self._find_selectors()
        self._harvest_literals()

    # -- indexing ----------------------------------------------------------
    def _add(self, var: str, writer: Writer):
        upper = var.upper()
        self.writers.setdefault(upper, []).append(writer)
        base = base_name(upper)
        if base != upper:
            self.spellings.setdefault(base, []).append(upper)

    def writes_to(self, var: str) -> list:
        """Every write that lands on this field, however it is spelled.

        ``MOVE X TO A OF R`` and ``EXEC CICS RECEIVE INTO(R)`` write the same
        bytes, but they arrive here under two keys - the qualified reference
        and the declared name the record's descendants are listed under. Kept
        apart, the reaching-definition walk sees only whichever half the
        reader happened to spell, so a field the program fills at one site and
        reads at another looks unwritten from one side and unread from the
        other.

        The runtime store already settled this question the other way:
        ``Layout.slot_for`` falls back to the base name, so the two spellings
        are one cell during execution. Provenance disagreeing with execution
        about which writes exist is the same defect the byte store fixed for
        values, one layer up - and it is what made a screen field's producer
        come back as the file READ six statements later instead of the
        terminal RECEIVE that actually fills it.
        """
        upper = (var or "").upper()
        out = list(self.writers.get(upper, []))
        base = base_name(upper)
        aliases = ([base] if base != upper else []) + \
            [s for s in self.spellings.get(base, []) if s != upper]
        for alias in aliases:
            for w in self.writers.get(alias, []):
                if w not in out:
                    out.append(w)
        return out

    def _index(self):
        for para in self.program.paragraphs:
            def visit(stmt, pname, guards, induction, literals):
                kind = stmt.get("type", "")
                attrs = stmt.get("attributes", {})
                line = stmt.get("line_start", 0)
                text = norm(stmt.get("text", ""))

                if kind == "MOVE":
                    source = attrs.get("source", "")
                    src = parse_term(source)
                    for base in move_targets(attrs.get("targets", "")):
                        w = Writer(pname, line, "MOVE", source=source,
                                   guards=tuple(guards), literals=dict(literals))
                        self._add(base, w)
                        for child in self.model.descendants(base):
                            self._add(child, w)
                        if src.kind == "var" and self._is_payload(src.name):
                            self.stub_fills[base] = Writer(
                                pname, line, "FILL", source=src.name,
                                guards=tuple(guards), literals=dict(literals))

                elif kind == "SET":
                    name = attrs.get("name")
                    if name:
                        # `SET FLG-ACCT-VALID TO TRUE` writes the *parent*
                        # field, not a field called FLG-ACCT-VALID - there is
                        # no such storage. Recorded against the condition-name
                        # the write is invisible: nothing appears to write the
                        # parent, so the ladder concludes the field is never
                        # assigned and emits a false infeasibility proof for
                        # any obligation on it. The interpreter already
                        # resolves 88s to the parent, so leaving this alone
                        # also puts provenance and execution at odds about
                        # the same program.
                        entry = self.model.condition_names.get(name.upper())
                        target, value = name, attrs.get("value", "")
                        if entry:
                            parent, values = entry
                            target = parent
                            # TO TRUE means "any of its values"; the first is
                            # the conventional witness. TO FALSE names no
                            # value at all, so the source stays empty and the
                            # writer records only that the field is touched.
                            if norm(value).upper() != "FALSE" and values:
                                value = values[0]
                            else:
                                value = ""
                        self._add(target, Writer(pname, line, "SET",
                                                 source=value,
                                                 guards=tuple(guards)))

                elif kind in STUB_KINDS:
                    key = op_key(text)
                    # The resource a CICS command names is what tells two
                    # invocations of one verb apart - the same role a DD name
                    # plays for a CALL - so it belongs with the discriminators.
                    site_literals = dict(literals)
                    site_literals.update(exec_selectors(text))
                    self.call_literals.setdefault(key, []).append(site_literals)
                    # An operation counts as external whether or not it hands
                    # anything back: CLOSE, SYNCPOINT and a CALL with no USING
                    # all touch the outside world, and a test still has to
                    # account for them.
                    self.operations.setdefault(pname, set()).add(key)
                    outputs = list(stub_outputs(text))
                    for f, status in self.model.file_status.items():
                        if re.search(r"\b%s\b" % re.escape(f), text, re.I):
                            outputs.append(status)
                    if kind in ("READ", "RETURN"):
                        for f, records in self.model.fd_records.items():
                            if re.search(r"\b%s\b" % re.escape(f), text, re.I):
                                outputs.extend(records)
                    for var in outputs:
                        w = Writer(pname, line, "STUB", op_key=key,
                                   guards=tuple(guards), literals=site_literals)
                        self._add(var, w)
                        self.payloads.add(var)
                        # A record filled straight by the operation - READ ...
                        # INTO REC - is as much a place for undeclared fields
                        # to come from as one filled by a later MOVE. Register
                        # it so a field whose copybook is missing can still be
                        # traced back to the read that produced it.
                        self.stub_fills.setdefault(var, Writer(
                            pname, line, "FILL", source=var, op_key=key,
                            guards=tuple(guards), literals=dict(literals)))
                        for child in self.model.descendants(var):
                            self._add(child, w)
                            self.payloads.add(child)

                elif kind in _ARITH:
                    for groups in re.findall(
                            r"\bTO\s+([A-Z0-9-]+)|\bGIVING\s+([A-Z0-9-]+)"
                            r"|COMPUTE\s+([A-Z0-9-]+)", text, re.I):
                        for g in groups:
                            if g:
                                self._add(g.upper(), Writer(pname, line, kind,
                                                            source=text,
                                                            guards=tuple(guards)))
            walk_guarded(para, visit)

    def _is_payload(self, var: str) -> bool:
        return any(w.kind == "STUB" for w in self.writers.get(var.upper(), []))

    def _find_selectors(self):
        """A field discriminates a stub's invocations when it is set to
        *different* literals at different call sites.  A field set to the
        same value everywhere - blanking the output area, zeroing a return
        code - tells two calls apart not at all."""
        for key, sites in self.call_literals.items():
            values: dict = {}
            for site in sites:
                for k, v in site.items():
                    values.setdefault(k, set()).add(v)
            self.selectors[key] = {k for k, vs in values.items()
                                   if len(vs) > 1 or len(sites) == 1}

    def _harvest_literals(self):
        from .ir import norm as _norm

        def take(text):
            """Every literal a condition compares a field against."""
            if not text:
                return
            for alts in condition_atoms(text):
                for atom in alts:
                    # `IS NUMERIC` says what shape the value has, not what it
                    # is. Filing "NUMERIC" as a candidate value hands the
                    # sampler a string that satisfies nothing and crowds out
                    # the literals that would.
                    if atom.op in ("IS", "IS-NOT"):
                        if atom.lhs.kind == "var" and atom.lhs.refmod:
                            self._record_slice(atom.lhs, atom.rhs.value)
                        elif atom.lhs.kind == "var":
                            self._class_candidates(atom.lhs.name,
                                                   str(atom.rhs.value))
                        continue
                    # `FUNCTION LENGTH(FUNCTION TRIM(X)) = 0` says X is blank,
                    # and `FUNCTION TEST-NUMVAL-C(X) = 0` says it is a number,
                    # but neither puts a literal anywhere the harvest can see
                    # it. The field is left with no candidate that answers the
                    # question the program is asking about it.
                    for side in (atom.lhs, atom.rhs):
                        if side.kind == "var" and side.func and side.name:
                            self._function_candidates(side)
                    for a, b in ((atom.lhs, atom.rhs), (atom.rhs, atom.lhs)):
                        if a.kind == "var" and b.kind == "const":
                            self.literals.setdefault(a.name, set()).add(b.value)
                            if a.refmod:
                                self._record_slice(a, b.value)

        def scan(stmt):
            attrs = stmt.get("attributes", {})
            for text in (attrs.get("condition"), attrs.get("varying"),
                         attrs.get("until")):
                take(text)
            if stmt.get("type") == "EVALUATE":
                subject = parse_term(attrs.get("subject", ""))
                # `EVALUATE TRUE / WHEN <relation>` is how COBOL writes a
                # chain of ifs, and the arm is a whole condition rather than a
                # value to match the subject against. Filing its literals
                # under a field called TRUE leaves the fields the arms
                # actually test with no candidate values at all - which is
                # most of the validation logic in a screen program.
                on_truth = _norm(attrs.get("subject", "")).upper() in ("TRUE",
                                                                       "FALSE")
                for child in stmt.get("children") or []:
                    if child.get("type") != "WHEN":
                        continue
                    raw = child.get("attributes", {}).get("value", "")
                    if _norm(raw).upper() in ("OTHER", "ANY"):
                        continue
                    if on_truth:
                        take(raw)
                    elif subject.kind == "var":
                        val = parse_term(raw)
                        if val.kind == "const":
                            self.literals.setdefault(subject.name,
                                                     set()).add(val.value)
                        else:
                            take("%s = %s" % (attrs.get("subject", ""), raw))
            for child in stmt.get("children") or []:
                scan(child)

        for para in self.program.paragraphs:
            for stmt in para.get("statements", []):
                scan(stmt)
        for name, (parent, values) in self.model.condition_names.items():
            for v in values:
                term = parse_term(v)
                if term.kind == "const":
                    self.literals.setdefault(parent.upper(), set()).add(term.value)
        # Offering `FUNCTION CURRENT-DATE` to the sampler as well was tried
        # and measured at -2 directions across the corpus: one more name in
        # the pool dilutes every other draw more than the December date buys.
        # The slot stays settable by the harness; it is just not sampled.
        self._compose_sliced()

    def _field_width(self, name: str) -> int:
        from .layout import byte_length
        pic = self.model.pic_of(name)
        if not pic:
            return 0
        try:
            return byte_length(pic, self.model.usage_of(name),
                               self.model.look(self.model.sign, name, ""))
        except Exception:                                        # noqa: BLE001
            return 0

    def _class_candidates(self, name: str, klass: str) -> None:
        """A class condition names a shape, so offer a value of that shape.

        `IF WS-X IS NUMERIC` compares against nothing, so nothing about it
        reaches the literal table and a sampler drawing from literals can
        only ever take the direction the field's default happens to give.
        Both a member and a non-member of the class make both directions
        reachable.
        """
        width = self._field_width(name) or 1
        if width > 64:
            width = 64
        klass = (klass or "").upper()
        pool = self.literals.setdefault(name, set())
        if klass == "NUMERIC":
            pool.update({"0" * width, "*" * width, " " * width})
        elif klass.startswith("ALPHABETIC"):
            lower = klass.endswith("LOWER")
            pool.update({("a" if lower else "A") * width, "0" * width})
        elif klass in ("POSITIVE", "NEGATIVE", "ZERO"):
            pool.update({0, 1, -1})

    def _function_candidates(self, term) -> None:
        """Values that make an intrinsic go each way, for its argument."""
        width = self._field_width(term.name) or 1
        if width > 64:
            width = 64
        pool = self.literals.setdefault(term.name, set())
        if term.func in ("TRIM", "LENGTH", "UPPER-CASE", "LOWER-CASE"):
            pool.update({" " * width, "A" * width})
        elif term.func in ("NUMVAL", "NUMVAL-C", "TEST-NUMVAL",
                           "TEST-NUMVAL-C"):
            pool.update({"0" * width, "*" * width, " " * width})
        for arg in term.args:
            if arg.kind == "var" and arg.func:
                self._function_candidates(arg)

    def _record_slice(self, term, value) -> None:
        """Remember what the program says about one slice of a field."""
        try:
            start = int(str(term.refmod[0]).strip())
            length = int(str(term.refmod[1]).strip()) if term.refmod[1] else 1
        except (TypeError, ValueError):
            return
        if start < 1 or length < 1 or start + length > 256:
            return
        self.slices.setdefault(term.name, []).append((start, length, value))

    def _compose_sliced(self) -> None:
        """Build whole-field candidates out of what the slices require.

        A field the program only ever inspects a piece at a time - a date as
        ``(1:4)`` numeric, ``(5:1) = '-'``, ``(6:2)`` numeric - has no literal
        of its own anywhere in the source, so a sampler drawing from observed
        literals can never produce one that gets past the format check. The
        pieces, laid at the offsets the program names them at, compose exactly
        the value it is asking for.
        """
        from .layout import byte_length
        for name, pieces in self.slices.items():
            width = 0
            pic = self.model.pic_of(name)
            if pic:
                try:
                    width = byte_length(pic, self.model.usage_of(name),
                                        self.model.look(self.model.sign, name, ""))
                except Exception:                                # noqa: BLE001
                    width = 0
            width = max([width] + [s + n - 1 for s, n, _ in pieces])
            if width > 256:
                continue
            unique = list(dict.fromkeys(pieces))
            # The satisfying composition, then one variant per slice that
            # breaks *only* that slice. A validation paragraph is a chain of
            # arms, each testing one piece, and an arm is only evaluated when
            # every earlier one failed - so reaching the k-th arm's true
            # direction needs a value that is right everywhere before k and
            # wrong at k. n+1 candidates is exactly that ladder.
            for broken in [None] + list(range(len(unique))):
                for filler in ("0", " "):
                    body = [filler] * width
                    for i, (start, length, value) in enumerate(unique):
                        text = _slice_text(value, length, violate=(i == broken))
                        body[start - 1:start - 1 + length] = list(text[:length])
                    self.literals.setdefault(name, set()).add("".join(body))
                    if broken is None:
                        break

    # -- lookups -----------------------------------------------------------
    def _rank(self, para: str) -> int:
        return self.order.get(para, 10 ** 6)

    def visible(self, var: str, at: tuple | None) -> list:
        # A qualified reference names a declaration recorded under its base
        # name, so the *lookup* has to see through the qualifier even though
        # the identity keeps it - the same split `model.look` already makes.
        # Merging rather than falling back matters: a map field the program
        # also MOVEs to has writers under both spellings, and taking only the
        # qualified half attributed it to whichever stub filled the MOVE's
        # source, so a screen field came back as a field of a file READ
        # rather than of the terminal RECEIVE that actually fills it, the
        # plan bound an outcome for the wrong operation, and the field the
        # condition tests was never set by anything.
        writers = self.writes_to(var)
        if not at or not self.order:
            return writers
        para, line = at
        here = self._rank(para)

        def key(w: Writer):
            # The reaching definition is the *latest* write before the read,
            # so among preceding writes prefer the nearest: same paragraph
            # first, then the highest-ranked earlier paragraph.
            if w.para == para and w.line < line:
                return (0, w.conditional, -w.line)
            if self._rank(w.para) < here:
                return (1, w.conditional, -self._rank(w.para))
            return (2, w.conditional, self._rank(w.para))

        return sorted(writers, key=key)

    def discriminators(self, literals: dict, key: str = "") -> dict:
        varying = self.selectors.get(key)
        if varying is None:
            return dict(literals)
        return {k: v for k, v in literals.items() if k in varying}

    def producer(self, var: str, at: tuple | None = None, depth: int = 0,
                 seen: frozenset = frozenset(), acceptable=None) -> Producer:
        """Walk a variable back to whatever the harness can actually set.

        A MOVE is a rename, so an obligation transfers unchanged to its
        source - tier-0 lifting in one line.  Every candidate write is
        tried, not just the first, because a single static order is only
        ever a guess about which one reaches the read.
        """
        var = var.upper()
        if depth > 16 or var in seen:
            return Producer("unknown", var=var)
        writers = self.visible(var, at)

        if writers and all(w.kind == "MOVE"
                           and parse_term(w.source).kind == "var"
                           and parse_term(w.source).name in seen for w in writers):
            # Every remaining write copies from something already on the walk:
            # a mutual copy pair, e.g. a table cell filled from a record field
            # in one paragraph and read back into it in another. Neither is
            # the origin; the record fill upstream is.
            writers = []

        if not writers:
            return self._from_record(var, depth, seen)

        # If every producer is one the harness cannot deliver, the first is
        # still the answer. Preferring a deliverable producer is choosing
        # between alternatives the program left open; returning *none* would
        # let a harness limitation decide what is required, which AGENTS.md
        # forbids in as many words. Measured: without this, one program lost
        # 11 of 12 solved plans while another gained 28.
        refused_first = None
        for index, w in enumerate(writers):
            if w.kind == "MOVE":
                src = parse_term(w.source)
                if src.kind == "const":
                    if len(writers) == 1:
                        return Producer("literal", var=var, site=w.para,
                                        value=src.value, trace=(var,))
                    # The *reaching definition*, when it is unconditional, is
                    # the value at this read - nothing can steer around it, so
                    # walking past it to an earlier write binds a value the
                    # program has already thrown away.
                    #
                    # `visible(var, at)` puts the nearest preceding write
                    # first, and skipping a constant whenever the field has
                    # more than one writer ignored that ordering entirely. Two
                    # unconditional MOVEs in a caller - one from an input, then
                    # one from a literal - and the plan bound the input,
                    # reported no open obligation, and never reached the
                    # target. Bound, unreported, and wrong.
                    #
                    # Scoped to a write in the *same paragraph*, before the
                    # read. Across paragraphs "nearest" is a static-order
                    # guess about which write reaches, and treating a guess as
                    # a hard literal calls solvable routes impossible - it
                    # cost 23 witnesses when tried. A *conditional* write also
                    # falls through: that one can be steered around, which is
                    # `blocking_writes`' job.
                    if (at and index == 0 and not w.conditional
                            and w.para == at[0] and w.line < at[1]):
                        return Producer("literal", var=var, site=w.para,
                                        value=src.value, trace=(var,))
                    continue
                up = self.producer(src.name, (w.para, w.line), depth + 1,
                                   seen | {var}, acceptable=acceptable)
                if up.kind in ("stub", "literal", "input"):
                    # Walking up to a *group* - a commarea, a whole record -
                    # loses which field was being asked about, and every
                    # field then shares one slot and collides with the rest.
                    # The field is what a harness sets, so keep its name.
                    upstream = up.var or src.name
                    if up.kind == "input" and self.model.descendants(upstream):
                        upstream = var
                    candidate = Producer(
                        up.kind, var=upstream,
                        site=up.site or w.para, op_key=up.op_key,
                        value=up.value,
                        discriminators=self.discriminators(
                            up.discriminators or w.literals, up.op_key),
                        trace=(var,) + tuple(up.trace),
                        inferred=up.inferred)
                    if acceptable is None or acceptable(candidate):
                        return candidate
                    refused_first = refused_first or candidate
                    continue
            if w.kind == "STUB":
                candidate = Producer("stub", var=var, site=w.para,
                                     op_key=w.op_key,
                                     discriminators=self.discriminators(
                                         w.literals, w.op_key),
                                     trace=(var,))
                if acceptable is None or acceptable(candidate):
                    return candidate
                # The harness cannot deliver this one. A field written in more
                # than one place is a choice the *program* left open, so
                # walking on to the next writer picks between alternatives
                # rather than relaxing anything - the same licence route
                # ordering already has.
                refused_first = refused_first or candidate
                continue
        fallback = self._from_record(var, depth, seen)
        if fallback.kind == "stub":
            return fallback
        if refused_first is not None:
            return refused_first
        return Producer("unknown", var=var, site=writers[0].para)

    def _from_record(self, var: str, depth: int, seen: frozenset) -> Producer:
        if (self.model.knows(var) or self.model.knows(base_name(var))
                or not self.stub_fills):
            return Producer("input", var=var)
        group = associate_field(var, self.stub_fills)
        if not group:
            return Producer("input", var=var)
        fill = self.stub_fills[group]
        up = self.producer(fill.source, (fill.para, fill.line), depth + 1,
                           seen | {var})
        # The fill site is the authority on *which* invocation produced this
        # payload: the MOVE sits in the paragraph that made the call.
        return Producer("stub", var=var, site=fill.para,
                        op_key=up.op_key or "EXTERNAL",
                        discriminators=self.discriminators(
                            fill.literals or up.discriminators, up.op_key),
                        trace=(var, group, fill.source), inferred=True)

    def blocking_writes(self, var: str, op: str, value) -> list:
        """Conditional writes that would violate ``var op value`` if run."""
        from .ir import holds
        out = []
        for w in self.writes_to(var):
            if not w.conditional or w.kind != "MOVE":
                continue
            src = parse_term(w.source)
            if src.kind == "const" and not holds(src.value, op, value):
                out.append(w)
        return out

    def establishing_writes(self, var: str, op: str, value) -> list:
        """Conditional writes that would satisfy ``var op value`` if they ran.

        The mirror of :meth:`blocking_writes`. When an obligation cannot be
        met by the entry state because the program overwrites the field on
        the way, the field is not therefore hopeless - it is *produced*, and
        the obligation becomes: reach the write that produces it. That turns
        a dead end into a set of guards to satisfy, which is the same kind of
        problem the ladder already solves one level out.

        `SET <88> TO TRUE` counts here as well as MOVE, since after the
        attribution fix it carries the value it establishes.
        """
        from .ir import holds
        out = []
        for w in self.writes_to(var):
            if w.kind not in ("MOVE", "SET"):
                continue
            src = parse_term(w.source)
            if src.kind == "const" and holds(src.value, op, value):
                out.append(w)
        return out

    def frame_source(self, paragraph: str, span: int = 0) -> list:
        """The raw source of one paragraph - what an agent needs to read when
        the deterministic tiers give up on it."""
        para = self.program.paragraph(paragraph)
        if not para or not self.program.source_path:
            return []
        try:
            with open(self.program.source_path, "r", errors="replace") as fh:
                lines = fh.read().splitlines()
        except OSError:
            return []
        start = max(0, para.get("line_start", 1) - 1 - span)
        end = min(len(lines), para.get("line_end", start) + span)
        return [(i + 1, lines[i]) for i in range(start, end)]
