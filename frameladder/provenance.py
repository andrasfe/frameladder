"""Where every value comes from, and which knob sets it."""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .conditions import condition_atoms
from .graph import walk_guarded
from .ir import Producer, move_targets, norm, parse_term

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
    m = re.search(r"CALL\s+'([^']+)'", text, re.I)
    if m:
        return "CALL:%s" % m.group(1).upper()
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

    out = [m.group(1).upper() for m in
           re.finditer(r"\b(?:USING|INTO)\s+([A-Z0-9-]+)", flat, re.I)]
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
        self.payloads: set = set()
        self.operations: dict = {}      # paragraph -> external ops performed
        self._index()
        self._find_selectors()
        self._harvest_literals()

    # -- indexing ----------------------------------------------------------
    def _add(self, var: str, writer: Writer):
        self.writers.setdefault(var.upper(), []).append(writer)

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
                        self._add(name, Writer(pname, line, "SET",
                                               source=attrs.get("value", ""),
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
        def scan(stmt):
            attrs = stmt.get("attributes", {})
            for text in (attrs.get("condition"), attrs.get("varying"),
                         attrs.get("until")):
                if not text:
                    continue
                for alts in condition_atoms(text):
                    for atom in alts:
                        for a, b in ((atom.lhs, atom.rhs), (atom.rhs, atom.lhs)):
                            if a.kind == "var" and b.kind == "const":
                                self.literals.setdefault(a.name, set()).add(b.value)
            if stmt.get("type") == "EVALUATE":
                subject = parse_term(attrs.get("subject", ""))
                for child in stmt.get("children") or []:
                    if child.get("type") == "WHEN" and subject.kind == "var":
                        val = parse_term(child.get("attributes", {}).get("value", ""))
                        if val.kind == "const":
                            self.literals.setdefault(subject.name, set()).add(val.value)
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

    # -- lookups -----------------------------------------------------------
    def _rank(self, para: str) -> int:
        return self.order.get(para, 10 ** 6)

    def visible(self, var: str, at: tuple | None) -> list:
        writers = self.writers.get(var.upper(), [])
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
                 seen: frozenset = frozenset()) -> Producer:
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

        for w in writers:
            if w.kind == "MOVE":
                src = parse_term(w.source)
                if src.kind == "const":
                    if len(writers) == 1:
                        return Producer("literal", var=var, site=w.para,
                                        value=src.value, trace=(var,))
                    continue
                up = self.producer(src.name, (w.para, w.line), depth + 1,
                                   seen | {var})
                if up.kind in ("stub", "literal", "input"):
                    # Walking up to a *group* - a commarea, a whole record -
                    # loses which field was being asked about, and every
                    # field then shares one slot and collides with the rest.
                    # The field is what a harness sets, so keep its name.
                    upstream = up.var or src.name
                    if up.kind == "input" and self.model.descendants(upstream):
                        upstream = var
                    return Producer(up.kind, var=upstream,
                                    site=up.site or w.para, op_key=up.op_key,
                                    value=up.value,
                                    discriminators=self.discriminators(
                                        up.discriminators or w.literals, up.op_key),
                                    trace=(var,) + tuple(up.trace),
                                    inferred=up.inferred)
            if w.kind == "STUB":
                return Producer("stub", var=var, site=w.para, op_key=w.op_key,
                                discriminators=self.discriminators(w.literals,
                                                                   w.op_key),
                                trace=(var,))
        fallback = self._from_record(var, depth, seen)
        if fallback.kind == "stub":
            return fallback
        return Producer("unknown", var=var, site=writers[0].para)

    def _from_record(self, var: str, depth: int, seen: frozenset) -> Producer:
        if var in self.model.declared or not self.stub_fills:
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
        for w in self.writers.get(var.upper(), []):
            if not w.conditional or w.kind != "MOVE":
                continue
            src = parse_term(w.source)
            if src.kind == "const" and not holds(src.value, op, value):
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
