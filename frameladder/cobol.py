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
_VALUE_IN = re.compile(r"\bVALUE\s+(?:IS\s+)?('[^']*'|\"[^\"]*\"|[A-Z0-9+-]+)", re.I)
_OCCURS = re.compile(r"\bOCCURS\s+(\d+)", re.I)
_LEVEL88 = re.compile(r"^\s*88\s+([A-Z0-9][A-Z0-9-]*)\s+VALUES?\s+(?:ARE\s+|IS\s+)?(.*)$", re.I)


@dataclass
class DataModel:
    """Record layout: what contains what, and how wide each field is."""
    pic: dict = field(default_factory=dict)
    initial: dict = field(default_factory=dict)
    occurs: dict = field(default_factory=dict)
    children: dict = field(default_factory=dict)     # group -> all descendants
    parent: dict = field(default_factory=dict)
    declared: set = field(default_factory=set)
    condition_names: dict = field(default_factory=dict)   # 88 name -> (parent, values)

    def descendants(self, group: str) -> list[str]:
        return self.children.get(group.upper(), [])

    def merge(self, other: "DataModel") -> "DataModel":
        self.pic.update(other.pic)
        self.initial.update(other.initial)
        self.occurs.update(other.occurs)
        self.parent.update(other.parent)
        self.declared |= other.declared
        self.condition_names.update(other.condition_names)
        for group, kids in other.children.items():
            self.children.setdefault(group, []).extend(kids)
        return self


def parse_data_division(path: str) -> DataModel:
    model = DataModel()
    stack: list[tuple[int, str]] = []
    buffer = ""
    in_procedure = False

    for line in read_lines(path):
        if re.search(r"\bPROCEDURE\s+DIVISION\b", line.text, re.I):
            in_procedure = True
        if in_procedure:
            break
        buffer += " " + line.text.strip()
        if "." not in line.text:
            continue
        for chunk in buffer.split("."):
            if not chunk.strip():
                continue
            m88 = _LEVEL88.match(chunk)
            if m88 and stack:
                values = [v.strip() for v in re.split(r"[,\s]+(?:THRU|THROUGH)?\s*",
                                                      m88.group(2)) if v.strip()]
                model.condition_names[m88.group(1).upper()] = (stack[-1][1], values)
                continue
            m = _DECL.match(chunk)
            if not m:
                continue
            level, name, rest = int(m.group(1)), m.group(2).upper(), m.group(3)
            if level in (66, 88):
                continue
            while stack and stack[-1][0] >= level:
                stack.pop()
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
                model.initial[name] = v.group(1).strip("'\"")
            o = _OCCURS.search(rest)
            if o:
                model.occurs[name] = int(o.group(1))
            stack.append((level, name))
        buffer = ""
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


_PARA_HEADER = re.compile(r"^([A-Z0-9][A-Z0-9-]*)\.\s*$", re.I)
_SECTION = re.compile(r"^([A-Z0-9][A-Z0-9-]*)\s+SECTION\.\s*$", re.I)


def _procedure_lines(lines: list[Line]) -> list[Line]:
    for i, line in enumerate(lines):
        if re.search(r"\bPROCEDURE\s+DIVISION\b", line.text, re.I):
            rest = lines[i:]
            # The DIVISION header itself may carry a USING clause and a period.
            while rest and "." not in rest[0].text:
                rest = rest[1:]
            return rest[1:]
    return []


def split_paragraphs(lines: list[Line]) -> list[tuple[str, list[Line]]]:
    """Area-A labels start paragraphs; everything after one belongs to it."""
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
        if current_name is not None:
            current.append(line)
    if current_name is not None:
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

    def peek(self) -> str:
        return self.t[self.i].word.upper() if self.i < len(self.t) else ""

    def done(self) -> bool:
        return self.i >= len(self.t)

    def take_until_boundary(self) -> list[Token]:
        start = self.i
        while not self.done() and self.peek() not in _BOUNDARY:
            self.i += 1
        return self.t[start:self.i]

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
        if word == "IF":
            return self.if_statement()
        if word == "EVALUATE":
            return self.evaluate_statement()
        if word == "PERFORM":
            return self.perform_statement()
        if word == "GO":
            return self.go_statement()
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
        return {"type": "EVALUATE",
                "text": "EVALUATE " + " ".join(t.word for t in subject),
                "line_start": head.line, "line_end": head.line,
                "attributes": {"subject": " ".join(t.word for t in subject)},
                "children": arms}

    def perform_statement(self) -> dict:
        head = self.t[self.i]
        self.i += 1
        words = self.take_until_boundary()
        upper = [w.word.upper() for w in words]
        text = "PERFORM " + " ".join(w.word for w in words)

        # PERFORM <name> [THRU <name>] - a call, unless a loop clause follows.
        if words and upper[0] not in ("UNTIL", "VARYING", "WITH", "TEST") \
                and not re.match(r"^\d+$", upper[0]):
            target = words[0].word.upper()
            attrs: dict[str, Any] = {"target": target}
            if "THRU" in upper or "THROUGH" in upper:
                k = upper.index("THRU") if "THRU" in upper else upper.index("THROUGH")
                if k + 1 < len(words):
                    attrs["target"] = "%s THRU %s" % (target, words[k + 1].word.upper())
            rest = " ".join(w.word for w in words[1:])
            m = re.search(r"\bUNTIL\b(.*)", rest, re.I)
            if m:
                attrs["condition"] = m.group(1).strip()
                body = self.statements({"END-PERFORM", "."})
                if self.peek() == "END-PERFORM":
                    self.i += 1
                return {"type": "PERFORM", "text": text, "line_start": head.line,
                        "line_end": head.line, "attributes": attrs,
                        "children": body}
            return {"type": "PERFORM", "text": text, "line_start": head.line,
                    "line_end": head.line, "attributes": attrs, "children": []}

        # Inline PERFORM: UNTIL / VARYING / n TIMES.
        attrs = {}
        joined = " ".join(w.word for w in words)
        if upper and upper[0] == "VARYING":
            attrs["varying"] = joined
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

    def go_statement(self) -> dict:
        head = self.t[self.i]
        self.i += 1
        if self.peek() == "TO":
            self.i += 1
        words = self.take_until_boundary()
        target = words[0].word.upper() if words else ""
        depending = bool(re.search(r"\bDEPENDING\b",
                                   " ".join(w.word for w in words), re.I))
        return {"type": "GO_TO",
                "text": "GO TO " + " ".join(w.word for w in words),
                "line_start": head.line, "line_end": head.line,
                "attributes": {"target": target, "depending": depending},
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

        words = self.take_until_boundary()
        text = verb + (" " + " ".join(w.word for w in words) if words else "")
        attrs: dict[str, Any] = {}
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
            m = re.match(r"([A-Z0-9-]+)\s+TO\s+(\S+)", joined, re.I)
            if m:
                attrs["name"], attrs["value"] = m.group(1).upper(), m.group(2).upper()
        kind = {"GOBACK": "GOBACK", "STOP": "STOP", "EXIT": "EXIT"}.get(verb, verb)
        return {"type": kind, "text": text, "line_start": head.line,
                "line_end": words[-1].line if words else head.line,
                "attributes": attrs, "children": []}


def parse_procedure(lines: list[Line]) -> list[dict]:
    paragraphs = []
    for name, body in split_paragraphs(_procedure_lines(lines)):
        parser = _Parser(tokenize(body))
        statements = parser.statements(set())
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


def load_program(path: str, copybooks: str | None = None) -> Program:
    """Load COBOL source, or a pre-parsed cobalt AST, into one shape."""
    model = DataModel()
    if path.endswith(".ast") or path.endswith(".json"):
        with open(path, "r", errors="replace") as fh:
            raw = json.load(fh)
        program = Program(raw.get("program_id", os.path.basename(path)),
                          raw["paragraphs"], model, path)
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
                          parse_procedure(lines), model, path)
    if copybooks and os.path.isdir(copybooks):
        for entry in sorted(os.listdir(copybooks)):
            model.merge(parse_data_division(os.path.join(copybooks, entry)))
    program.model = model
    return program
