"""Physical record layout: where each field sits and how wide it really is.

A plan says what value a field should hold. A harness needs a *record* - the
bytes a file contains or a subprogram is handed - and getting from one to the
other needs the byte offset and length of every field, which is a question
about type rather than about logic.

That is why USAGE matters more here than anywhere else. ``PIC S9(4)`` is four
bytes as DISPLAY, three as COMP-3 and two as COMP, so a layout computed from
PIC alone puts every field after the first packed one at the wrong offset -
and a record that is wrong from byte nine onwards is worse than no record at
all, because it looks plausible.

Two things make the arithmetic non-obvious. ``REDEFINES`` does not advance
the cursor: it re-describes bytes already counted, which is how one area
holds a date as characters and as digits at the same time. ``OCCURS``
multiplies a subtree, so the whole group repeats rather than the last field.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

# Binary widths under the IBM default. Note this is decimal *digits* deciding
# the byte count, not the value range: S9(4) COMP is two bytes and, under
# TRUNC(STD), cannot hold 32767 despite two bytes being able to.
_BINARY_BYTES = ((4, 2), (9, 4), (18, 8))


@dataclass
class Field:
    name: str
    offset: int
    length: int
    pic: str = ""
    usage: str = ""
    occurs: int = 0
    redefines: str = ""

    @property
    def end(self) -> int:
        return self.offset + self.length


def digits_of(pic: str) -> tuple:
    """(integer digits, decimal digits) implied by a PIC clause."""
    spec = (pic or "").upper()
    whole = dec = 0
    for part, target in ((spec.split("V")[0], "w"),
                         (spec.split("V")[1] if "V" in spec else "", "d")):
        count = 0
        for m in re.finditer(r"([9XAZ])(?:\((\d+)\))?", part):
            count += int(m.group(2)) if m.group(2) else 1
        if target == "w":
            whole = count
        else:
            dec = count
    return whole, dec


def byte_length(pic: str, usage: str = "", sign: str = "") -> int:
    """How many bytes a single occurrence of an elementary field occupies."""
    spec = (pic or "").upper()
    usage = (usage or "DISPLAY").upper()
    if not spec:
        return 0
    whole, dec = digits_of(spec)
    total = whole + dec

    if usage in ("COMP-3", "PACKED-DECIMAL"):
        # Two digits per byte, plus a nibble for the sign, rounded up.
        return (total + 2) // 2
    if usage in ("COMP", "COMP-4", "COMP-5", "BINARY", "COMPUTATIONAL"):
        for limit, width in _BINARY_BYTES:
            if total <= limit:
                return width
        return 8
    if usage == "COMP-1":
        return 4
    if usage == "COMP-2":
        return 8
    if usage in ("INDEX", "POINTER"):
        return 4 if usage == "INDEX" else 8

    # DISPLAY. The sign is overpunched onto the last digit and costs nothing
    # unless it was asked to be SEPARATE.
    length = total
    if spec.startswith("S") and "SEPARATE" in (sign or "").upper():
        length += 1
    return length


def record_layout(model, root: str) -> list:
    """Every field under a group, in order, with offsets and lengths.

    Children are taken from the declaration order the parser recorded, so a
    layout reflects the source rather than an alphabetical accident.
    """
    root = root.upper()
    kids = _direct_children(model, root)
    if not kids:
        length = byte_length(model.pic.get(root, ""), model.usage.get(root, ""),
                             model.sign.get(root, ""))
        return [Field(root, 0, length, model.pic.get(root, ""),
                      model.usage.get(root, ""), model.occurs.get(root, 0),
                      model.redefines.get(root, ""))]

    out: list = []
    cursor = 0
    starts: dict = {}
    for child in kids:
        redefines = model.redefines.get(child, "")
        if redefines and redefines.upper() in starts:
            # Re-describes bytes already counted; the cursor does not move.
            begin = starts[redefines.upper()]
        else:
            begin = cursor

        sub = record_layout(model, child)
        size = max((f.end for f in sub), default=0)
        times = model.occurs.get(child, 0)
        span = size * times if times else size

        starts[child] = begin
        out.append(Field(child, begin, span, model.pic.get(child, ""),
                         model.usage.get(child, ""), times, redefines))
        for f in sub[1:] if len(sub) > 1 else []:
            out.append(Field(f.name, begin + f.offset, f.length, f.pic,
                             f.usage, f.occurs, f.redefines))
        if not redefines:
            cursor = begin + span
    return [Field(root, 0, cursor)] + out


def _direct_children(model, group: str) -> list:
    """Immediate children, in declaration order.

    FILLER is included: it cannot be referenced but it takes up space, and
    a layout that skips it puts everything after it at the wrong offset.
    """
    return [name for name, parent in model.parent.items()
            if parent.upper() == group.upper()]


def render(model, root: str, values: dict | None = None) -> str:
    """The record as bytes, with any known values placed in their fields."""
    fields = record_layout(model, root)
    size = fields[0].length if fields else 0
    buffer = [" "] * size
    for f in fields[1:]:
        if not values or f.name not in values:
            continue
        text = str(values[f.name])
        usage = (f.usage or "DISPLAY").upper()
        if usage not in ("DISPLAY", ""):
            continue          # packed and binary need real encoding, not text
        text = (text[:f.length] if len(text) > f.length
                else text.ljust(f.length))
        buffer[f.offset:f.offset + f.length] = list(text)
    return "".join(buffer)
