"""Byte-level storage: a record is bytes, and a name is a window onto them.

``layout.py`` already answers *where* a field sits and *how wide it is*; this
module makes that the storage model rather than a report about it.  A field
map - ``{FIELD: value}`` - cannot express four things COBOL does routinely,
and each of them is a wrong answer rather than a coarse one:

* ``WS-TAB(1)`` and ``WS-TAB(2)`` are different bytes.  Flattened to one cell,
  a table write is read back by every other subscript.
* ``REDEFINES`` of a different shape or width is one set of bytes read two
  ways.  Aliasing values instead only works when the two descriptions happen
  to have the same width and the same category.
* ``MOVE`` truncates because the receiving field is that many bytes wide, in
  opposite directions for the two categories.  Deriving it from the PIC
  separately is a second implementation of the same fact.
* ``USAGE`` decides the bytes entirely.  ``S9(4)`` is four characters as
  DISPLAY, two as COMP and three as COMP-3, and a parity generator that
  cannot say which is looking for divergence with the wrong instrument.

Everything here is standard COBOL: the encodings are the ones the standard
and the IBM manuals fix, and nothing in this file knows a field name.

Byte values were checked against GnuCOBOL 3.2 on an ASCII host by
redefining each representation as ``PIC X(n)`` and printing ``FUNCTION ORD``
of every byte - see the sign tables below for what that showed.
"""

from __future__ import annotations

import re
import struct
from collections.abc import MutableMapping
from dataclasses import dataclass

from .layout import byte_length, digits_of, record_layout

# Bytes and characters are the same alphabet here: latin-1 is the only codec
# that round-trips all 256 of them, which is what LOW-VALUE and HIGH-VALUE
# need - they are byte values, not letters.
CODEC = "latin-1"

# `A OF B` is a qualified reference: one name, spelled with the group it
# belongs to. It names the same declaration - and therefore the same bytes -
# as the bare name.
_QUALIFIED = re.compile(r"\s+(?:OF|IN)\s+", re.I)

# A DISPLAY sign is overpunched onto one digit rather than costing a byte.
# GnuCOBOL on an ASCII host writes 0x70+d for a negative digit and leaves a
# positive one alone; a record extracted from z/OS carries the EBCDIC zones
# instead. Both are read; the ASCII form is written, because GnuCOBOL is the
# oracle this repository checks itself against.
_NEG_PUNCH = {}
_POS_PUNCH = {}
for _d in range(10):
    _NEG_PUNCH[0x70 + _d] = _d                      # GnuCOBOL ASCII
    _NEG_PUNCH[0xD0 + _d] = _d                      # EBCDIC zone D
    _POS_PUNCH[0x30 + _d] = _d                      # plain digit
    _POS_PUNCH[0xC0 + _d] = _d                      # EBCDIC zone C
# The EBCDIC zones seen through a straight byte copy: '{ABCDEFGHI' positive,
# '}JKLMNOPQR' negative. A staged mainframe extract arrives looking like this.
for _i, _c in enumerate("{ABCDEFGHI"):
    _POS_PUNCH.setdefault(ord(_c), _i)
for _i, _c in enumerate("}JKLMNOPQR"):
    _NEG_PUNCH.setdefault(ord(_c), _i)

_PACKED = ("COMP-3", "PACKED-DECIMAL", "COMPUTATIONAL-3")
_BINARY = ("COMP", "COMP-4", "COMP-5", "BINARY", "COMPUTATIONAL",
           "COMPUTATIONAL-4", "COMPUTATIONAL-5")
_FLOAT = {"COMP-1": 4, "COMP-2": 8, "COMPUTATIONAL-1": 4, "COMPUTATIONAL-2": 8}
_ADDRESS = ("INDEX", "POINTER", "PROCEDURE-POINTER")

# Anything in a PIC that is neither a digit position nor a category letter is
# an editing character, and an edited item holds the *printed* form rather
# than the value. Encoding one as a number would put the wrong bytes in the
# record; it is carried as text instead, at its declared width.
_PIC_PLAIN = set("S9XAVN")

# A table can be declared far larger than any run will touch. Buffers are
# allocated on first use for that reason; this only bounds the pathological
# case where one declaration would dominate the whole run.
MAX_ROOT_BYTES = 4 << 20


def _is_edited(spec: str) -> bool:
    body = re.sub(r"\(\d+\)", "", (spec or "").upper())
    return bool(set(body) - _PIC_PLAIN)


def _category(pic: str, usage: str) -> str:
    """What the bytes of this field mean. Decided by PIC and USAGE only."""
    spec = (pic or "").upper()
    use = (usage or "DISPLAY").upper()
    if not spec and use not in _ADDRESS:
        return "group"
    if use in _PACKED:
        return "packed"
    if use in _BINARY:
        return "binary"
    if use in _FLOAT:
        return "float"
    if use in _ADDRESS:
        return "binary"
    if _is_edited(spec):
        return "edited"
    if "9" in spec and "X" not in spec and "A" not in spec:
        return "display-num"
    return "alnum"


@dataclass(frozen=True)
class Slot:
    """One name's window: where it starts, how wide one occurrence is, and
    how to read the bytes back."""
    name: str
    root: str
    offset: int                # byte offset of occurrence 1 within the root
    length: int                # bytes in ONE occurrence
    category: str
    pic: str = ""
    usage: str = "DISPLAY"
    scale: int = 0             # digits after the implied decimal point
    digits: int = 0
    signed: bool = False
    separate: str = ""         # "" | "LEADING" | "TRAILING"
    dims: tuple = ()           # ((stride, count), ...), outermost first

    @property
    def numeric(self) -> bool:
        return self.category in ("display-num", "packed", "binary", "float")


# --------------------------------------------------------------------------
# Codecs
# --------------------------------------------------------------------------

# LOW-VALUE and HIGH-VALUE name a byte, and a figurative constant is as wide
# as the item it initialises: `01 A PIC X(3) VALUE LOW-VALUES` is three NULs,
# not one NUL and two spaces. The parser resolves the constant to its byte
# before the layout ever sees it, which is right for every other consumer, so
# the width has to be put back here. A one-character *literal* is padded with
# spaces instead, which is what the normal alphanumeric rule already does.
FILL_BYTES = ("\x00", "\xff")


def _spread(value, length: int):
    if isinstance(value, str) and value in FILL_BYTES and length > 1:
        return value * length
    return value


def _as_number(value):
    if isinstance(value, bool):
        return 1 if value else 0
    if isinstance(value, (int, float)):
        return value
    text = "" if value is None else str(value).strip()
    if not text:
        return None
    try:
        return float(text) if ("." in text or "E" in text.upper()) else int(text)
    except ValueError:
        return None


def _scaled(value, scale: int, digits: int):
    """The integer the field actually stores, truncated the COBOL way.

    Truncation, not rounding, and in both directions at once: the low-order
    digits past the field's own scale are dropped, and so are the high-order
    ones past its width. `MOVE 12345 TO PIC 9(2)` leaves 45 - not 12 - and
    `MOVE 1.239 TO PIC 9V99` leaves 1.23. ROUNDED is a phrase on the
    arithmetic statements and is applied before this.
    """
    number = _as_number(value)
    if number is None:
        return None
    if scale <= 0:
        scaled = abs(int(number))
    else:
        # Binary floating point cannot be trusted to truncate: 0.29 * 100 is
        # 28.999999999999996, and int() of that is 28. Decimal reads the
        # digits the value was written with.
        from decimal import Decimal, InvalidOperation
        try:
            scaled = int(abs(Decimal(str(number))) * (10 ** scale))
        except (InvalidOperation, ValueError):
            scaled = int(abs(number) * (10 ** scale))
    if digits > 0:
        scaled %= 10 ** digits
    return -scaled if number < 0 else scaled


def _unscale(units: int, scale: int):
    if scale <= 0:
        return units
    return units / float(10 ** scale)


def encode(slot: Slot, value) -> bytes:
    """One value as the bytes the field holds. Never longer than the field."""
    n = slot.length
    if n <= 0:
        return b""
    cat = slot.category

    if cat in ("group", "alnum", "edited"):
        if cat == "edited" and isinstance(value, (int, float)) \
                and not isinstance(value, bool):
            body = ("%d" % value if float(value).is_integer()
                    else str(value)).rjust(n)
        else:
            body = "" if value is None else str(value)
        raw = body.encode(CODEC, "replace")
        return raw[:n] if len(raw) >= n else raw + b" " * (n - len(raw))

    units = _scaled(value, slot.scale, slot.digits)
    if units is None:
        # Not a number at all. The bytes of a numeric field are still bytes,
        # and a plan or a group move can put text in one; keeping it is what
        # lets `IS NUMERIC` go the way the program's own data sends it.
        raw = ("" if value is None else str(value)).encode(CODEC, "replace")
        return raw[:n] if len(raw) >= n else raw + b" " * (n - len(raw))

    if cat == "binary":
        limit = 1 << (8 * n)
        if slot.signed:
            wrapped = ((units + (limit >> 1)) % limit) - (limit >> 1)
            return int(wrapped).to_bytes(n, "big", signed=True)
        return int(units % limit).to_bytes(n, "big", signed=False)

    if cat == "float":
        return struct.pack(">f" if n == 4 else ">d",
                           _unscale(units, slot.scale))

    if cat == "packed":
        places = 2 * n - 1
        text = str(abs(units)).zfill(places)[-places:]
        nibble = "C" if units >= 0 else "D"
        if not slot.signed:
            nibble = "F"
        return bytes.fromhex(text + nibble)

    # DISPLAY numeric.
    width = slot.digits
    text = str(abs(units)).zfill(width)[-width:] if width else ""
    if slot.signed and slot.separate:
        sign = "-" if units < 0 else "+"
        text = (sign + text) if slot.separate == "LEADING" else (text + sign)
    elif slot.signed and units < 0 and text:
        text = text[:-1] + chr(0x70 + int(text[-1]))
    raw = text.encode(CODEC, "replace")
    return raw[:n] if len(raw) >= n else b"0" * (n - len(raw)) + raw


def decode(slot: Slot, data: bytes):
    """The bytes back as a value.

    A numeric field whose bytes are not digits reads as its text rather than
    as zero: that is what the bytes say, and a class condition asked about
    the shape of them has to get the real answer.
    """
    cat = slot.category
    if cat in ("group", "alnum"):
        return data.decode(CODEC, "replace")

    if cat == "binary":
        units = int.from_bytes(data, "big", signed=slot.signed)
        return _unscale(units, slot.scale)

    if cat == "float":
        try:
            return struct.unpack(">f" if len(data) == 4 else ">d", data)[0]
        except struct.error:
            return 0.0

    if cat == "packed":
        raw = data.hex().upper()
        body, nibble = raw[:-1], raw[-1:]
        if not body.isdigit():
            return data.decode(CODEC, "replace")
        units = int(body or "0")
        if nibble in ("D", "B"):
            units = -units
        return _unscale(units, slot.scale)

    text = data.decode(CODEC, "replace")
    if cat == "edited":
        body = text.strip()
        number = _as_number(body)
        return body if number is None else number

    # DISPLAY numeric.
    body = text
    sign = 1
    if slot.signed and slot.separate == "LEADING":
        sign, body = (-1 if body[:1] == "-" else 1), body[1:]
    elif slot.signed and slot.separate == "TRAILING":
        sign, body = (-1 if body[-1:] == "-" else 1), body[:-1]
    elif slot.signed and body:
        last = body[-1]
        code = ord(last)
        if code in _NEG_PUNCH and not last.isdigit():
            sign, body = -1, body[:-1] + str(_NEG_PUNCH[code])
        elif code in _POS_PUNCH and not last.isdigit():
            body = body[:-1] + str(_POS_PUNCH[code])
    body = body.strip()
    if not body or not body.isdigit():
        return text
    units = sign * int(body)
    return _unscale(units, slot.scale)


# --------------------------------------------------------------------------
# The layout, which is a property of the data division and not of a run
# --------------------------------------------------------------------------

class Layout:
    """Slot table and initial byte image for one program's data division.

    Built once per `DataModel` and shared by every run of it: nothing here
    depends on what a particular run did, and a coverage sweep builds
    hundreds of interpreters over the same declarations.
    """

    def __init__(self, model):
        self.model = model
        self.slots: dict = {}
        self.sizes: dict = {}          # root -> byte size
        self.images: dict = {}         # root -> initial bytes
        self.alias: dict = {}          # root -> the root whose bytes it shares
        self._build()

    # -- construction ---------------------------------------------------
    def _roots(self) -> list:
        names = []
        seen = set()
        for table in (self.model.pic, self.model.children, self.model.parent):
            for name in table:
                upper = name.upper()
                if upper in seen:
                    continue
                seen.add(upper)
                names.append(upper)
        return [n for n in names if not self.model.parent.get(n)]

    def _build(self) -> None:
        for root in self._roots():
            try:
                fields = record_layout(self.model, root)
            except Exception:                                    # noqa: BLE001
                continue
            if not fields:
                continue
            size = max((f.end for f in fields), default=0)
            if size <= 0 or size > MAX_ROOT_BYTES:
                continue
            # A 01-level REDEFINES has no group to hang off, so `record_layout`
            # never sees the pair. It is the same construct one level up and
            # wants the same answer: the two names name one set of bytes.
            over = (self.model.redefines.get(root) or "").upper()
            self.sizes[root] = size
            if over:
                self.alias[root] = over
            occurrences = {f.name.upper(): (f.length // f.occurs, f.occurs)
                           for f in fields if f.occurs}
            for field in fields:
                slot = self._slot(root, field, occurrences)
                if slot is not None and slot.name not in self.slots:
                    self.slots[slot.name] = slot
        # Resolve alias chains, then give every root that owns bytes an image.
        for root in list(self.alias):
            seen = set()
            target = root
            while target in self.alias and target not in seen:
                seen.add(target)
                target = self.alias[target]
            self.alias[root] = target
            self.sizes[target] = max(self.sizes.get(target, 0),
                                     self.sizes.get(root, 0))
        for root in self.sizes:
            if root not in self.alias:
                self.images[root] = self._image(root)

    def _slot(self, root: str, field, occurrences: dict):
        name = field.name.upper()
        pic = field.pic or ""
        usage = (field.usage or self.model.usage_of(name) or "DISPLAY").upper()
        stride = (field.length // field.occurs) if field.occurs else field.length
        if stride <= 0:
            return None
        category = _category(pic, usage)
        whole, dec = digits_of(pic) if pic else (0, 0)
        sign = (self.model.look(self.model.sign, name, "") or "").upper()
        separate = ""
        if "SEPARATE" in sign:
            separate = "LEADING" if "LEADING" in sign else "TRAILING"
        return Slot(name=name, root=root, offset=field.offset, length=stride,
                    category=category, pic=pic, usage=usage,
                    scale=dec if category != "alnum" else 0,
                    digits=whole + dec, signed=pic.upper().startswith("S"),
                    separate=separate,
                    dims=self._dims(name, occurrences))

    def _dims(self, name: str, occurrences: dict) -> tuple:
        chain = []
        cursor = name
        guard = 0
        while cursor and guard < 64:
            if cursor in occurrences:
                chain.append(occurrences[cursor])
            cursor = (self.model.parent.get(cursor) or "").upper()
            guard += 1
        return tuple(reversed(chain))

    def _image(self, root: str) -> bytes:
        """The bytes the program starts with.

        A field with no VALUE is not undefined: GnuCOBOL leaves a DISPLAY
        numeric item reading zero and an alphanumeric one reading spaces, and
        so does every mainframe compiler under the usual options. Checked by
        compiling a bare `01 N PIC 9(3).` and printing its bytes.
        """
        size = self.sizes.get(root, 0)
        buffer = bytearray(b" " * size)
        for name, slot in self.slots.items():
            if slot.root != root or slot.category == "group":
                continue
            if self._under_redefines(name, root):
                continue
            value = self.model.look(self.model.initial, name)
            if value is None:
                value = 0 if slot.numeric or slot.category == "edited" else " "
            if slot.category in ("alnum", "edited") and not isinstance(value, str):
                value = str(value)
            raw = encode(slot, _spread(value, slot.length))
            count = 1
            for _stride, times in slot.dims:
                count *= times
            step = slot.length
            for occurrence in range(count):
                start = slot.offset + self._stride_offset(slot, occurrence)
                if start + step <= size:
                    buffer[start:start + step] = raw
        # A group with its own VALUE fills the whole window; that is one
        # clause covering bytes the children never mention.
        for name, slot in self.slots.items():
            if slot.root != root or slot.category != "group":
                continue
            value = self.model.look(self.model.initial, name)
            if value is None:
                continue
            raw = encode(slot, value if isinstance(value, str) else str(value))
            buffer[slot.offset:slot.offset + slot.length] = raw
        return bytes(buffer)

    @staticmethod
    def _stride_offset(slot: Slot, occurrence: int) -> int:
        """Byte offset of the n-th occurrence, counting the dimensions from
        the innermost outwards."""
        remaining, offset = occurrence, 0
        for stride, count in reversed(slot.dims):
            offset += (remaining % count) * stride
            remaining //= count
        return offset

    def _under_redefines(self, name: str, root: str) -> bool:
        cursor = name
        guard = 0
        while cursor and guard < 64:
            if self.model.redefines.get(cursor):
                return True
            if cursor == root:
                return False
            cursor = (self.model.parent.get(cursor) or "").upper()
            guard += 1
        return False

    # -- queries --------------------------------------------------------
    def slot_for(self, name: str):
        upper = (name or "").upper()
        found = self.slots.get(upper)
        if found is not None:
            return found
        from .ir import base_name
        return self.slots.get(base_name(upper))


def layout_of(model) -> Layout:
    """Cached per data model - the declarations do not change during a run."""
    cached = getattr(model, "_fl_layout", None)
    if cached is None:
        cached = Layout(model)
        try:
            model._fl_layout = cached
        except Exception:                                        # noqa: BLE001
            pass
    return cached


# --------------------------------------------------------------------------
# The store itself
# --------------------------------------------------------------------------

class ByteMemory:
    """One run's bytes. Buffers are allocated the first time a record is
    touched, so a program that declares a large table but never reads it
    costs nothing."""

    def __init__(self, layout: Layout):
        self.layout = layout
        self._buffers: dict = {}

    def buffer(self, root: str) -> bytearray:
        target = self.layout.alias.get(root, root)
        buffer = self._buffers.get(target)
        if buffer is None:
            image = self.layout.images.get(target)
            if image is None:
                image = b" " * self.layout.sizes.get(target, 0)
            buffer = bytearray(image)
            self._buffers[target] = buffer
        return buffer

    def window(self, slot: Slot, index=()) -> tuple:
        """(buffer, start, length) for one occurrence of one field."""
        offset = slot.offset
        for position, (stride, count) in enumerate(slot.dims):
            raw = index[position] if position < len(index) else 1
            try:
                subscript = int(raw)
            except (TypeError, ValueError):
                subscript = 1
            if subscript < 1:
                subscript = 1
            if count and subscript > count:
                # Out of range. COBOL without SSRANGE reads past the table;
                # clamping keeps the run inside its own record rather than
                # inventing a neighbour's bytes.
                subscript = count
            offset += (subscript - 1) * stride
        buffer = self.buffer(slot.root)
        if offset + slot.length > len(buffer):
            buffer.extend(b" " * (offset + slot.length - len(buffer)))
        return buffer, offset, slot.length

    def read(self, slot: Slot, index=()):
        buffer, offset, length = self.window(slot, index)
        return decode(slot, bytes(buffer[offset:offset + length]))

    def raw(self, slot: Slot, index=()) -> bytes:
        buffer, offset, length = self.window(slot, index)
        return bytes(buffer[offset:offset + length])

    def write(self, slot: Slot, value, index=(), fill: str = "") -> None:
        buffer, offset, length = self.window(slot, index)
        if fill:
            # A figurative constant is as wide as whatever receives it:
            # `MOVE SPACES TO <group>` blanks the whole group, and `MOVE
            # ZEROS` fills it with the character zero rather than with one.
            raw = (fill * length).encode(CODEC, "replace")[:length]
        else:
            raw = encode(slot, value)
        buffer[offset:offset + length] = raw

    def write_raw(self, slot: Slot, data: bytes, index=()) -> None:
        buffer, offset, length = self.window(slot, index)
        if len(data) < length:
            data = data + b" " * (length - len(data))
        buffer[offset:offset + length] = data[:length]


def occurrence_count(slot: Slot) -> int:
    total = 1
    for _stride, times in slot.dims:
        total *= max(1, times)
    return total


def occurrence_index(slot: Slot, ordinal: int) -> tuple:
    """The one-based subscripts of the n-th occurrence, innermost varying
    fastest - the order a table is laid out in memory."""
    subscripts = []
    remaining = ordinal
    for _stride, count in reversed(slot.dims):
        count = max(1, count)
        subscripts.append(remaining % count + 1)
        remaining //= count
    return tuple(reversed(subscripts))


class FieldMap(MutableMapping):
    """The ``{FIELD: value}`` interface, backed by bytes where there is a layout.

    Everything outside this module goes on reading and writing names. A name
    the data division describes is a window onto a record; a name it does not
    - a table index, a harness slot, a value a plan supplies for something the
    program never declared - is an ordinary dictionary entry, exactly as
    before. That fallback is the reason this can be adopted at all: a partial
    layout degrades to the old model field by field rather than all at once.

    Not a ``dict`` subclass on purpose. ``dict(other)`` and ``{**other}`` take
    the C-level fast path for anything that passes ``PyDict_Check``, which
    would read the underlying dictionary and miss every byte-backed field.
    """

    def __init__(self, memory: ByteMemory, initial=None):
        self.memory = memory
        self.extra: dict = {}
        # `FNAMEI` and `FNAMEI OF COUSR1AI` are two ways of writing one
        # declaration, so they are one set of bytes and an entry state that
        # mentions both has to settle which it meant. The qualified form is
        # the more specific reference, so it is applied last and wins - which
        # is also what a per-read exact-key lookup used to do. Held apart as
        # separate cells they scored conditions in which one field was two
        # different values at once, which no compiler can produce.
        for name, value in sorted((initial or {}).items(),
                                  key=lambda kv: _QUALIFIED.search(kv[0]) is not None):
            self[name] = value

    def slot(self, key: str):
        return self.memory.layout.slot_for(key)

    def __getitem__(self, key):
        upper = (key or "").upper()
        slot = self.slot(upper)
        if slot is not None:
            return self.memory.read(slot)
        if upper in self.extra:
            return self.extra[upper]
        raise KeyError(key)

    def __setitem__(self, key, value) -> None:
        upper = (key or "").upper()
        slot = self.slot(upper)
        if slot is not None:
            self.memory.write(slot, value)
        else:
            self.extra[upper] = value

    def __delitem__(self, key) -> None:
        self.extra.pop((key or "").upper(), None)

    def __contains__(self, key) -> bool:
        upper = (key or "").upper()
        return upper in self.extra or self.slot(upper) is not None

    def __iter__(self):
        seen = set(self.extra)
        yield from self.extra
        for name in self.memory.layout.slots:
            if name not in seen:
                yield name

    def __len__(self) -> int:
        return len(set(self.extra) | set(self.memory.layout.slots))
