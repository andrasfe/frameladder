"""Which entry-state bytes a value in flight is still a copy of.

The ladder lifts an obligation *statically*, outwards along the call chain,
and that is where deep targets are lost. A plan fixes a field in the entry
state; the program moves something else over it three paragraphs later; the
obligation arrives at the target attached to a field nobody is setting any
more. `provenance.blocking_writes` notices that a write exists, which is not
the same as knowing what to ask for instead.

This is the dynamic answer to the same question, and it is a weakest
precondition computed along a concrete path rather than over the whole
program. While a run is in progress every stored value carries the entry
field it is still a copy of and which byte range of it, so

    MOVE DFHCOMMAREA (1:200) TO CARDDEMO-COMMAREA

does not destroy the obligation on `CDEMO-FROM-TRANID`. It *relocates* it
onto bytes 74..78 of `DFHCOMMAREA`, which is a thing a harness can still set.
Lifting through a group move needs the record layout, and that is the whole
reason the transfer function lives next to a byte range rather than a name.

An origin is deliberately narrow. Copying is the only operation it survives:
arithmetic, INITIALIZE, STRING, a stub return and a literal MOVE all produce
values the entry state does not decide, and saying so is the useful half of
the answer. A guard whose operands are all opaque is a guard no entry state
can flip, and a search that knows this spends its budget somewhere else
instead of re-deriving the same dead plan once per route.

Opacity is represented by ``None`` rather than by a variant, because every
caller has to handle "cannot say" anyway and a sentinel object would only
make it possible to forget.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Origin:
    """Bytes ``[lo:hi)`` of the entry-state value of ``name``.

    ``hi`` is ``None`` for "to the end", which is both the common case - a
    whole field moved to a whole field - and the honest answer when a
    reference modification's length is an expression the interpreter could
    not evaluate.
    """

    name: str
    lo: int = 0
    hi: int | None = None

    @property
    def width(self) -> int | None:
        return None if self.hi is None else max(0, self.hi - self.lo)

    def slice(self, start: int, stop: int | None) -> "Origin | None":
        """The origin of bytes ``[start:stop)`` *of this value*.

        Composition is what makes the transfer function work through a chain
        of moves: a slice of a slice is a slice, so `MOVE A(5:20) TO B` then
        `MOVE B(3:2) TO C` leaves C holding bytes 7..9 of A, and an obligation
        on C is an obligation on those two bytes of A.
        """
        if start < 0:
            return None
        lo = self.lo + start
        if self.hi is not None and lo >= self.hi:
            return None                    # entirely past the end: no bytes
        hi = None if stop is None else self.lo + stop
        if hi is not None and self.hi is not None:
            hi = min(hi, self.hi)
        elif hi is None:
            hi = self.hi
        if hi is not None and hi <= lo:
            return None
        return Origin(self.name, lo, hi)

    @property
    def whole(self) -> bool:
        """True when this is the entry field itself, not a piece of one."""
        return self.lo == 0 and self.hi is None

    def __str__(self) -> str:
        if self.whole:
            return self.name
        return "%s(%d:%s)" % (self.name, self.lo + 1,
                              "" if self.hi is None else self.hi - self.lo)


def splice(base: str, lo: int, hi: int | None, piece: str) -> str:
    """Put ``piece`` at ``[lo:hi)`` of ``base``, growing it if it is short.

    Growing with spaces rather than refusing matters: the first obligation
    against a 2,000-byte commarea arrives when the entry state holds no
    commarea at all, and a harness that will not write byte 74 of a string
    that does not exist yet can never place the second one either.
    """
    text = base if isinstance(base, str) else ("" if base is None else str(base))
    end = hi if hi is not None else lo + len(piece)
    if len(text) < end:
        text = text.ljust(end)
    return text[:lo] + piece + (text[end:] if hi is not None else "")
