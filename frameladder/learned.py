"""Values that have been observed to work, kept and reused.

Everything else the tool knows about a value is static: a literal in the
source, a PIC clause, a platform status code. None of it says whether a value
*got anywhere*. A run does.

So each run that covers something new writes down what it was holding, and a
later plan facing a slot the source never pins down can ask what has worked
here before. The observation is the useful part - a value that reached a
frame once will very likely reach it again, and it costs nothing to try.

The division of labour matters. *Deciding what to try next* is judgment and
may vary: an agent looking at a date field and two working values either side
of a range can reasonably propose something between them. *Retrieving what is
known* must not vary, or two runs of the same command stop agreeing. So this
file records and retrieves deterministically, and the proposing is done by
whoever is driving - with :func:`between` offered as the one interpolation
that is safe to derive mechanically.
"""

from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass, field


@dataclass
class Observation:
    value: object
    covered: int = 0          # how much this value was holding when it worked
    seen: int = 0

    def to_dict(self) -> dict:
        return {"value": self.value, "covered": self.covered, "seen": self.seen}


@dataclass
class Learned:
    """field -> the values it has held on a run that covered something."""
    path: str | None = None
    fields: dict = field(default_factory=dict)

    def __post_init__(self):
        if self.path and os.path.exists(self.path):
            self.load()

    # -- recording ---------------------------------------------------------
    def record(self, state: dict, covered: int) -> None:
        """Note what a run was holding and how much it reached.

        Recording *every* run would fill the dictionary with values that
        prove nothing, so only runs that covered something are kept, and how
        much they covered is retained as the ranking.
        """
        if covered <= 0:
            return
        for name, value in (state or {}).items():
            key = str(name).upper()
            table = self.fields.setdefault(key, {})
            entry = table.get(repr(value))
            if entry is None:
                entry = Observation(value)
                table[repr(value)] = entry
            entry.seen += 1
            entry.covered = max(entry.covered, covered)

    # -- retrieval, which must be invariant --------------------------------
    def values_for(self, name: str) -> list:
        """What has worked here, best first, deterministically.

        Ordered by how much was covered when the value was in play, then by
        how often it has been seen, then by its own text - so the answer
        never depends on dictionary insertion order or on the run that
        happened to go first.
        """
        table = self.fields.get(str(name).upper(), {})
        entries = sorted(table.values(),
                         key=lambda e: (-e.covered, -e.seen, repr(e.value)))
        return [e.value for e in entries]

    def best(self, name: str):
        found = self.values_for(name)
        return found[0] if found else None

    def between(self, name: str):
        """A value between the two that have worked best.

        The one interpolation safe to derive without judgment: if two numbers
        both reached something, a number between them is the same shape and
        the same order of magnitude, and it probes the interval neither
        endpoint does. Only offered when the recorded values really are
        numeric - "between" two account codes means nothing.
        """
        found = [v for v in self.values_for(name) if _numeric(v)]
        if len(found) < 2:
            return None
        low, high = sorted((_number(found[0]), _number(found[1])))
        if high - low < 2:
            return None
        middle = low + (high - low) // 2
        sample = self.values_for(name)[0]
        if isinstance(sample, str):
            return str(middle).rjust(len(sample), "0")[-len(sample):]
        return middle

    # -- persistence -------------------------------------------------------
    def load(self) -> None:
        try:
            with open(self.path, "r", errors="replace") as fh:
                raw = json.load(fh)
        except (OSError, ValueError):
            return
        for name, entries in (raw.get("fields") or {}).items():
            table = self.fields.setdefault(name.upper(), {})
            for item in entries:
                table[repr(item["value"])] = Observation(
                    item["value"], item.get("covered", 0), item.get("seen", 0))

    def save(self) -> None:
        if not self.path:
            return
        directory = os.path.dirname(os.path.abspath(self.path))
        if directory:
            os.makedirs(directory, exist_ok=True)
        payload = {"fields": {name: [e.to_dict() for e in table.values()]
                              for name, table in sorted(self.fields.items())}}
        tmp = self.path + ".tmp"
        with open(tmp, "w") as fh:
            json.dump(payload, fh, indent=2, default=str, sort_keys=True)
        os.replace(tmp, self.path)

    def summary(self) -> dict:
        return {"fields": len(self.fields),
                "observations": sum(len(t) for t in self.fields.values())}


def _numeric(value) -> bool:
    if isinstance(value, bool):
        return False
    if isinstance(value, (int, float)):
        return True
    return isinstance(value, str) and bool(re.fullmatch(r"\s*-?\d+\s*", value))


def _number(value) -> int:
    return int(str(value).strip())
