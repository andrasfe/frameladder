"""Verified witnesses, kept and reused across traces.

A state that opens a paragraph is evidence about a *frame*, not about the
one path that happened to discover it.  Chains overlap heavily - across the
corpus 63% of targets have a chain that extends another target's - so every
target re-deriving its own arbitrary values wastes the work and, worse,
invents a different value each time for the same free slot.

A witness is keyed by the chain prefix it was verified for.  Planning a new
target looks up the longest prefix already known and offers its values as
*preferences*: they are taken where the ladder has a free choice and ignored
where a constraint decides, so reuse can make a plan more consistent but
never less correct.

Consistency is the real prize.  Confirming a witness against a compiler costs
a compile and a run; if twenty targets share a prefix and agree on its
values, that prefix is confirmed once rather than twenty times.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass, field


@dataclass
class Witness:
    chain: tuple
    state: dict
    target: str
    verified: bool = False
    source: str = "interpreter"        # 'interpreter' | 'compiler'

    @property
    def key(self) -> str:
        return " -> ".join(self.chain)


@dataclass
class WitnessStore:
    path: str | None = None
    entries: dict = field(default_factory=dict)

    def __post_init__(self):
        if self.path and os.path.exists(self.path):
            self.load()

    def add(self, chain, state: dict, target: str, verified: bool = False,
            source: str = "interpreter") -> Witness:
        witness = Witness(tuple(chain), dict(state), target, verified, source)
        prior = self.entries.get(witness.key)
        # A compiler-confirmed witness outranks an interpreter-only one; among
        # equals the first stands, so results stay stable across runs.
        if prior is None or (witness.verified and not prior.verified):
            self.entries[witness.key] = witness
        return self.entries[witness.key]

    def longest_prefix(self, chain) -> Witness | None:
        """The most specific witness whose chain is a prefix of this one."""
        chain = tuple(chain)
        best = None
        for witness in self.entries.values():
            n = len(witness.chain)
            if n > len(chain) or chain[:n] != witness.chain:
                continue
            if best is None or n > len(best.chain):
                best = witness
            elif n == len(best.chain) and witness.verified and not best.verified:
                best = witness
        return best

    def preferences(self, chain) -> dict:
        witness = self.longest_prefix(chain)
        return dict(witness.state) if witness else {}

    # -- persistence -------------------------------------------------------
    def load(self) -> None:
        try:
            with open(self.path, "r", errors="replace") as fh:
                raw = json.load(fh)
        except (OSError, ValueError):
            return
        for item in raw.get("witnesses", []):
            witness = Witness(tuple(item["chain"]), item["state"],
                              item.get("target", ""), item.get("verified", False),
                              item.get("source", "interpreter"))
            self.entries[witness.key] = witness

    def save(self) -> None:
        if not self.path:
            return
        os.makedirs(os.path.dirname(os.path.abspath(self.path)), exist_ok=True)
        payload = {"witnesses": [
            {"chain": list(w.chain), "state": w.state, "target": w.target,
             "verified": w.verified, "source": w.source}
            for w in self.entries.values()]}
        tmp = self.path + ".tmp"
        with open(tmp, "w") as fh:
            json.dump(payload, fh, indent=2, default=str)
        os.replace(tmp, self.path)

    def summary(self) -> dict:
        verified = [w for w in self.entries.values() if w.verified]
        return {"witnesses": len(self.entries),
                "verified": len(verified),
                "compiler_confirmed": sum(1 for w in verified
                                          if w.source == "compiler"),
                "distinct_states": len({json.dumps(w.state, sort_keys=True,
                                                   default=str)
                                        for w in self.entries.values()})}
