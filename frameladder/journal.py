"""Append-only run log, so a loop survives the agent session that started it."""

from __future__ import annotations

import json
import os
import time
from typing import Any


class Journal:
    def __init__(self, work_dir: str | None):
        self.dir = work_dir
        self.path = os.path.join(work_dir, "journal.jsonl") if work_dir else None
        if work_dir:
            os.makedirs(work_dir, exist_ok=True)

    def append(self, kind: str, **payload: Any) -> None:
        if not self.path:
            return
        record = {"t": round(time.time(), 3), "kind": kind}
        record.update(payload)
        with open(self.path, "a") as fh:
            fh.write(json.dumps(record, default=str) + "\n")
            fh.flush()
            os.fsync(fh.fileno())

    def events(self) -> list:
        if not self.path or not os.path.exists(self.path):
            return []
        out = []
        with open(self.path, "r", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    out.append(json.loads(line))
                except ValueError:
                    continue
        return out

    def bindings(self, target: str | None = None) -> dict:
        """Every binding the agent has supplied, latest wins."""
        out: dict = {}
        for event in self.events():
            if event.get("kind") != "bind":
                continue
            if target and event.get("target") not in (None, target):
                continue
            out[event["name"].upper()] = event["value"]
        return out

    def rejected(self, target: str | None = None) -> list:
        return [e for e in self.events()
                if e.get("kind") == "reject"
                and (not target or e.get("target") == target)]

    def snapshot(self) -> dict:
        events = self.events()
        attempts = [e for e in events if e.get("kind") == "verify"]
        return {
            "events": len(events),
            "bindings": self.bindings(),
            "attempts": len(attempts),
            "last_status": attempts[-1].get("reached") if attempts else None,
            "targets": sorted({e.get("target") for e in events if e.get("target")}),
            "notes": [e.get("text") for e in events if e.get("kind") == "note"][-10:],
        }
