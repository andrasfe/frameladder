"""Does a generated plan actually reach its target in a real compiler?

`differential.py` compares interpreter and compiler on *default* runs, so it
validates control-flow semantics but never a plan.  Every reachability claim
the tool makes is therefore self-reported: the interpreter that verifies the
plan is the one whose rules produced it.

This closes that gap.  The plan's entry state is injected as MOVE statements
at the top of the PROCEDURE DIVISION, every paragraph is marked, and the
program is compiled and run.  If the target's marker appears, the plan works
in GnuCOBOL.  If it does not, the plan was only ever true of the interpreter.

Only the *entry state* can be injected this way.  Outcomes the plan assigns
to external operations are returns from CALL and READ, which no amount of
MOVE statements can supply, so those plans are reported separately rather
than counted as passes.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from frameladder.cobol import ENTRY_PARAGRAPH, load_program, read_lines
from frameladder.interpreter import verify
from frameladder.ladder import analyse, build_plan
from frameladder.witness import WitnessStore
from conformance.differential import (MARKER, compile_and_run, instrument,
                                      io_defaults, stage_files)


def literal(value) -> str | None:
    """Render a planned value as a COBOL literal, or None if it cannot be."""
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        return str(value)
    if not isinstance(value, str):
        return None
    if value == "":
        return "SPACES"
    if all(ch == "\x00" for ch in value):
        return "LOW-VALUES"
    if all(ch == "\xff" for ch in value):
        return "HIGH-VALUES"
    if any(ord(ch) < 32 or ord(ch) > 126 or ch == "'" for ch in value):
        return None
    return "'%s'" % value


def inject(src: str, out: str, state: dict, declared: set) -> tuple:
    """Put MOVE statements for the plan's entry state at the program's start."""
    with open(src, "r", errors="replace") as fh:
        lines = fh.read().splitlines()

    where = None
    for i, line in enumerate(lines):
        body = line[6:72] if len(line) > 6 else line
        if re.search(r"\bPROCEDURE\s+DIVISION\b", body, re.I):
            where = i
            while where < len(lines) and "." not in (
                    lines[where][6:72] if len(lines[where]) > 6 else lines[where]):
                where += 1
            break
    if where is None:
        return None, [], list(state)

    applied, skipped = [], []
    moves = []
    for name, value in sorted(state.items()):
        text = literal(value)
        if text is None or name not in declared:
            skipped.append(name)
            continue
        moves.append("           MOVE %s TO %s" % (text, name))
        applied.append(name)

    lines[where + 1:where + 1] = moves
    with open(out, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    return out, applied, skipped


def check(path: str, copybooks=(), limit: int | None = None,
          store: WitnessStore | None = None) -> list:
    program = load_program(path)
    analyse(program)
    entry = program.paragraph_names[0] if program.paragraph_names else None
    if not entry:
        return []
    declared = set(program.model.declared)
    rows = []

    targets = [n for n in program.paragraph_names[1:]]
    if limit:
        targets = targets[:limit]

    # Compiling a state yields a whole trace, and a trace answers
    # reachability for every paragraph at once - so the unit of work is the
    # distinct state, not the target. Two thirds of targets ask for a state
    # some other target already asked for.
    groups: dict = {}
    for target in targets:
        plan = build_plan(program, target, entry=entry)
        if not plan.chain:
            continue
        predicted = verify(program, plan, entry,
                           defaults=io_defaults(program))["reached"]
        signature = repr(sorted(plan.flat_state().items()))
        groups.setdefault(signature, []).append((target, plan, predicted))

    for signature, members in groups.items():
        _t, plan, _p = members[0]
        work = tempfile.mkdtemp(prefix="fl-plan-")
        marked = os.path.join(work, os.path.basename(path))
        instrument(path, marked)
        injected = os.path.join(work, "inj_" + os.path.basename(path))
        result, applied, skipped = inject(marked, injected,
                                          plan.flat_state(), declared)
        if result is None:
            continue
        trace, note = compile_and_run(injected, work, copybooks,
                                      stage_files(path, work))
        for index, (target, plan, predicted) in enumerate(members):
            row = {
                "target": target,
                "needs_stubs": bool(plan.stub_plan()),
                "predicted": predicted,
                "real": (trace is not None and target in trace),
                "applied": applied, "skipped": skipped,
                "note": note if trace is None else "",
                "cached": index > 0,
            }
            if store is not None and row["real"]:
                store.add(plan.chain, plan.flat_state(), target,
                          verified=True, source="compiler")
            rows.append(row)
    rows.sort(key=lambda r: r["target"])
    return rows


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("programs", nargs="+")
    ap.add_argument("-I", "--copybooks", action="append", default=[])
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--witnesses", help="file to persist confirmed witnesses in")
    args = ap.parse_args(argv)

    agree = disagree = 0
    stub_dependent = 0
    compiles = cached = 0
    store = WitnessStore(args.witnesses)
    matrix = {(True, True): 0, (True, False): 0,
              (False, True): 0, (False, False): 0}
    for path in args.programs:
        rows = check(path, args.copybooks, args.limit, store)
        if not rows:
            print("%-16s (nothing runnable)" % os.path.basename(path))
            continue
        print("\n%s" % os.path.basename(path))
        print("  %-32s %10s %8s %s" % ("target", "predicted", "real", "verdict"))
        for r in rows:
            if r["note"]:
                print("  %-32s %10s %8s %s" % (r["target"], r["predicted"], "-",
                                               r["note"][:40]))
                continue
            if r.get("cached"):
                cached += 1
            else:
                compiles += 1
            if r["needs_stubs"]:
                stub_dependent += 1
            ok = r["predicted"] == r["real"]
            agree += ok
            disagree += not ok
            matrix[(bool(r["predicted"]), bool(r["real"]))] += 1
            print("  %-32s %10s %8s %s%s"
                  % (r["target"], r["predicted"], r["real"],
                     "agree" if ok else "DISAGREE",
                     "  (plan needs stub outcomes)" if r["needs_stubs"] else ""))

    total = agree + disagree
    if total:
        print("\n%-38s %s" % ("interpreter says REACHED, GnuCOBOL agrees:",
                              matrix[(True, True)]))
        print("%-38s %s" % ("interpreter says REACHED, GnuCOBOL does not:",
                            matrix[(True, False)]))
        print("%-38s %s" % ("interpreter says no, GnuCOBOL reaches it:",
                            matrix[(False, True)]))
        print("%-38s %s" % ("both say not reached:", matrix[(False, False)]))
        print("\nagreement %d/%d (%.0f%%); %d plans also depend on stub "
              "outcomes that entry-state injection cannot supply"
              % (agree, total, 100.0 * agree / total, stub_dependent))
        print("compiles run %d, reused from an identical confirmed state %d "
              "(%.0f%% avoided)"
              % (compiles, cached, 100.0 * cached / max(1, compiles + cached)))
        if args.witnesses:
            store.save()
            print("witnesses: %s" % json.dumps(store.summary()))
    return 0 if disagree == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
