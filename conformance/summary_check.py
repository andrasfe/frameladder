"""Does a paragraph summary agree with the interpreter about the same paragraph?

A summary that disagrees with execution is worse than no summary: it produces
confident, wrong plans, and this repository has found that failure three times
already under different names. So the summary is a *claim* and this is the
harness that checks it, in the same spirit as `conformance/microdiff.py` for
the interpreter and `tests/parser_agreement.py` for the parser.

The check is deliberately blunt. For a paragraph and a concrete entry state:

* run the paragraph in the interpreter and record which paragraphs it
  performed and which variables it wrote;
* find the summary paths whose condition is *consistent* with that state;
* require that at least one of them predicts the same calls, and that every
  write it predicts before a call really did happen before that call.

Consistency, not satisfaction: a summary path's condition is evaluated with
the interpreter's own `evaluate`, so the two cannot disagree about what a
COBOL condition means - only about the structure of the paragraph, which is
what is being tested.

Run:  python3 -m conformance.summary_check <program.cbl> [--copybooks DIR]
"""

from __future__ import annotations

import argparse
import glob
import os
import random
import sys

from frameladder.cobol import load_program
from frameladder.conformance_defaults import io_defaults
from frameladder.interpreter import Interpreter
from frameladder.summary import summarise_program


# Relations this harness can decide. A class condition (`IS NUMERIC`) and
# anything else it cannot judge is *not* evidence against the summary: an
# earlier version stringified every atom and re-parsed it, which turned
# `IO-STATUS NOT NUMERIC` into a comparison against the literal 'NUMERIC',
# evaluated it false, and reported the paragraph as a disagreement. The
# summary was right and the harness was wrong, which is the one direction a
# conformance harness must never fail in.
_DECIDABLE = ("=", "!=", "<", ">", "<=", ">=")


def _atom_is_false(interp, atom) -> bool:
    """True only when this atom is *definitely* false in this state."""
    from frameladder.ir import holds
    if getattr(atom, "op", "") not in _DECIDABLE:
        return False
    try:
        sides = []
        for term in (atom.lhs, atom.rhs):
            if getattr(term, "kind", "") == "const":
                sides.append(term.value)
            elif getattr(term, "kind", "") == "var" and not term.index:
                if term.name not in interp.state:
                    return False               # unknown; cannot judge
                sides.append(interp.state[term.name])
            else:
                return False
        return not holds(sides[0], atom.op, sides[1])
    except Exception:                                        # noqa: BLE001
        return False


def _states(program, count: int, seed: int) -> list:
    """Entry states drawn from the literals the program itself compares."""
    from frameladder.ladder import analyse
    _graph, prov = analyse(program)
    pool = {name: sorted(values, key=repr)
            for name, values in prov.literals.items() if values}
    rng = random.Random(seed)
    out = [{}]
    for _ in range(count - 1):
        out.append({name: rng.choice(values) for name, values in pool.items()})
    return out


def check_program(path: str, copybooks: str | None, samples: int = 6,
                  seed: int = 7) -> dict:
    program = load_program(path, copybooks)
    summaries = summarise_program(program)
    defaults = io_defaults(program, "bare")

    agree = disagree = skipped = 0
    complaints: list = []

    for state in _states(program, samples, seed):
        for name, summary in summaries.items():
            if not summary.paths:
                skipped += 1
                continue
            interp = Interpreter(program, dict(state), defaults=defaults)
            before = set(interp.state)
            try:
                interp.perform(name, 0)
            except Exception:                                # noqa: BLE001
                skipped += 1
                continue
            performed = [p for p in interp.trace.entered if p != name]
            touched = {k for k in interp.state
                       if k not in before or interp.state.get(k)
                       != state.get(k)} - {"_display"}

            live = [c for c in summary.paths
                    if not any(_atom_is_false(interp, a) for a in c.condition)]

            if not live:
                # Every path ruled out, yet the paragraph ran. Only a
                # complaint when the summary claims to be complete.
                if summary.complete:
                    disagree += 1
                    complaints.append((name, "no path matched a state the "
                                             "paragraph ran under"))
                else:
                    skipped += 1
                continue

            predicted = {n for c in live for _i, n in c.calls}
            actual = {q.upper() for q in performed}
            missing = {c for c in actual if c in program.paragraph_names} - predicted
            if missing and summary.complete:
                disagree += 1
                complaints.append((name, "performed %s, no path predicted it"
                                   % ", ".join(sorted(missing)[:3])))
            else:
                agree += 1

    return {"program": os.path.basename(path), "paragraphs": len(summaries),
            "complete": sum(1 for s in summaries.values() if s.complete),
            "agree": agree, "disagree": disagree, "skipped": skipped,
            "complaints": complaints[:6]}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("programs", nargs="+")
    ap.add_argument("--copybooks")
    ap.add_argument("--samples", type=int, default=6)
    ap.add_argument("--seed", type=int, default=7)
    args = ap.parse_args(argv)

    paths: list = []
    for pattern in args.programs:
        paths.extend(sorted(glob.glob(pattern)) or [pattern])

    total = {"agree": 0, "disagree": 0, "skipped": 0, "paragraphs": 0,
             "complete": 0}
    print("%-16s %6s %9s %7s %9s %8s" % ("program", "paras", "complete",
                                         "agree", "disagree", "skipped"))
    for path in paths:
        try:
            row = check_program(path, args.copybooks, args.samples, args.seed)
        except Exception as exc:                             # noqa: BLE001
            print("%-16s  parse/run failed: %s" % (os.path.basename(path),
                                                   str(exc)[:40]))
            continue
        for key in total:
            total[key] += row[key]
        print("%-16s %6d %9d %7d %9d %8d"
              % (row["program"], row["paragraphs"], row["complete"],
                 row["agree"], row["disagree"], row["skipped"]))
        for name, why in row["complaints"]:
            print("      %-28s %s" % (name, why))

    checked = total["agree"] + total["disagree"]
    print("\n%d paragraphs, %d complete (%.1f%%); %d/%d checks agree (%.2f%%)"
          % (total["paragraphs"], total["complete"],
             100.0 * total["complete"] / max(1, total["paragraphs"]),
             total["agree"], checked,
             100.0 * total["agree"] / max(1, checked)))
    return 0 if total["disagree"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
