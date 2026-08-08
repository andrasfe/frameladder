"""Check the interpreter against a real compiler.

Every "verified reached" result rests on the built-in interpreter, which
shares its condition parser and its control-flow rules with the planner.
If those rules are wrong, the plan and the verification are wrong in the
same way and agree with each other - so agreement proves nothing.

This breaks the circle.  Each paragraph is instrumented with a marker,
the program is compiled with GnuCOBOL and run, and the sequence of
paragraphs it really executed is compared against the sequence the
interpreter predicts.  A divergence is a genuine finding: one of the two
is wrong about COBOL, and the compiler is not the one to doubt.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from frameladder.cobol import load_program, read_lines
from frameladder.interpreter import Interpreter

MARKER = "FL:"
LIMIT = 400


def instrument(path: str, out_path: str) -> list:
    """Put a marker at the top of every paragraph.

    The parser being tested is also the one locating the paragraphs, which
    is fine: if it put a marker in the wrong place the traces would
    disagree, and disagreement is exactly what this looks for.
    """
    program = load_program(path)
    with open(path, "r", errors="replace") as fh:
        lines = fh.read().splitlines()

    insertions = []
    skipped = []
    for para in program.paragraphs:
        start = para.get("line_start") or 0
        if start <= 0:
            continue
        statements = para.get("statements") or []
        # An ALTER target must contain nothing but its GO TO - the compiler
        # rejects the paragraph outright otherwise. Marking it would change
        # what is being measured, so it goes untraced instead.
        if len(statements) == 1 and statements[0].get("type") in ("GO_TO", "GOTO"):
            skipped.append(para["name"])
            continue
        insertions.append((start, para["name"]))

    for start, name in sorted(insertions, reverse=True):
        lines.insert(start - 1, "           DISPLAY '%s%s'" % (MARKER, name))

    with open(out_path, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    return skipped


_ASSIGN = re.compile(r"\bASSIGN\s+(?:TO\s+)?([A-Z0-9][A-Z0-9-]*)", re.I)


def stage_files(path: str, work: str) -> list:
    """Give every assigned file an empty file to open.

    Without one the first OPEN fails and the program abends four
    paragraphs in, so the comparison only ever exercises the prologue.
    An empty file opens cleanly and the first READ returns end-of-file,
    which is a real, well-defined path through the program - and a much
    longer one.
    """
    names = []
    for line in read_lines(path):
        m = _ASSIGN.search(line.text)
        if m:
            names.append(m.group(1).upper())
    env = {}
    for name in names:
        target = os.path.join(work, name)
        if not os.path.exists(target):
            open(target, "w").close()
        env["DD_" + name] = target
    return env


def compile_and_run(src: str, work: str, copybooks=(), env_extra=None,
                    timeout: int = 10):
    """Returns (trace, note). An empty trace with a note is not a failure of
    the comparison - it means the program could not be run here."""
    binary = os.path.join(work, "prog")
    errors = []
    for extra in ([], ["-free"]):
        includes = [a for d in copybooks for a in ("-I", d)]
        proc = subprocess.run(["cobc", "-x", *extra, *includes, src, "-o", binary],
                              capture_output=True, text=True, cwd=work)
        if proc.returncode == 0:
            break
        errors.append((extra, (proc.stderr or "").strip()))
    else:
        # Report the *fixed-format* attempt: real mainframe source is fixed
        # format, and the free-format fallback fails on the sequence numbers
        # in columns 1-6, which would hide the actual problem.
        _flags, text = errors[0]
        lines = [l for l in text.splitlines() if "error:" in l]
        return None, "compile failed: %s" % (lines[0] if lines else
                                             (text.splitlines() or ["?"])[0])

    try:
        env = dict(os.environ)
        env.update(env_extra or {})
        run = subprocess.run([binary], capture_output=True, text=True,
                             cwd=work, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return None, "timed out"
    out = (run.stdout or "") + (run.stderr or "")
    trace = [m.group(1) for m in re.finditer(r"%s([A-Z0-9_-]+)" % MARKER, out)]
    return trace, ("exit %d" % run.returncode if run.returncode else "")


def io_defaults(program) -> dict:
    """Match the staged empty files: opens succeed, reads hit end-of-file.

    This is what the real run sees, so giving the interpreter anything
    else would compare two different executions and blame the difference
    on semantics.
    """
    out: dict = {}
    for f, status in program.model.file_status.items():
        indexed = program.model.organization.get(f, "").startswith("INDEX")
        # An empty flat file is a perfectly good sequential file and a
        # meaningless indexed one, so only the sequential opens succeed -
        # which is exactly what the compiled program sees.
        # Opening a missing indexed file for input fails; opening it for
        # output creates it. Everything sequential works either way, since
        # an empty flat file was staged.
        missing = "35" if indexed else "00"
        for verb, value in (("OPEN-INPUT", missing), ("OPEN-I-O", missing),
                            ("OPEN-OUTPUT", "00"), ("OPEN-EXTEND", "00"),
                            ("OPEN", missing), ("CLOSE", "00"), ("WRITE", "00"),
                            ("REWRITE", "00"), ("START", "00"),
                            ("READ", missing if indexed else "10")):
            out["%s:%s" % (verb, f)] = {status: value}
    return out


def predicted(path: str, entry: str | None = None) -> list:
    program = load_program(path)
    interp = Interpreter(program, {}, defaults=io_defaults(program))
    start = entry or (program.paragraph_names[0] if program.paragraph_names else "")
    if not start:
        return []
    return interp.run(start).entered


def common_prefix(a: list, b: list) -> int:
    n = 0
    while n < min(len(a), len(b)) and a[n] == b[n]:
        n += 1
    return n


def compare(path: str, verbose: bool = False, copybooks=()) -> dict:
    work = tempfile.mkdtemp(prefix="fl-conf-")
    src = os.path.join(work, os.path.basename(path))
    try:
        untraced = instrument(path, src)
    except Exception as exc:                                   # noqa: BLE001
        return {"program": os.path.basename(path), "note": "parse failed: %s" % exc}

    real, note = compile_and_run(src, work, copybooks, stage_files(path, work))
    if real is None:
        return {"program": os.path.basename(path), "note": note}

    mine = [p for p in predicted(path) if p not in untraced]
    real, mine = real[:LIMIT], mine[:LIMIT]
    n = common_prefix(real, mine)
    result = {
        "program": os.path.basename(path),
        "real_len": len(real), "mine_len": len(mine),
        "agree": n, "identical": real == mine, "note": note,
        "untraced": untraced,
        "first_divergence": None,
    }
    if not result["identical"]:
        result["first_divergence"] = {
            "at": n,
            "real": real[n] if n < len(real) else "(end)",
            "mine": mine[n] if n < len(mine) else "(end)",
            "context_real": real[max(0, n - 3):n + 3],
            "context_mine": mine[max(0, n - 3):n + 3],
        }
    if verbose:
        print("real:", real[:40])
        print("mine:", mine[:40])
    return result


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("programs", nargs="+")
    ap.add_argument("-v", "--verbose", action="store_true")
    ap.add_argument("-I", "--copybooks", action="append", default=[],
                    help="copybook directory (repeatable)")
    args = ap.parse_args(argv)

    rows = [compare(p, args.verbose, args.copybooks) for p in args.programs]
    runnable = [r for r in rows if "real_len" in r]
    identical = [r for r in runnable if r["identical"]]

    print("%-22s %7s %7s %7s  %s" % ("program", "real", "mine", "agree", "verdict"))
    for r in rows:
        if "real_len" not in r:
            print("%-22s %7s %7s %7s  %s" % (r["program"], "-", "-", "-", r["note"]))
            continue
        verdict = "identical" if r["identical"] else (
            "diverges at %d: real=%s mine=%s"
            % (r["first_divergence"]["at"], r["first_divergence"]["real"],
               r["first_divergence"]["mine"]))
        print("%-22s %7d %7d %7d  %s"
              % (r["program"], r["real_len"], r["mine_len"], r["agree"], verdict))

    if runnable:
        print("\n%d/%d runnable programs traced identically"
              % (len(identical), len(runnable)))
    return 0 if len(identical) == len(runnable) else 1


if __name__ == "__main__":
    raise SystemExit(main())
