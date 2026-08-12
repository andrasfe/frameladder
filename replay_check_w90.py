"""Replay verification: does each stored witness recipe, run through a
fresh Interpreter, take the direction it is stored under?

Samples every k-th witness per program (deterministic), rebuilds the
interpreter from nothing but the recipe row, and checks the direction key
appears in the fresh run's own credited directions.
"""
import json
import subprocess
import sys

CBL = "/Users/andraslferenczi/aws-mainframe-modernization-carddemo/app/cbl"
CPY = "/Users/andraslferenczi/aws-mainframe-modernization-carddemo/app/cpy"
PROGRAMS = ["COACTUPC", "COTRN02C", "COUSR00C", "COTRN00C",
            "COMEN01C", "COBIL00C", "COSGN00C", "COCRDUPC"]
STEP = 7          # sample every 7th stored witness

sys.path.insert(0, ".")
from frameladder.cobol import load_program            # noqa: E402
from frameladder.interpreter import Interpreter       # noqa: E402
from frameladder.ledger import Ledger, _KIND          # noqa: E402
from frameladder.conformance_defaults import io_defaults  # noqa: E402

total = ok = 0
for prog_name in PROGRAMS:
    path = "w90_out_%s.jsonl" % prog_name
    subprocess.run(
        [sys.executable, "-m", "frameladder.cli",
         "%s/%s.cbl" % (CBL, prog_name), "--copybooks", CPY, "--json",
         "witnesses", "--out", path],
        capture_output=True, text=True, cwd=".")
    with open(path) as fh:
        rows = [json.loads(line) for line in fh]
    prog = load_program("%s/%s.cbl" % (CBL, prog_name), copybooks=CPY)
    sample = rows[::STEP]
    good = 0
    for row in sample:
        state = row["input_state"]
        interp = Interpreter(prog, dict(state), stubs=row["stubs"],
                             terminals=row["terminals"],
                             defaults=io_defaults(prog, row["world"]))
        trace = interp.run(prog.paragraph_names[0])
        led = Ledger()
        led.credit(trace, state, row["world"], row["stubs"],
                   row["terminals"], "replay")
        key = (row["paragraph"], row["ordinal"], row["kind"],
               bool(row["direction"]))
        if key in led.covered():
            good += 1
    total += len(sample)
    ok += good
    print("%-10s replayed %3d/%3d" % (prog_name, good, len(sample)))
print("reproduction rate: %d/%d = %.1f%%" % (ok, total, 100.0 * ok / total))
