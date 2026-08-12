"""Measure witness coverage over the worst CICS programs. Scratch script."""
import json
import subprocess
import sys

CBL = "/Users/andraslferenczi/aws-mainframe-modernization-carddemo/app/cbl"
CPY = "/Users/andraslferenczi/aws-mainframe-modernization-carddemo/app/cpy"
PROGRAMS = ["COACTUPC", "COTRN02C", "COUSR00C", "COTRN00C",
            "COMEN01C", "COBIL00C", "COSGN00C", "COCRDUPC"]

wit = tot = 0
for prog in PROGRAMS:
    out = subprocess.run(
        [sys.executable, "-m", "frameladder.cli", "%s/%s.cbl" % (CBL, prog),
         "--copybooks", CPY, "--json", "witnesses"],
        capture_output=True, text=True)
    try:
        d = json.loads(out.stdout)
    except Exception:
        print(prog, "FAILED", out.stderr[-300:])
        continue
    wit += d["witnessed"]
    tot += d["directions_total"]
    print("%-10s %4d/%4d = %5.1f%%  (%d runs, %d dedup)"
          % (prog, d["witnessed"], d["directions_total"], d["witness_pct"],
             d["runs"], d["runs_deduplicated"]))
print("pooled     %4d/%4d = %5.1f%%" % (wit, tot, 100.0 * wit / tot))
