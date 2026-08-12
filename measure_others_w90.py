"""Witness coverage on programs outside the target eight (regression check)."""
import json
import subprocess
import sys

CBL = "/Users/andraslferenczi/aws-mainframe-modernization-carddemo/app/cbl"
CPY = "/Users/andraslferenczi/aws-mainframe-modernization-carddemo/app/cpy"
PROGRAMS = [("CBACT01C", "cbl"), ("CBTRN02C", "cbl"), ("CBACT04C", "cbl"),
            ("COUSR01C", "cbl"), ("COCRDSLC", "cbl"), ("COADM01C", "cbl"),
            ("CORPT00C", "cbl"), ("COCRDLIC", "cbl")]

wit = tot = 0
for prog_name, _ in PROGRAMS:
    import os
    path = "%s/%s.cbl" % (CBL, prog_name)
    if not os.path.exists(path):
        path = "%s/%s.CBL" % (CBL, prog_name)
    out = subprocess.run(
        [sys.executable, "-m", "frameladder.cli", path,
         "--copybooks", CPY, "--json", "witnesses"],
        capture_output=True, text=True)
    try:
        d = json.loads(out.stdout)
    except Exception:
        print(prog_name, "FAILED", out.stderr[-200:])
        continue
    wit += d["witnessed"]
    tot += d["directions_total"]
    print("%-10s %4d/%4d = %5.1f%%" % (prog_name, d["witnessed"],
                                       d["directions_total"],
                                       d["witness_pct"]))
print("pooled     %4d/%4d = %5.1f%%" % (wit, tot, 100.0 * wit / tot))
