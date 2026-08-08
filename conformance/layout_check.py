"""Compare computed record lengths against what the compiler says."""
import glob, os, re, subprocess, sys, tempfile
sys.path.insert(0, "/Users/andraslferenczi/frameladder")
from frameladder.cobol import parse_data_division
from frameladder.layout import record_layout

CPY = "/Users/andraslferenczi/aws-mainframe-modernization-carddemo/app/cpy"
ok = bad = skipped = 0
misses = []
for path in sorted(glob.glob(os.path.join(CPY, "*"))):
    if not os.path.isfile(path):
        continue
    model = parse_data_division(path)
    roots = [n for n in model.declared if n not in model.parent]
    if not roots:
        continue
    work = tempfile.mkdtemp()
    src = os.path.join(work, "T.cbl")
    body = "".join("           DISPLAY 'LEN %s=' LENGTH OF %s\n" % (r, r)
                   for r in roots)
    with open(src, "w") as fh:
        fh.write("       IDENTIFICATION DIVISION.\n       PROGRAM-ID. T.\n"
                 "       DATA DIVISION.\n       WORKING-STORAGE SECTION.\n"
                 "       COPY %s.\n"
                 "       PROCEDURE DIVISION.\n       A-MAIN.\n%s"
                 "           GOBACK\n           .\n"
                 % (os.path.basename(path).split(".")[0], body))
    proc = subprocess.run(["cobc", "-x", "-I", CPY, src, "-o",
                           os.path.join(work, "t")],
                          capture_output=True, text=True, cwd=work)
    if proc.returncode != 0:
        skipped += len(roots)
        continue
    run = subprocess.run([os.path.join(work, "t")], capture_output=True,
                         text=True, cwd=work)
    real = {m.group(1): int(m.group(2))
            for m in re.finditer(r"LEN ([A-Z0-9-]+)=\s*0*(\d+)", run.stdout)}
    for root, length in real.items():
        mine = record_layout(model, root)[0].length
        if mine == length:
            ok += 1
        else:
            bad += 1
            if len(misses) < 8:
                misses.append((os.path.basename(path), root, mine, length))
print("records checked against GnuCOBOL: %d" % (ok + bad))
print("  lengths agree : %d (%.0f%%)" % (ok, 100 * ok / max(1, ok + bad)))
print("  disagree      : %d" % bad)
print("  not compilable: %d" % skipped)
for m in misses:
    print("   %-16s %-26s mine %5d  real %5d" % m)
