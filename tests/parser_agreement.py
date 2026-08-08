"""Compare the built-in parser against pre-parsed cobalt ASTs.

Paragraph names and call edges are what the ladder actually consumes, so
those are what this measures. Run it over every program for which both a
source file and an AST exist.
"""
import glob
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from frameladder import cobol


def edges(program):
    found = set()

    def walk(stmt, para):
        attrs = stmt.get("attributes", {})
        if stmt.get("type") in ("PERFORM", "GO_TO") and attrs.get("target"):
            for t in re.split(r"\s+THRU\s+|\s+THROUGH\s+", attrs["target"]):
                found.add((para, t.strip().upper()))
        for child in stmt.get("children") or []:
            walk(child, para)

    for p in program.paragraphs:
        for stmt in p.get("statements", []):
            walk(stmt, p["name"])
    return found


AST_DIRS = ["/Users/andraslferenczi/specter/examples",
            "/Users/andraslferenczi/specter/specter/experiments/programs/_inputs"]
SRC_DIRS = ["/Users/andraslferenczi/aws-mainframe-modernization-carddemo/app/cbl",
            "/Users/andraslferenczi/specter/specter/experiments/programs/_inputs"]

sources = {}
for d in SRC_DIRS:
    for path in glob.glob(os.path.join(d, "**", "*.[cC][bB][lL]"), recursive=True):
        if os.path.isfile(path):
            sources.setdefault(os.path.basename(path).split(".")[0].upper(), path)

asts = {}
for d in AST_DIRS:
    for path in glob.glob(os.path.join(d, "**", "*.ast"), recursive=True):
        if os.path.isfile(path):
            asts.setdefault(os.path.basename(path).split(".")[0].upper(), path)

names = sorted(set(sources) & set(asts))
print("%-12s %7s %7s %7s   %7s %7s %7s" %
      ("program", "para_mine", "para_ast", "match", "edge_mine", "edge_ast", "recall"))
tot_pr = tot_er = 0.0
rows = 0
for name in names:
    try:
        mine = cobol.load_program(sources[name])
        ref = cobol.load_program(asts[name])
    except Exception as exc:                                   # noqa: BLE001
        print("%-12s  ERROR %s" % (name, exc))
        continue
    pm, pr = set(mine.paragraph_names), set(ref.paragraph_names)
    em, er = edges(mine), edges(ref)
    p_recall = len(pm & pr) / len(pr) if pr else 1.0
    e_recall = len(em & er) / len(er) if er else 1.0
    tot_pr += p_recall
    tot_er += e_recall
    rows += 1
    print("%-12s %7d %7d %6.0f%%   %7d %7d %6.0f%%" %
          (name, len(pm), len(pr), 100 * p_recall, len(em), len(er), 100 * e_recall))
    missing_p = sorted(pr - pm)[:4]
    if missing_p:
        print("             missing paragraphs: %s" % ", ".join(missing_p))
    missing_e = sorted(er - em)[:4]
    if missing_e:
        print("             missing edges: %s" % ", ".join("%s->%s" % e for e in missing_e))
if rows:
    print("\nmean paragraph recall %.1f%%   mean edge recall %.1f%%   (%d programs)"
          % (100 * tot_pr / rows, 100 * tot_er / rows, rows))
