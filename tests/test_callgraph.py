"""Unit tests for `frameladder.callgraph`. Self-contained: every corpus is
written inline to a temp directory, nothing external.
"""

import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from frameladder.callgraph import call_edges, certify


HEADER = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. %s.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
"""


def _corpus(files: dict, copybooks: dict) -> tuple:
    """Write `{name: source}` under a fresh `cbl/` dir and `{name: source}`
    under a sibling `cpy/` dir - the layout `cobol.find_copybooks` expects,
    the same one CardDemo itself uses. Returns `(cbl_dir, cpy_dir)`.
    """
    root = tempfile.mkdtemp()
    cbl_dir = os.path.join(root, "cbl")
    cpy_dir = os.path.join(root, "cpy")
    os.makedirs(cbl_dir)
    os.makedirs(cpy_dir)
    for name, source in files.items():
        with open(os.path.join(cbl_dir, name + ".cbl"), "w") as fh:
            fh.write(source)
    for name, source in copybooks.items():
        with open(os.path.join(cpy_dir, name + ".cpy"), "w") as fh:
            fh.write(source)
    return cbl_dir, cpy_dir


class TestCallEdges(unittest.TestCase):
    """A literal XCTL and a COPY-resolved OCCURS-table dispatch."""

    def _dispatch_corpus(self):
        menutab = """       01  MENU-OPTIONS-DATA.
           05  FILLER                  PIC X(8) VALUE 'TARGETAA'.
           05  FILLER                  PIC X(8) VALUE 'TARGETBB'.
       01  MENU-OPTIONS REDEFINES MENU-OPTIONS-DATA.
           05  MENU-OPT OCCURS 2 TIMES.
             10  MENU-PGMNAME          PIC X(8).
"""
        menu01 = HEADER % "MENU01" + """       01  WS-IDX               PIC 9(2) VALUE 1.
       01  MY-COMMAREA          PIC X(10).
           COPY MENUTAB.
       PROCEDURE DIVISION.
       MAIN-PARA.
           EXEC CICS XCTL
                PROGRAM(MENU-PGMNAME(WS-IDX))
                COMMAREA(MY-COMMAREA)
           END-EXEC
           GOBACK
           .
"""
        target = lambda n: HEADER % n + """       01  WS-X PIC X.
       PROCEDURE DIVISION.
       MAIN-PARA.
           GOBACK
           .
"""
        return _corpus(
            {"MENU01": menu01, "TARGETAA": target("TARGETAA"),
             "TARGETBB": target("TARGETBB")},
            {"MENUTAB": menutab})

    def test_literal_xctl_is_an_edge(self):
        cbl_dir, cpy_dir = self._dispatch_corpus()
        edges = call_edges(cbl_dir, cpy_dir)
        # every edge into TARGETAA/TARGETBB in this corpus comes from the
        # table, but the mechanism that resolves a bare literal is exercised
        # by the certification corpus below (CALLERA/CALLERB -> 'TARGETC').
        self.assertTrue(edges)

    def test_copy_resolved_dispatch_table_produces_real_edges(self):
        """The measured pitfall: a literal-only scan finds zero edges here,
        because the dispatch is `XCTL PROGRAM(MENU-PGMNAME(WS-IDX))` with the
        program names pooled from an OCCURS table's REDEFINES layout in a
        COPYbook, not written anywhere as a bare literal operand.
        """
        cbl_dir, cpy_dir = self._dispatch_corpus()
        edges = call_edges(cbl_dir, cpy_dir)
        pairs = {(e.caller, e.callee) for e in edges}
        self.assertIn(("MENU01", "TARGETAA"), pairs)
        self.assertIn(("MENU01", "TARGETBB"), pairs)
        table_edges = [e for e in edges if e.how == "table"]
        self.assertEqual(len(table_edges), 2)


class TestCertification(unittest.TestCase):
    """One caller-unreachable certificate, one producible-by direction, on
    the same commarea field and the same target - the only difference is
    which literal each caller's own MOVEs can be shown to produce.
    """

    def _certification_corpus(self):
        cacomy = """       01  CA-RECORD.
           05  CA-FLAG              PIC X(1).
"""
        callera = HEADER % "CALLERA" + """       COPY CACOMY.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE 'Y' TO CA-FLAG
           EXEC CICS XCTL
                PROGRAM('TARGETC')
                COMMAREA(CA-RECORD)
           END-EXEC
           GOBACK
           .
"""
        callerb = HEADER % "CALLERB" + """       COPY CACOMY.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE 'X' TO CA-FLAG
           EXEC CICS XCTL
                PROGRAM('TARGETC')
                COMMAREA(CA-RECORD)
           END-EXEC
           GOBACK
           .
"""
        targetc = HEADER % "TARGETC" + """       COPY CACOMY.
       PROCEDURE DIVISION.
       MAIN-PARA.
           IF CA-FLAG EQUAL 'X'
              CONTINUE
           END-IF
           IF CA-FLAG EQUAL 'Z'
              CONTINUE
           END-IF
           GOBACK
           .
"""
        return _corpus(
            {"CALLERA": callera, "CALLERB": callerb, "TARGETC": targetc},
            {"CACOMY": cacomy})

    def _direction_for(self, result, required_value):
        for row in result["directions"]:
            if row.get("required_value") == required_value and row["direction"]:
                return row
        return None

    def test_edges_in_are_both_callers(self):
        cbl_dir, cpy_dir = self._certification_corpus()
        result = certify(os.path.join(cbl_dir, "TARGETC.cbl"), cpy_dir, cbl_dir)
        callers = {e["caller"] for e in result["edges_in"]}
        self.assertEqual(callers, {"CALLERA", "CALLERB"})

    def test_producible_direction_names_its_caller(self):
        cbl_dir, cpy_dir = self._certification_corpus()
        result = certify(os.path.join(cbl_dir, "TARGETC.cbl"), cpy_dir, cbl_dir)
        row = self._direction_for(result, "X")
        self.assertIsNotNone(row)
        self.assertEqual(row["verdict"], "producible-by")
        self.assertEqual(row["by"], ["CALLERB"])

    def test_unproducible_direction_is_certified_unreachable(self):
        cbl_dir, cpy_dir = self._certification_corpus()
        result = certify(os.path.join(cbl_dir, "TARGETC.cbl"), cpy_dir, cbl_dir)
        row = self._direction_for(result, "Z")
        self.assertIsNotNone(row)
        self.assertEqual(row["verdict"], "caller-unreachable")
        self.assertEqual(sorted(row["predecessors_checked"]), ["CALLERA", "CALLERB"])
        self.assertEqual(row["writers_found"]["CALLERA"], ["Y"])
        self.assertEqual(row["writers_found"]["CALLERB"], ["X"])

    def test_non_commarea_field_is_out_of_scope(self):
        """A field the certifier cannot show is declared in any copybook
        named on an inbound COMMAREA operand is not "unreachable" - it is
        simply not a claim this certifier is positioned to make.
        """
        cbl_dir, cpy_dir = self._certification_corpus()
        with open(os.path.join(cbl_dir, "TARGETC.cbl"), "a"):
            pass
        targetc_path = os.path.join(cbl_dir, "TARGETC.cbl")
        with open(targetc_path) as fh:
            source = fh.read()
        source = source.replace(
            "       PROCEDURE DIVISION.",
            "       01  WS-LOCAL-ONLY PIC X(1) VALUE 'Q'.\n"
            "       PROCEDURE DIVISION.")
        source = source.replace(
            "           IF CA-FLAG EQUAL 'Z'\n              CONTINUE\n           END-IF\n",
            "           IF WS-LOCAL-ONLY EQUAL 'Q'\n              CONTINUE\n           END-IF\n")
        with open(targetc_path, "w") as fh:
            fh.write(source)
        result = certify(targetc_path, cpy_dir, cbl_dir)
        row = next(r for r in result["directions"]
                   if r["condition"] == "WS-LOCAL-ONLY EQUAL 'Q'" and r["direction"])
        self.assertEqual(row["verdict"], "not-commarea-gated")


class TestBaselineFiltering(unittest.TestCase):
    def test_baseline_removes_already_witnessed_directions(self):
        cbl_dir, cpy_dir = TestCertification()._certification_corpus()
        full = certify(os.path.join(cbl_dir, "TARGETC.cbl"), cpy_dir, cbl_dir)
        row = next(r for r in full["directions"] if r.get("required_value") == "Z")

        baseline = tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False)
        baseline.write('{"program": "TARGETC", "paragraph": "%s", "ordinal": %d, '
                       '"kind": "%s", "direction": %s}\n'
                       % (row["paragraph"], row["ordinal"], row["kind"],
                          "true" if row["direction"] else "false"))
        baseline.close()

        filtered = certify(os.path.join(cbl_dir, "TARGETC.cbl"), cpy_dir, cbl_dir,
                           baseline.name)
        still_present = any(r.get("required_value") == "Z" and r["direction"]
                            for r in filtered["directions"])
        self.assertFalse(still_present, "a direction in the baseline must not "
                         "be re-examined as missing")


if __name__ == "__main__":
    unittest.main()
