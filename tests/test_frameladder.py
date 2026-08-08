"""Unit tests. Self-contained: COBOL is written inline, nothing external."""

import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from frameladder import cobol, conditions, graph, ir
from frameladder.interpreter import Interpreter, verify
from frameladder.ladder import build_plan


def write(source: str) -> str:
    handle = tempfile.NamedTemporaryFile("w", suffix=".cbl", delete=False)
    handle.write(source)
    handle.close()
    return handle.name


def program(source: str):
    return cobol.load_program(write(source))


HEADER = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
"""


class TestConditions(unittest.TestCase):
    def test_relational_words_without_to(self):
        atoms = conditions.condition_atoms("WS-A EQUAL SPACES")
        self.assertEqual(str(atoms[0][0]), "WS-A = ' '")

    def test_not_equal_and_not_greater(self):
        self.assertEqual(str(conditions.condition_atoms("A NOT EQUAL B")[0][0]),
                         "A != B")
        self.assertEqual(str(conditions.condition_atoms("A NOT GREATER 5")[0][0]),
                         "A <= 5")

    def test_abbreviated_subject(self):
        atoms = conditions.condition_atoms("WS-RC = '00' OR '04'")
        self.assertEqual([str(a[0]) for a in atoms],
                         ["WS-RC = '00'", "WS-RC = '04'"])

    def test_negated_or_becomes_conjunction(self):
        atoms = conditions.condition_atoms("A = 1 OR B = 2", negate=True)
        self.assertEqual(sorted(str(a) for a in atoms[0]), ["A != 1", "B != 2"])

    def test_folded_across_lines(self):
        atoms = conditions.condition_atoms("A > B\nOR (C > D)", negate=True)
        self.assertEqual(sorted(str(a) for a in atoms[0]), ["A <= B", "C <= D"])

    def test_negate_atom_keeps_alternatives(self):
        # NOT(A = X OR A = Y) has to negate both branches, and must not go
        # through text - a level-88 truth value has no surface syntax.
        alt = ir.Atom(ir.Term("var", name="A"), "=", ir.Term("const", value="Y"))
        atom = ir.Atom(ir.Term("var", name="A"), "=", ir.Term("const", value="X"),
                       "", (alt,))
        self.assertEqual(sorted(str(a) for a in ir.negate_atom(atom)),
                         ["A != 'X'", "A != 'Y'"])


class TestParser(unittest.TestCase):
    SRC = HEADER + """       01  WS-FLAG PIC X VALUE 'N'.
       01  WS-REC.
           05  WS-KEY PIC X(4).
       PROCEDURE DIVISION.
       A-MAIN.
           MOVE 'Y' TO WS-FLAG
           IF WS-FLAG = 'Y'
              PERFORM B-DEEP THRU B-EXIT
           ELSE
              MOVE 'N' TO WS-FLAG
           END-IF
           GOBACK
           .
       B-DEEP.
           MOVE 'K' TO WS-KEY
           .
       B-EXIT.
           EXIT
           .
"""

    def setUp(self):
        self.p = program(self.SRC)

    def test_paragraphs(self):
        self.assertEqual(self.p.paragraph_names, ["A-MAIN", "B-DEEP", "B-EXIT"])

    def test_group_containment_and_pic(self):
        self.assertIn("WS-KEY", self.p.model.descendants("WS-REC"))
        self.assertEqual(self.p.model.pic["WS-KEY"], "X(4)")
        self.assertEqual(self.p.model.initial["WS-FLAG"], "N")

    def test_thru_perform_yields_both_endpoints(self):
        g = graph.build_graph(self.p)
        callees = {s.callee for s in g["A-MAIN"]}
        self.assertIn("B-DEEP", callees)
        self.assertIn("B-EXIT", callees)

    def test_else_is_negated_not_inherited(self):
        seen = {}

        def visit(stmt, para, guards, induction, literals):
            if stmt.get("type") == "MOVE" and "'N'" in stmt.get("text", ""):
                seen["guards"] = [str(g) for g in guards]

        graph.walk_guarded(self.p.paragraph("A-MAIN"), visit)
        self.assertEqual(seen.get("guards"), ["WS-FLAG != 'Y'"])


class TestGraph(unittest.TestCase):
    def test_alter_edge_carries_its_arm_guard(self):
        p = program(HEADER + """       01  WS-SEL PIC X(4).
       PROCEDURE DIVISION.
       D-START.
           EVALUATE WS-SEL
             WHEN 'AAAA'
               ALTER D-JUMP TO PROCEED TO D-TWO
               GO TO D-JUMP
             WHEN OTHER
               GO TO D-END
           END-EVALUATE
           .
       D-JUMP.
           GO TO D-ONE
           .
       D-ONE.
           EXIT
           .
       D-TWO.
           EXIT
           .
       D-END.
           GOBACK
           .
""")
        g = graph.build_graph(p)
        alter = [s for s in g["D-START"] if s.callee == "D-TWO"]
        self.assertTrue(alter, "expected a direct edge from the arm that alters")
        self.assertEqual([str(x) for x in alter[0].guards], ["WS-SEL = 'AAAA'"])

    def test_completes_detects_total_escape(self):
        p = program(HEADER + """       01  WS-SEL PIC X(1).
       PROCEDURE DIVISION.
       E-START.
           EVALUATE WS-SEL
             WHEN 'A'
               GO TO E-ONE
             WHEN OTHER
               GO TO E-ONE
           END-EVALUATE
           .
       E-ONE.
           GOBACK
           .
       E-TWO.
           GOBACK
           .
""")
        self.assertFalse(graph.completes(p.paragraph("E-START")["statements"]))
        g = graph.build_graph(p)
        self.assertNotIn("fallthrough", [s.kind for s in g["E-START"]])


class TestLadder(unittest.TestCase):
    def test_guard_lifted_and_verified(self):
        p = program(HEADER + """       01  WS-FLAG PIC X VALUE 'N'.
       PROCEDURE DIVISION.
       F-MAIN.
           IF WS-FLAG = 'Y'
              PERFORM F-DEEP
           END-IF
           GOBACK
           .
       F-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "F-DEEP", entry="F-MAIN")
        self.assertEqual([str(a) for a in plan.atoms], ["WS-FLAG = 'Y'"])
        self.assertTrue(plan.solved)
        self.assertEqual(plan.flat_state(), {"WS-FLAG": "Y"})
        self.assertTrue(verify(p, plan, "F-MAIN")["reached"])

    def test_rendezvous_between_two_producers(self):
        p = program(HEADER + """       01  WS-SEL PIC X(4).
       01  AREA-A PIC X(8).
       01  REC-A PIC X(8).
       01  REC-B PIC X(8).
       PROCEDURE DIVISION.
       G-MAIN.
           MOVE 'AAAA' TO WS-SEL
           CALL 'SUB' USING AREA-A
           MOVE AREA-A TO REC-A
           MOVE 'BBBB' TO WS-SEL
           CALL 'SUB' USING AREA-A
           MOVE AREA-A TO REC-B
           IF REC-A = REC-B
              PERFORM G-DEEP
           END-IF
           GOBACK
           .
       G-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "G-DEEP", entry="G-MAIN")
        self.assertEqual(len(plan.rendezvous), 1)
        left, right, value = plan.rendezvous[0]
        self.assertNotEqual(left, right)
        bound = {b.slot: b.value for b in plan.bindings}
        self.assertEqual(bound[left], value)
        self.assertEqual(bound[right], value)

    def test_alternative_is_revisited_on_conflict(self):
        # H-GATE falls through only if A is not SPACES; H-NEXT is reached only
        # if A is SPACES *or* LOW-VALUES. Committing to SPACES makes this look
        # infeasible; LOW-VALUES satisfies both.
        p = program(HEADER + """       01  WS-A PIC X(4).
       PROCEDURE DIVISION.
       H-MAIN.
           PERFORM H-GATE THRU H-END
           GOBACK
           .
       H-GATE.
           IF WS-A EQUAL SPACES
              GO TO H-END
           END-IF
           .
       H-NEXT.
           IF WS-A EQUAL SPACES OR WS-A EQUAL LOW-VALUES
              GO TO H-TARGET
           END-IF
           .
       H-TARGET.
           EXIT
           .
       H-END.
           EXIT
           .
""")
        plan = build_plan(p, "H-TARGET", entry="H-MAIN")
        values = {b.producer.var: b.value for b in plan.bindings}
        self.assertEqual(values.get("WS-A"), "\x00")

    def test_unreachable_target_is_reported(self):
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       I-MAIN.
           GOBACK
           .
""")
        plan = build_plan(p, "NO-SUCH-PARA", entry="I-MAIN")
        self.assertFalse(plan.solved)
        self.assertEqual(plan.chain, [])


class TestInterpreter(unittest.TestCase):
    def test_perform_thru_runs_the_whole_range(self):
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       J-MAIN.
           PERFORM J-ONE THRU J-THREE
           GOBACK
           .
       J-ONE.
           CONTINUE
           .
       J-TWO.
           CONTINUE
           .
       J-THREE.
           EXIT
           .
""")
        trace = Interpreter(p, {}, sequential=False).run("J-MAIN")
        self.assertTrue({"J-ONE", "J-TWO", "J-THREE"} <= trace.entered_set)

    def test_alter_redirects_the_goto(self):
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       K-MAIN.
           ALTER K-JUMP TO PROCEED TO K-TWO
           PERFORM K-JUMP
           GOBACK
           .
       K-JUMP.
           GO TO K-ONE
           .
       K-ONE.
           GOBACK
           .
       K-TWO.
           GOBACK
           .
""")
        trace = Interpreter(p, {}, sequential=False).run("K-MAIN")
        self.assertIn("K-TWO", trace.entered_set)
        self.assertNotIn("K-ONE", trace.entered_set)

    def test_stub_outcome_then_terminal(self):
        p = program(HEADER + """       01  WS-RC PIC XX.
       01  AREA-A PIC X(4).
       PROCEDURE DIVISION.
       L-MAIN.
           CALL 'SUB' USING AREA-A
           CALL 'SUB' USING AREA-A
           GOBACK
           .
""")
        interp = Interpreter(p, {},
                             stubs={"CALL:SUB": [{"when": {}, "set": {"AREA-A": "AAAA"}}]},
                             terminals={"CALL:SUB": {"AREA-A": "ZZZZ"}})
        interp.run("L-MAIN")
        # First call takes the planned outcome, second falls to the terminal.
        self.assertEqual(interp.state["AREA-A"], "ZZZZ")

    def test_runaway_is_named_not_timed_out(self):
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       M-MAIN.
           GO TO M-LOOP
           .
       M-LOOP.
           GO TO M-LOOP
           .
""")
        trace = Interpreter(p, {}, sequential=False).run("M-MAIN")
        self.assertEqual(trace.runaway, "M-LOOP")


if __name__ == "__main__":
    unittest.main()


class TestSynergies(unittest.TestCase):
    """Constraint shapes where the relation is fixed but the values are free,
    plus the cases where the answer is a proof rather than a plan."""

    def test_boolean_is_not_arithmetic(self):
        # bool subclasses int in Python, so negating a truth value used to
        # produce 2 - which is not a value any COBOL field can hold.
        from frameladder.ladder import witness
        self.assertIs(witness("!=", ir.Term("const", value=True), set()), False)

    def test_separation_between_two_produced_values(self):
        p = program(HEADER + """       01  WS-SEL PIC X(4).
       01  AREA-A PIC X(4).
       01  REC-A PIC X(4).
       01  REC-B PIC X(4).
       PROCEDURE DIVISION.
       N-MAIN.
           MOVE 'AAAA' TO WS-SEL
           CALL 'SUB' USING AREA-A
           MOVE AREA-A TO REC-A
           MOVE 'BBBB' TO WS-SEL
           CALL 'SUB' USING AREA-A
           MOVE AREA-A TO REC-B
           IF REC-A NOT EQUAL REC-B
              PERFORM N-DEEP
           END-IF
           GOBACK
           .
       N-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "N-DEEP", entry="N-MAIN")
        self.assertTrue(plan.rendezvous, "expected a constructed pair")
        values = [b.value for b in plan.bindings]
        self.assertEqual(len(set(values)), 2, "the two sides must differ")

    def test_ordering_between_two_produced_values(self):
        p = program(HEADER + """       01  WS-LO PIC 9(4).
       01  WS-HI PIC 9(4).
       PROCEDURE DIVISION.
       O-MAIN.
           IF WS-HI GREATER WS-LO
              PERFORM O-DEEP
           END-IF
           GOBACK
           .
       O-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "O-DEEP", entry="O-MAIN")
        state = plan.flat_state()
        self.assertGreater(state["WS-HI"], state["WS-LO"])
        self.assertTrue(verify(p, plan, "O-MAIN")["reached"])

    def test_file_status_is_an_output_of_its_io(self):
        src = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INFILE
                  FILE STATUS IS WS-ST.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-REC PIC X(80).
       WORKING-STORAGE SECTION.
       01  WS-ST PIC XX.
       PROCEDURE DIVISION.
       P-MAIN.
           READ IN-FILE
           GOBACK
           .
"""
        p = program(src)
        self.assertEqual(p.model.file_status.get("IN-FILE"), "WS-ST")
        self.assertIn("IN-REC", p.model.fd_records.get("IN-FILE", []))
        from frameladder.ladder import analyse
        _graph, prov = analyse(p)
        self.assertEqual(prov.producer("WS-ST").kind, "stub")

    def test_two_values_for_one_read_are_a_sequence(self):
        # '00' for the record and '10' at end of file is how every COBOL read
        # loop works; treating the second as a conflict makes it unsolvable.
        src = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INFILE
                  FILE STATUS IS WS-ST.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-REC PIC X(80).
       WORKING-STORAGE SECTION.
       01  WS-ST PIC XX.
       PROCEDURE DIVISION.
       Q-MAIN.
           READ IN-FILE
           IF WS-ST = '00'
              READ IN-FILE
              IF WS-ST NOT EQUAL '00'
                 PERFORM Q-DEEP
              END-IF
           END-IF
           GOBACK
           .
       Q-DEEP.
           EXIT
           .
"""
        p = program(src)
        plan = build_plan(p, "Q-DEEP", entry="Q-MAIN")
        outcomes = plan.stub_plan().get("READ:IN-FILE", [])
        self.assertGreaterEqual(len(outcomes), 2,
                                "expected an ordered outcome sequence")
        self.assertEqual([o["seq"] for o in outcomes], sorted(o["seq"] for o in outcomes))

    def test_unwritable_variable_gives_an_infeasibility_proof(self):
        # WS-NEVER is declared and never assigned, so demanding two values of
        # it is not a search problem - the chain is dead, and saying so is
        # the useful answer.
        p = program(HEADER + """       01  WS-NEVER PIC X.
       PROCEDURE DIVISION.
       R-MAIN.
           IF WS-NEVER = '0'
              IF WS-NEVER = '1'
                 PERFORM R-DEEP
              END-IF
           END-IF
           GOBACK
           .
       R-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "R-DEEP", entry="R-MAIN")
        self.assertTrue(any("INFEASIBLE" in why
                            for _atom, why in plan.open_obligations),
                        "expected a proof, not a vague failure")

    def test_declared_constant_is_not_a_knob(self):
        p = program(HEADER + """       01  WS-VAL PIC X(4).
       PROCEDURE DIVISION.
       S-MAIN.
           IF WS-VAL = 'ABCD'
              PERFORM S-DEEP
           END-IF
           GOBACK
           .
       S-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "S-DEEP", entry="S-MAIN")
        self.assertEqual(plan.flat_state().get("WS-VAL"), "ABCD")
