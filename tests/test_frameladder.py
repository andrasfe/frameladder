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


class TestDivergence(unittest.TestCase):
    """Free values spent on exposing divergence rather than on constants."""

    def test_collation_pairs_cross_class_boundaries(self):
        from frameladder import divergence
        # Verified against GnuCOBOL under both collating sequences: ordering
        # disagrees between EBCDIC and ASCII for exactly these class pairs.
        for low, high in divergence.collation_pairs(1):
            a, b = divergence.char_class(low.value), divergence.char_class(high.value)
            self.assertNotEqual(a, b, "a same-class pair proves nothing")
            self.assertIn(tuple(sorted((a, b))),
                          {tuple(sorted(p)) for p in divergence.UNSTABLE_CLASS_PAIRS})

    def test_boundary_candidates_follow_the_pic(self):
        from frameladder.divergence import boundary_candidates
        text = {c.category for c in boundary_candidates("X(4)")}
        self.assertTrue({"spaces", "low-values", "over-width"} <= text)
        num = {c.category for c in boundary_candidates("S9(3)")}
        self.assertTrue({"zero", "all-nines", "overflow", "negative-max"} <= num)
        # The over-width value must actually exceed the field, or it is not a
        # truncation probe at all.
        over = [c for c in boundary_candidates("X(4)") if c.category == "over-width"]
        self.assertEqual(len(over[0].value), 5)

    def test_candidates_never_break_their_own_constraint(self):
        from frameladder.divergence import candidates_for
        from frameladder.cobol import DataModel
        model = DataModel()
        model.pic["WS-A"] = "X(2)"
        for cand in candidates_for("WS-A", "!=", "AB", model, {"AB", "CD"}, {}):
            self.assertNotEqual(cand.value, "AB",
                                "a candidate that breaks the constraint would "
                                "change which path runs")

    def test_free_and_forced_bindings_are_distinguished(self):
        p = program(HEADER + """       01  WS-F PIC X(2).
       01  WS-G PIC X(2).
       PROCEDURE DIVISION.
       T-MAIN.
           IF WS-F = 'YY'
              IF WS-G NOT EQUAL 'ZZ'
                 PERFORM T-DEEP
              END-IF
           END-IF
           GOBACK
           .
       T-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "T-DEEP", entry="T-MAIN")
        by_var = {b.producer.var: b.free for b in plan.bindings}
        self.assertFalse(by_var["WS-F"], "equality pins the value")
        self.assertTrue(by_var["WS-G"], "disequality leaves it free")

    def test_family_members_all_still_reach_the_target(self):
        from frameladder.ladder import build_family
        p = program(HEADER + """       01  WS-F PIC X(2).
       PROCEDURE DIVISION.
       U-MAIN.
           IF WS-F NOT EQUAL 'ZZ'
              PERFORM U-DEEP
           END-IF
           GOBACK
           .
       U-DEEP.
           EXIT
           .
""")
        family = build_family(p, "U-DEEP", entry="U-MAIN", limit=8,
                              verify_each=lambda pl: verify(p, pl, "U-MAIN")["reached"])
        self.assertGreater(len(family), 1, "expected more than the baseline")
        for member in family:
            self.assertTrue(verify(p, member["plan"], "U-MAIN")["reached"])
        values = {repr(m["plan"].flat_state()) for m in family}
        self.assertEqual(len(values), len(family), "members must differ")

    def test_rendezvous_partners_move_together(self):
        # Changing one side of an agreement without the other would break the
        # constraint that made the slot free.
        from frameladder.ladder import build_family
        p = program(HEADER + """       01  AREA-A PIC X(4).
       01  REC-A PIC X(4).
       01  REC-B PIC X(4).
       PROCEDURE DIVISION.
       V-MAIN.
           CALL 'SUB' USING AREA-A
           MOVE AREA-A TO REC-A
           CALL 'SUB' USING AREA-A
           MOVE AREA-A TO REC-B
           IF REC-A = REC-B
              PERFORM V-DEEP
           END-IF
           GOBACK
           .
       V-DEEP.
           EXIT
           .
""")
        base = build_plan(p, "V-DEEP", entry="V-MAIN")
        self.assertTrue(base.rendezvous)
        for member in build_family(p, "V-DEEP", entry="V-MAIN", limit=6):
            state = member["plan"].flat_state()
            paired = [state[v] for v in ("REC-A", "REC-B", "AREA-A") if v in state]
            self.assertLessEqual(len(set(map(repr, paired))), 1,
                                 "both ends of a rendezvous must hold one value")


class TestLiveness(unittest.TestCase):
    def test_read_before_write_is_live_in(self):
        from frameladder.liveness import live_in
        p = program(HEADER + """       01  WS-IN PIC X(2).
       01  WS-OUT PIC X(2).
       01  WS-TMP PIC X(2).
       PROCEDURE DIVISION.
       W-MAIN.
           MOVE WS-IN TO WS-OUT
           MOVE 'AB' TO WS-TMP
           MOVE WS-TMP TO WS-OUT
           GOBACK
           .
""")
        live = live_in(p, "W-MAIN")
        self.assertIn("WS-IN", live, "read before any write")
        self.assertNotIn("WS-TMP", live, "written before it is read")
        self.assertNotIn("WS-OUT", live, "only ever written")

    def test_live_in_follows_performs(self):
        from frameladder.liveness import live_in
        p = program(HEADER + """       01  WS-DEEP PIC X(2).
       PROCEDURE DIVISION.
       X-MAIN.
           PERFORM X-SUB
           GOBACK
           .
       X-SUB.
           IF WS-DEEP = 'ZZ'
              CONTINUE
           END-IF
           .
""")
        self.assertIn("WS-DEEP", live_in(p, "X-MAIN"),
                      "a callee's inputs are the caller's too")

    def test_verbs_are_not_variables(self):
        from frameladder.liveness import live_in
        p = program(HEADER + """       01  WS-N PIC 9(2).
       PROCEDURE DIVISION.
       Y-MAIN.
           DISPLAY 'HELLO' WS-N
           CALL 'SUBPROG'
           GOBACK
           .
""")
        live = live_in(p, "Y-MAIN")
        self.assertIn("WS-N", live)
        for noise in ("DISPLAY", "CALL", "SUBPROG", "HELLO"):
            self.assertNotIn(noise, live)


class TestWitnessStore(unittest.TestCase):
    def test_longest_prefix_wins(self):
        from frameladder.witness import WitnessStore
        store = WitnessStore()
        store.add(("A",), {"X": 1}, "A")
        store.add(("A", "B"), {"X": 2}, "B")
        found = store.longest_prefix(("A", "B", "C"))
        self.assertEqual(found.chain, ("A", "B"))
        self.assertEqual(store.preferences(("A", "B", "C")), {"X": 2})

    def test_unrelated_chain_gets_nothing(self):
        from frameladder.witness import WitnessStore
        store = WitnessStore()
        store.add(("A", "B"), {"X": 1}, "B")
        self.assertEqual(store.preferences(("Q", "R")), {})

    def test_compiler_confirmation_outranks_interpreter(self):
        from frameladder.witness import WitnessStore
        store = WitnessStore()
        store.add(("A",), {"X": 1}, "A", verified=False)
        store.add(("A",), {"X": 9}, "A", verified=True, source="compiler")
        self.assertEqual(store.entries["A"].state["X"], 9)
        self.assertEqual(store.summary()["compiler_confirmed"], 1)

    def test_preferences_only_move_free_slots(self):
        # A carried value must never override something a constraint decided,
        # or reuse could turn a correct plan into an unreachable one.
        p = program(HEADER + """       01  WS-F PIC X(2).
       01  WS-G PIC X(2).
       PROCEDURE DIVISION.
       Z-MAIN.
           IF WS-F = 'YY'
              IF WS-G NOT EQUAL 'ZZ'
                 PERFORM Z-DEEP
              END-IF
           END-IF
           GOBACK
           .
       Z-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "Z-DEEP", entry="Z-MAIN",
                          preferred={"WS-F": "QQ", "WS-G": "GG"})
        state = plan.flat_state()
        self.assertEqual(state["WS-F"], "YY", "equality must survive a preference")
        self.assertEqual(state["WS-G"], "GG", "a free slot may take one")
        self.assertTrue(verify(p, plan, "Z-MAIN")["reached"])


class TestHeuristics(unittest.TestCase):
    def test_class_condition_is_not_a_relation(self):
        # `IS NOT` matches the relational operators, so without recognising
        # class conditions first this parses as `ACCT-ID != NUMERIC` - which
        # looks plausible and compares against the word NUMERIC.
        from frameladder.conditions import CLASS_OP, CLASS_OP_NOT
        atoms = conditions.condition_atoms("ACCT-ID IS NOT NUMERIC")[0]
        self.assertEqual(atoms[0].op, CLASS_OP_NOT)
        self.assertEqual(atoms[0].rhs.value, "NUMERIC")
        self.assertEqual(atoms[0].lhs.name, "ACCT-ID")
        plain = conditions.condition_atoms("WS-X IS NUMERIC")[0]
        self.assertEqual(plain[0].op, CLASS_OP)
        self.assertEqual(plain[0].lhs.name, "WS-X")

    def test_role_depends_on_name_and_shape_together(self):
        from frameladder.heuristics import semantic_value
        # The same field name at two widths wants two different values, and a
        # validator will reject the other one.
        self.assertEqual(semantic_value("ACCT-OPEN-DATE", "X(8)"), "20250115")
        self.assertEqual(semantic_value("ACCT-OPEN-DATE", "X(10)"), "2025-01-15")
        self.assertEqual(semantic_value("CUST-ADDR-STATE-CD", "X(2)"), "NY")
        self.assertIsNone(semantic_value("WS-FOO", "X(4)"),
                          "an unrecognised name must not be guessed at")

    def test_class_condition_drives_a_conforming_value(self):
        p = program(HEADER + """       01  WS-IN PIC X(4).
       PROCEDURE DIVISION.
       AA-MAIN.
           IF WS-IN IS NUMERIC
              PERFORM AA-DEEP
           END-IF
           GOBACK
           .
       AA-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "AA-DEEP", entry="AA-MAIN")
        value = plan.flat_state()["WS-IN"]
        self.assertTrue(str(value).strip().isdigit(),
                        "a class condition constrains shape, not value")
        self.assertEqual(len(str(value)), 4, "shape follows the PIC")

    def test_negated_class_condition_takes_the_other_shape(self):
        p = program(HEADER + """       01  WS-IN PIC X(4).
       PROCEDURE DIVISION.
       AB-MAIN.
           IF WS-IN IS NOT NUMERIC
              PERFORM AB-DEEP
           END-IF
           GOBACK
           .
       AB-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "AB-DEEP", entry="AB-MAIN")
        self.assertFalse(str(plan.flat_state()["WS-IN"]).strip().isdigit())

    def test_shape_beats_plausibility(self):
        # A realistic date that fails IS NUMERIC is worse than digits that
        # pass: the class test is an obligation the program actually stated.
        from frameladder.heuristics import preferred_value
        shaped = preferred_value("ACCT-OPEN-DATE", "X(10)", klass="NUMERIC")
        self.assertTrue(str(shaped).isdigit())
        plain = preferred_value("ACCT-OPEN-DATE", "X(10)")
        self.assertEqual(plain, "2025-01-15")
