"""Unit tests. Self-contained: COBOL is written inline, nothing external."""

import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from frameladder import cobol, conditions, graph, interpreter, ir
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

    def test_nested_intrinsic_names_the_real_operand(self):
        # `FUNCTION` binds to the token after it. Split on whitespace and the
        # outer call gets a variable named `FUNCTION` and one named `TRIM(X)`,
        # so the field the guard is really about is never named and the
        # condition is undecidable in both directions.
        atom = conditions.condition_atoms(
            "FUNCTION LENGTH(FUNCTION TRIM(WS-NAME)) = 0")[0][0]
        self.assertEqual(atom.lhs.name, "WS-NAME")
        self.assertEqual(atom.lhs.func, "LENGTH")
        self.assertEqual(len(atom.lhs.args), 1)

    def test_intrinsic_arguments_still_split_on_space(self):
        # The rejoin must not swallow the space-as-separator rule the
        # reference manuals use for multi-argument intrinsics.
        self.assertEqual(
            len(conditions.condition_atoms("FUNCTION MOD(A B) = 0")[0][0].lhs.args),
            2)
        maxi = conditions.condition_atoms(
            "FUNCTION MAX(FUNCTION LENGTH(A) FUNCTION LENGTH(B)) = 3")[0][0]
        self.assertEqual(maxi.lhs.func, "MAX")
        self.assertEqual([a.name for a in maxi.lhs.args], ["A", "B"])

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

    def test_thru_perform_enters_the_range_at_its_start(self):
        # `PERFORM B-DEEP THRU B-EXIT` enters at B-DEEP. An edge straight to
        # B-EXIT makes the endpoint independently callable, so a plan reaches
        # an exit paragraph without taking on one obligation from the range -
        # 37 such edges on one program alone. Flow onward through the range is
        # ordinary fall-through, which the graph already models and models
        # better, because it withholds the edge where control does not in fact
        # continue.
        g = graph.build_graph(self.p)
        callees = {s.callee for s in g["A-MAIN"]}
        self.assertIn("B-DEEP", callees)
        self.assertNotIn("B-EXIT", callees)

    def test_the_end_of_a_range_is_still_reachable_through_it(self):
        # Removing the shortcut must not make the endpoint unreachable -
        # only reachable by the work that actually reaches it.
        from frameladder.graph import depths
        g = graph.build_graph(self.p)
        self.assertIn("B-EXIT", depths(g, "A-MAIN"))

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

    def test_unwritable_variable_reports_the_chain_as_unplannable(self):
        # WS-NEVER is declared and never assigned, so demanding two values of
        # it is not a search problem on this chain. Note the scope: the claim
        # is about the chain, not the program. Stated globally it was wrong -
        # on GAM0VII 7 of 24 directions called infeasible were then observed
        # executing, because the obligations came from one route and another
        # route had no opinion about the field.
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
        self.assertTrue(any("no plan on this chain" in why
                            for _atom, why in plan.open_obligations),
                        "expected a specific reason, not a vague failure")

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


PACK = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    "packs", "en-US.json")


class _WithPack(unittest.TestCase):
    """The naming pack is opt-in, so a test about it has to opt in."""

    def setUp(self):
        from frameladder import heuristics
        self._roles = list(heuristics._ROLES)
        self._samples = dict(heuristics._SAMPLES)
        self._words = dict(heuristics._WORDS)
        heuristics.load_pack(PACK)

    def tearDown(self):
        from frameladder import heuristics
        heuristics._ROLES[:] = self._roles
        heuristics._SAMPLES.clear(); heuristics._SAMPLES.update(self._samples)
        heuristics._WORDS.clear(); heuristics._WORDS.update(self._words)


class TestHeuristics(_WithPack):
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


class TestExternalWorld(unittest.TestCase):
    """CALL, file I/O, CICS and SQL - the operations whose outcomes a test
    has to supply because the program cannot produce them itself."""

    def test_cics_operands_are_parenthesised(self):
        from frameladder.provenance import op_key, stub_outputs, exec_selectors
        text = ("EXEC CICS READ DATASET(WS-FILE) INTO(WS-REC) "
                "RIDFLD(WS-KEY) RESP(WS-RESP-CD) END-EXEC")
        self.assertEqual(op_key(text), "EXEC:CICS:READ")
        outputs = stub_outputs(text)
        # RESP is CICS's FILE STATUS: the channel every error path tests.
        self.assertIn("WS-RESP-CD", outputs)
        self.assertIn("WS-REC", outputs)
        # DATASET is a keyword naming the resource, not a variable to set.
        self.assertNotIn("DATASET", outputs)
        self.assertEqual(exec_selectors(text), {"DATASET": "WS-FILE"})

    def test_every_sql_statement_sets_sqlcode(self):
        from frameladder.provenance import stub_outputs
        outputs = stub_outputs("EXEC SQL SELECT NAME INTO :WS-NAME "
                               "FROM CUST WHERE ID = :WS-ID END-EXEC")
        self.assertIn("SQLCODE", outputs, "the DB2 analogue of a file status")
        self.assertIn("WS-NAME", outputs, "host variables receive the result")
        self.assertNotIn("WS-ID", outputs, "a predicate host variable is input")

    def test_open_mode_is_part_of_the_operation(self):
        from frameladder.provenance import op_key
        # Opening a missing file for input fails where opening it for output
        # creates it, so they are different operations with different outcomes.
        self.assertEqual(op_key("OPEN INPUT ACCTFILE-FILE"),
                         "OPEN-INPUT:ACCTFILE-FILE")
        self.assertEqual(op_key("OPEN OUTPUT ACCTFILE-FILE"),
                         "OPEN-OUTPUT:ACCTFILE-FILE")

    def test_file_status_is_an_outcome_not_an_input(self):
        src = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INFILE
                  ORGANIZATION IS SEQUENTIAL
                  FILE STATUS IS WS-ST.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-REC PIC X(80).
       WORKING-STORAGE SECTION.
       01  WS-ST PIC XX.
       PROCEDURE DIVISION.
       AC-MAIN.
           OPEN INPUT IN-FILE
           IF WS-ST = '00'
              PERFORM AC-DEEP
           END-IF
           GOBACK
           .
       AC-DEEP.
           EXIT
           .
"""
        p = program(src)
        plan = build_plan(p, "AC-DEEP", entry="AC-MAIN")
        stubs = plan.stub_plan()
        self.assertIn("OPEN-INPUT:IN-FILE", stubs)
        self.assertEqual(stubs["OPEN-INPUT:IN-FILE"][0]["set"], {"WS-ST": "00"})
        # It must not be presented as something the caller sets directly.
        self.assertNotIn("WS-ST", plan.input_state())

    def test_two_calls_are_told_apart_by_what_selects_them(self):
        p = program(HEADER + """       01  WS-DD PIC X(8).
       01  WS-AREA PIC X(4).
       01  REC-A PIC X(4).
       01  REC-B PIC X(4).
       PROCEDURE DIVISION.
       AD-MAIN.
           MOVE 'FIRST' TO WS-DD
           CALL 'SUB' USING WS-AREA
           MOVE WS-AREA TO REC-A
           MOVE 'SECOND' TO WS-DD
           CALL 'SUB' USING WS-AREA
           MOVE WS-AREA TO REC-B
           IF REC-A = REC-B
              PERFORM AD-DEEP
           END-IF
           GOBACK
           .
       AD-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "AD-DEEP", entry="AD-MAIN")
        whens = [e["when"].get("WS-DD")
                 for e in plan.stub_plan().get("CALL:SUB", [])]
        self.assertEqual(len(set(w for w in whens if w)), 2,
                         "one subprogram, two invocations, two outcomes")


class TestTerminalInput(unittest.TestCase):
    """A field an operation fills is that operation's outcome, and the
    program's spelling of it must not decide which operation gets the credit.

    All three of these were one bug on a screen program: the output map
    redefines the input map, the program clears the output map before
    sending, and the operator's field is refilled by the terminal read. Get
    any of them wrong and the field is never set, so every arm behind it is
    unreachable while the plan reports itself solved.
    """

    SCREEN = HEADER + """       01  IN-AREA.
           05  IN-KEY  PIC X(4).
           05  IN-NAME PIC X(4).
       01  OUT-AREA REDEFINES IN-AREA.
           05  OUT-KEY  PIC X(4).
           05  OUT-NAME PIC X(4).
       01  WS-RC PIC S9(8) COMP.
       01  WS-OTHER PIC X(4).
       PROCEDURE DIVISION.
       AE-MAIN.
           MOVE LOW-VALUES TO OUT-AREA
           EXEC CICS RECEIVE MAP('M1') MAPSET('S1') INTO(IN-AREA)
                RESP(WS-RC) END-EXEC
           IF IN-KEY OF IN-AREA NOT = LOW-VALUES
              PERFORM AE-DEEP
           END-IF
           GOBACK
           .
       AE-DEEP.
           MOVE WS-OTHER TO IN-KEY OF IN-AREA
           GOBACK
           .
"""

    def test_a_qualified_write_and_a_plain_one_are_one_field(self):
        # `MOVE X TO A OF R` files a writer under the qualified spelling and
        # the operation that fills R files one under the declared name. Read
        # apart, the reaching definition is whichever half was spelled.
        from frameladder.ladder import analyse
        p = program(self.SCREEN)
        _graph, prov = analyse(p)
        kinds = {w.kind for w in prov.writes_to("IN-KEY OF IN-AREA")}
        self.assertEqual(kinds, {"MOVE", "STUB"})
        self.assertEqual(kinds, {w.kind for w in prov.writes_to("IN-KEY")})

    def test_the_terminal_read_is_the_producer_of_what_it_fills(self):
        from frameladder.ladder import analyse
        p = program(self.SCREEN)
        _graph, prov = analyse(p)
        made = prov.producer("IN-KEY OF IN-AREA", ("AE-MAIN", 999))
        self.assertEqual(made.kind, "stub")
        self.assertEqual(made.op_key, "EXEC:CICS:RECEIVE")

    def test_a_clause_names_a_resource_not_a_field_to_read(self):
        # `MAP('M1')` discriminates two invocations of one verb. There is no
        # field called MAP, so matching it against the state made every
        # derived CICS outcome silently unmatched - and then replaced by the
        # default, which is invisible from the plan.
        p = program(self.SCREEN)
        plan = build_plan(p, "AE-DEEP", entry="AE-MAIN")
        stubs = plan.stub_plan()
        self.assertIn("EXEC:CICS:RECEIVE", stubs)
        when = stubs["EXEC:CICS:RECEIVE"][0]["when"]
        self.assertEqual({when.get("MAP"), when.get("MAPSET")}, {"M1", "S1"})
        result = verify(p, plan, "AE-MAIN")
        self.assertTrue(result["reached"],
                        "the outcome the plan derived has to be delivered")

    def test_one_delivery_carries_every_field_it_names(self):
        # A read fills a whole record, so bindings that differ by variable and
        # share a position are one outcome. Emitted one entry each they
        # described a call returning one field and then returning again, and
        # the consumer stops at the first match.
        from frameladder.ir import Binding, Plan, Producer
        made = lambda var: Producer("stub", var=var, op_key="READ:F",
                                    discriminators={"WS-DD": "A"})
        plan = Plan("T", ["T"], [], [], [
            Binding("a", made("F-ONE"), 1, "", seq=0),
            Binding("b", made("F-TWO"), 2, "", seq=0),
            Binding("c", made("F-ONE"), 9, "", seq=1),
        ], [], [])
        entries = plan.stub_plan()["READ:F"]
        self.assertEqual([e["set"] for e in entries],
                         [{"F-ONE": 1, "F-TWO": 2}, {"F-ONE": 9}])


class TestDependencies(unittest.TestCase):
    """What routing through a frame obliges a test to control."""

    SRC = HEADER + """       01  WS-F PIC X.
       01  WS-AREA PIC X(4).
       PROCEDURE DIVISION.
       AE-MAIN.
           IF WS-F = 'A'
              PERFORM AE-CHEAP
           ELSE
              PERFORM AE-DEAR
           END-IF
           PERFORM AE-TARGET
           GOBACK
           .
       AE-CHEAP.
           GO TO AE-TARGET
           .
       AE-DEAR.
           PERFORM AE-CALLS
           GO TO AE-TARGET
           .
       AE-CALLS.
           CALL 'SUBONE' USING WS-AREA
           .
       AE-TARGET.
           EXIT
           .
"""

    def setUp(self):
        from frameladder.ladder import analyse
        self.p = program(self.SRC)
        self.graph, self.prov = analyse(self.p)

    def test_reach_is_transitive_not_just_direct(self):
        from frameladder.dependencies import direct_operations, external_reach
        direct = direct_operations(self.p, self.prov)
        reach = external_reach(self.p, self.graph, self.prov)
        # The call lives in AE-CALLS, but AE-DEAR is what commits you to it.
        self.assertIn("AE-CALLS", direct)
        self.assertNotIn("AE-DEAR", direct)
        self.assertIn("CALL:SUBONE", reach["AE-DEAR"])
        self.assertEqual(reach["AE-CHEAP"], set(),
                         "a frame that reaches nothing external costs nothing")

    def test_cycles_do_not_hang_the_fixpoint(self):
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       AF-MAIN.
           PERFORM AF-LOOP
           .
       AF-LOOP.
           CALL 'SUBTWO'
           PERFORM AF-MAIN
           .
""")
        from frameladder.ladder import analyse
        from frameladder.dependencies import external_reach
        graph, prov = analyse(p)
        reach = external_reach(p, graph, prov)
        self.assertIn("CALL:SUBTWO", reach["AF-MAIN"])

    def test_commitments_subtract_what_the_plan_already_supplies(self):
        from frameladder.dependencies import Commitment
        c = Commitment("F", {"CALL:A", "CALL:B"}, {"CALL:A"})
        self.assertEqual(c.uncontrolled, {"CALL:B"})
        self.assertEqual(c.cost, 1)

    def test_routes_are_ranked_by_what_they_commit_you_to(self):
        from frameladder.dependencies import route_options
        options = route_options(self.p, self.graph, self.prov,
                                "AE-MAIN", "AE-TARGET")
        self.assertGreater(len(options), 1)
        costs = [len(o["operations"]) for o in options]
        self.assertEqual(costs, sorted(costs), "cheapest first")
        by_via = {o["via"]: len(o["operations"]) for o in options}
        self.assertLess(by_via.get("AE-CHEAP", 99), by_via.get("AE-DEAR", 0),
                        "the route avoiding the call must rank cheaper")


class TestFaultVocabulary(unittest.TestCase):
    """What an operation is allowed to say went wrong."""

    def _model(self):
        from frameladder.cobol import DataModel
        m = DataModel()
        m.file_status["IN-FILE"] = "WS-ST"
        return m

    def test_channel_comes_from_the_select_not_the_name(self):
        from frameladder.faults import channel_of
        model = self._model()
        self.assertEqual(channel_of("WS-ST", model), "file")
        self.assertEqual(channel_of("SQLCODE", model), "sql")
        # A CICS response field is one the source put in a RESP operand.
        model.cics_resp.add("WS-RESP")
        self.assertEqual(channel_of("WS-RESP", model), "cics")
        # A field that merely looks status-ish is not one; guessing would put
        # file-status codes into fields that are not file statuses.
        self.assertIsNone(channel_of("WS-STATUS-MESSAGE", model))
        # ...and that includes one spelled like a response field. This test
        # asserted the opposite until the suffix match was removed: it was
        # named for the invariant and encoded its violation.
        self.assertIsNone(channel_of("WS-SAVED-RESP", model))

    def test_useful_codes_come_before_obscure_ones(self):
        from frameladder.faults import codes_for
        codes = codes_for("WS-ST", self._model())
        self.assertEqual(codes[0], "00")
        # End-of-file and not-found unlock real code; a duplicate alternate
        # index almost never does.
        self.assertLess(codes.index("10"), codes.index("02"))
        self.assertLess(codes.index("23"), codes.index("02"))

    def test_program_literals_outrank_platform_codes(self):
        from frameladder.faults import enrich_domain
        ordered = enrich_domain("WS-ST", self._model(), {"77"})
        self.assertEqual(ordered[0], "77",
                         "a value the program itself tests is the better choice")
        self.assertIn("10", ordered)

    def test_negation_resolves_to_a_real_status(self):
        src = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INFILE
                  ORGANIZATION IS SEQUENTIAL
                  FILE STATUS IS WS-ST.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-REC PIC X(80).
       WORKING-STORAGE SECTION.
       01  WS-ST PIC XX.
       PROCEDURE DIVISION.
       AG-MAIN.
           READ IN-FILE
           IF WS-ST NOT = '00'
              PERFORM AG-DEEP
           END-IF
           GOBACK
           .
       AG-DEEP.
           EXIT
           .
"""
        p = program(src)
        plan = build_plan(p, "AG-DEEP", entry="AG-MAIN")
        chosen = plan.stub_plan()["READ:IN-FILE"][0]["set"]["WS-ST"]
        # The program names the value to avoid and no alternative, so without
        # a vocabulary the witness invents a string that is not a file status.
        self.assertIn(chosen, {"10", "23", "35", "22", "02", "04"})
        self.assertNotEqual(chosen, "X")

    def test_a_non_status_field_gets_no_codes(self):
        from frameladder.faults import enrich_domain
        model = self._model()
        self.assertEqual(enrich_domain("CUST-FIRST-NAME", model, {"BOB"}), ["BOB"])


class TestGenericity(_WithPack):
    """What the tool knows must come from the program, not from assuming the
    program was written in English by an American bank."""

    def test_no_naming_table_is_consulted_by_default(self):
        from frameladder import heuristics
        heuristics._ROLES.clear()
        heuristics._SAMPLES.clear()
        # With no pack loaded the tool must decline rather than invent: a
        # guess about naming is not knowledge, and it measured as worth zero
        # targets of reachability.
        self.assertIsNone(heuristics.semantic_value("ACCT-OPEN-DATE", "X(10)"))
        self.assertEqual(
            heuristics.semantic_value("ACCT-OPEN-DATE", "X(10)",
                                      evidence={"1999-12-31"}), "1999-12-31",
            "evidence from the program still works with no pack at all")

    def test_the_program_outranks_the_name_table(self):
        from frameladder.heuristics import semantic_value
        # ACCT-OPEN-DATE would get 2025-01-15 from the en-US pack, but if the
        # source compares it against something else, that is a fact rather
        # than an assumption and wins.
        self.assertEqual(semantic_value("ACCT-OPEN-DATE", "X(10)"), "2025-01-15")
        self.assertEqual(
            semantic_value("ACCT-OPEN-DATE", "X(10)", evidence={"1999-12-31"}),
            "1999-12-31")

    def test_evidence_must_fit_the_field(self):
        from frameladder.heuristics import from_evidence
        # A literal too long for the field would be truncated on storage, so
        # it is not usable as the value.
        self.assertIsNone(from_evidence({"TOOLONGVALUE"}, "X(4)"))
        self.assertEqual(from_evidence({"AB", "ABCD"}, "X(4)"), "ABCD")

    def test_non_english_names_work_through_a_pack(self):
        import json
        import tempfile
        from frameladder import heuristics
        # A German estate: GEB-DAT is a date, and nothing in the built-in
        # en-US table says so.
        self.assertIsNone(heuristics.semantic_value("KUNDE-GEB-DAT", "X(8)"))
        pack = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
        json.dump({"roles": {"date": ["GEB-DAT", "DATUM"]},
                   "samples": {"date": {"8": "31121999"}}}, pack)
        pack.close()
        saved_roles = list(heuristics._ROLES)
        saved_samples = dict(heuristics._SAMPLES)
        try:
            heuristics.load_pack(pack.name)
            self.assertEqual(heuristics.role_of("KUNDE-GEB-DAT"), "date")
            self.assertEqual(heuristics.semantic_value("KUNDE-GEB-DAT", "X(8)"),
                             "31121999")
        finally:
            heuristics._ROLES[:] = saved_roles
            heuristics._SAMPLES.clear()
            heuristics._SAMPLES.update(saved_samples)

    def test_status_codes_are_platform_not_program(self):
        from frameladder.cobol import DataModel
        from frameladder.faults import codes_for
        # These are the platform's fixed vocabulary, like HTTP status codes -
        # the one kind of built-in knowledge that is not a guess about naming.
        model = DataModel()
        model.file_status["F"] = "WS-ST"
        self.assertIn("10", codes_for("WS-ST", model))
        self.assertEqual(codes_for("SOME-OTHER-FIELD", model), [],
                         "a field outside a known channel gets no vocabulary")


class TestNameSweep(unittest.TestCase):
    """Names are decided by sweeping this program, not by assuming a prior."""

    def test_sweep_finds_only_what_is_undecided(self):
        from frameladder.cli import build_parser, cmd_names
        p = program(HEADER + """       01  WS-KNOWN PIC X(2).
       01  ACME-WIDGET-KEY PIC X(6).
       PROCEDURE DIVISION.
       AH-MAIN.
           IF WS-KNOWN = 'OK'
              IF ACME-WIDGET-KEY NOT = 'ZZZZZZ'
                 PERFORM AH-DEEP
              END-IF
           END-IF
           GOBACK
           .
       AH-DEEP.
           EXIT
           .
""")
        # Written to the parser's own path so the command sees a real program.
        args = build_parser().parse_args([p.source_path, "names"])
        payload = cmd_names(args)
        tokens = {t["token"] for t in payload["tokens"]}
        # WS-KNOWN is pinned by an equality, so it is not undecided.
        self.assertNotIn("KNOWN", tokens)
        # ACME-WIDGET-KEY is left open by a disequality and its tokens are
        # nothing any English table would carry - which is the point.
        self.assertTrue({"ACME", "WIDGET"} & tokens)

    def test_a_decision_persists_and_removes_the_question(self):
        import tempfile
        from frameladder.cli import build_parser, cmd_names, cmd_bind
        p = program(HEADER + """       01  ACME-WIDGET-KEY PIC X(6).
       PROCEDURE DIVISION.
       AI-MAIN.
           IF ACME-WIDGET-KEY NOT = 'ZZZZZZ'
              PERFORM AI-DEEP
           END-IF
           GOBACK
           .
       AI-DEEP.
           EXIT
           .
""")
        work = tempfile.mkdtemp()
        parser = build_parser()
        before = cmd_names(parser.parse_args([p.source_path, "--work-dir", work,
                                              "names"]))
        self.assertGreater(before["undecided_fields"], 0)
        cmd_bind(parser.parse_args([p.source_path, "--work-dir", work, "bind",
                                    "--bind", "ACME-WIDGET-KEY=W12345",
                                    "--why", "site convention"]))
        after = cmd_names(parser.parse_args([p.source_path, "--work-dir", work,
                                             "names"]))
        self.assertEqual(after["undecided_fields"], 0,
                         "a decision, once made, is data and is not re-asked")

    def test_declared_value_is_a_default_not_a_constraint(self):
        # A VALUE says what the field starts as. It should be preferred, and
        # it must still yield to a constraint that needs something else.
        p = program(HEADER + """       01  WS-F PIC X VALUE 'N'.
       PROCEDURE DIVISION.
       AJ-MAIN.
           IF WS-F = 'Y'
              PERFORM AJ-DEEP
           END-IF
           GOBACK
           .
       AJ-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "AJ-DEEP", entry="AJ-MAIN")
        self.assertEqual(plan.flat_state()["WS-F"], "Y")
        self.assertTrue(verify(p, plan, "AJ-MAIN")["reached"])

    def test_cics_response_constants_are_not_arrays(self):
        # DFHRESP(NOTFND) is a compile-time constant; read as a subscripted
        # name it becomes an array nobody can set.
        term = ir.parse_term("DFHRESP(NOTFND)")
        self.assertEqual(term.kind, "const")
        self.assertEqual(term.value, 13)
        self.assertEqual(ir.parse_term("DFHRESP(NORMAL)").value, 0)
        self.assertEqual(ir.parse_term("WS-TAB(I)").kind, "var")


class TestCopybookDiscovery(unittest.TestCase):
    """A missing copybook is the largest single cause of not knowing a field."""

    def test_conventional_directories_are_found_beside_the_source(self):
        import tempfile
        from frameladder.cobol import find_copybooks
        root = tempfile.mkdtemp()
        src = os.path.join(root, "src")
        os.makedirs(os.path.join(root, "cpy"))
        os.makedirs(src)
        program_path = os.path.join(src, "P.cbl")
        open(program_path, "w").close()
        # Beside the source, and one level up, are both conventional.
        os.makedirs(os.path.join(src, "copybook"))
        found = find_copybooks(program_path)
        self.assertTrue(any(f.endswith("copybook") for f in found))
        self.assertTrue(any(f.endswith("cpy") for f in found))

    def test_a_copybook_supplies_the_shape_the_program_omits(self):
        import tempfile
        root = tempfile.mkdtemp()
        os.makedirs(os.path.join(root, "cpy"))
        with open(os.path.join(root, "cpy", "REC.cpy"), "w") as fh:
            fh.write("       01  CUST-REC.\n"
                     "           05  CUST-GRADE PIC X(3).\n")
        path = os.path.join(root, "P.cbl")
        with open(path, "w") as fh:
            fh.write(HEADER + """       01  WS-X PIC X.
       PROCEDURE DIVISION.
       AK-MAIN.
           IF CUST-GRADE = 'AAA'
              PERFORM AK-DEEP
           END-IF
           GOBACK
           .
       AK-DEEP.
           EXIT
           .
""")
        p = cobol.load_program(path)
        # Without the copybook this field has no PIC at all, and with no PIC
        # there is no width, no sign and nothing to check a candidate against.
        self.assertEqual(p.model.pic.get("CUST-GRADE"), "X(3)")

    def test_an_explicit_directory_still_wins(self):
        import tempfile
        from frameladder.cobol import find_copybooks
        root = tempfile.mkdtemp()
        os.makedirs(os.path.join(root, "cpy"))
        path = os.path.join(root, "P.cbl")
        open(path, "w").close()
        self.assertTrue(find_copybooks(path))


class TestDictionary(unittest.TestCase):
    """The dictionary carries the type, not just the name."""

    def test_usage_is_part_of_the_type(self):
        import tempfile
        # PIC does not determine representation. S9(4) COMP is two binary
        # bytes, COMP-3 is three packed bytes with a sign nibble, DISPLAY is
        # four characters - they compare equal and serialise differently,
        # which is where a migration diverges.
        path = tempfile.NamedTemporaryFile("w", suffix=".cbl", delete=False)
        path.write(HEADER + """       01  WS-BIN  PIC S9(4) COMP.
       01  WS-PACK PIC S9(4) COMP-3.
       01  WS-CHAR PIC S9(4).
       01  WS-ALIAS REDEFINES WS-CHAR PIC X(4).
       01  WS-TAB PIC X(2) OCCURS 5 TIMES.
       PROCEDURE DIVISION.
       AL-MAIN.
           GOBACK
           .
""")
        path.close()
        m = cobol.load_program(path.name).model
        self.assertEqual(m.usage.get("WS-BIN"), "COMP")
        self.assertEqual(m.usage.get("WS-PACK"), "COMP-3")
        self.assertIsNone(m.usage.get("WS-CHAR"))
        self.assertEqual(m.redefines.get("WS-ALIAS"), "WS-CHAR")
        self.assertEqual(m.occurs.get("WS-TAB"), 5)

    def test_packed_decimal_spellings_are_one_type(self):
        import tempfile
        path = tempfile.NamedTemporaryFile("w", suffix=".cbl", delete=False)
        path.write(HEADER + """       01  A PIC S9(4) COMP-3.
       01  B PIC S9(4) USAGE IS COMP-3.
       01  C PIC S9(4) PACKED-DECIMAL.
       PROCEDURE DIVISION.
       AM-MAIN.
           GOBACK
           .
""")
        path.close()
        m = cobol.load_program(path.name).model
        self.assertEqual({m.usage.get(n) for n in "ABC"}, {"COMP-3"})

    def test_every_field_records_where_it_was_declared(self):
        p = program(HEADER + """       01  WS-LOCAL PIC X(2).
       PROCEDURE DIVISION.
       AN-MAIN.
           GOBACK
           .
""")
        self.assertTrue(p.model.origin.get("WS-LOCAL", "").endswith(".cbl"))

    def test_filler_is_not_a_field(self):
        p = program(HEADER + """       01  WS-REC.
           05  FILLER PIC X(4).
           05  WS-REAL PIC X(2).
       PROCEDURE DIVISION.
       AO-MAIN.
           GOBACK
           .
""")
        self.assertIn("WS-REAL", p.model.declared)
        self.assertNotIn("FILLER", p.model.declared)

    def test_not_equals_without_a_space(self):
        # `IF X NOT= Y` is as legal as `NOT =`, and a mandatory space made
        # the whole relation fall through to the bare `=`, yielding a
        # variable called "X NOT".
        for text in ("X NOT= Y", "X NOT = Y", "X IS NOT= Y", "X NOT EQUAL Y"):
            atoms = conditions.condition_atoms(text)[0]
            self.assertEqual(str(atoms[0]), "X != Y", text)


class TestRecordLayout(unittest.TestCase):
    """Offsets and byte lengths - checked against GnuCOBOL in conformance/."""

    def _model(self, text):
        import tempfile
        f = tempfile.NamedTemporaryFile("w", suffix=".cpy", delete=False)
        f.write(text)
        f.close()
        return cobol.parse_data_division(f.name)

    def test_usage_decides_the_width(self):
        from frameladder.layout import byte_length
        # Same PIC, three representations, three sizes. A layout computed from
        # PIC alone puts everything after the first packed field at the wrong
        # offset.
        self.assertEqual(byte_length("S9(4)"), 4)             # DISPLAY
        self.assertEqual(byte_length("S9(4)", "COMP-3"), 3)   # packed
        self.assertEqual(byte_length("S9(4)", "COMP"), 2)     # binary
        self.assertEqual(byte_length("S9(9)", "COMP"), 4)
        self.assertEqual(byte_length("S9(4)V99", "COMP-3"), 4)

    def test_separate_sign_costs_a_byte(self):
        from frameladder.layout import byte_length
        self.assertEqual(byte_length("S9(3)", "", "TRAILING"), 3)
        self.assertEqual(byte_length("S9(3)", "", "TRAILING SEPARATE"), 4)

    def test_redefines_does_not_advance_the_cursor(self):
        from frameladder.layout import record_layout
        m = self._model("""       01  REC.
           05  A PIC X(4).
           05  B REDEFINES A PIC 9(4).
           05  C PIC X(2).
""")
        fields = {f.name: f for f in record_layout(m, "REC")}
        self.assertEqual(fields["A"].offset, 0)
        self.assertEqual(fields["B"].offset, 0, "an alias shares the bytes")
        self.assertEqual(fields["C"].offset, 4, "and does not push C along")
        self.assertEqual(fields["REC"].length, 6)

    def test_occurs_multiplies_the_whole_subtree(self):
        from frameladder.layout import record_layout
        m = self._model("""       01  REC.
           05  T OCCURS 3 TIMES.
               10  X PIC X(2).
               10  Y PIC X(3).
           05  Z PIC X(1).
""")
        fields = {f.name: f for f in record_layout(m, "REC")}
        self.assertEqual(fields["T"].length, 15, "5 bytes, three times")
        self.assertEqual(fields["Z"].offset, 15)

    def test_filler_takes_space_without_being_a_field(self):
        from frameladder.layout import record_layout
        m = self._model("""       01  REC.
           05  A PIC X(2).
           05  FILLER PIC X(5).
           05  B PIC X(3).
""")
        fields = {f.name: f for f in record_layout(m, "REC")}
        self.assertEqual(fields["B"].offset, 7, "the filler is counted")
        self.assertEqual(fields["REC"].length, 10)
        self.assertNotIn("FILLER", m.declared, "but it cannot be referenced")

    def test_values_land_at_their_offsets(self):
        from frameladder.layout import render
        m = self._model("""       01  REC.
           05  A PIC X(3).
           05  B PIC X(4).
""")
        out = render(m, "REC", {"B": "WXYZ"})
        self.assertEqual(len(out), 7)
        self.assertEqual(out[3:7], "WXYZ")


class TestCoverage(unittest.TestCase):
    """Coverage is the union of what a plan set touched, counted by direction."""

    SRC = HEADER + """       01  WS-F PIC X VALUE 'N'.
           88  F-ON  VALUE 'Y'.
           88  F-OFF VALUE 'N', ' '.
       PROCEDURE DIVISION.
       AP-MAIN.
           IF WS-F = 'Y'
              PERFORM AP-YES
           ELSE
              PERFORM AP-NO
           END-IF
           GOBACK
           .
       AP-YES.
           CONTINUE
           .
       AP-NO.
           CONTINUE
           .
"""

    def test_a_direction_is_half_a_branch(self):
        from frameladder.coverage import accumulate, branches_of
        from frameladder.interpreter import Interpreter
        p = program(self.SRC)
        self.assertEqual(len(branches_of(p)), 1)
        one = Interpreter(p, {"WS-F": "Y"}).run("AP-MAIN")
        cov = accumulate(p, [one])
        self.assertEqual(cov.direction_pct, 50.0, "one way is half the branch")
        both = Interpreter(p, {"WS-F": "N"}).run("AP-MAIN")
        cov = accumulate(p, [one, both])
        self.assertEqual(cov.direction_pct, 100.0)

    def test_gaps_separate_never_from_one_way(self):
        from frameladder.coverage import accumulate, missing
        from frameladder.interpreter import Interpreter
        p = program(self.SRC)
        cov = accumulate(p, [Interpreter(p, {"WS-F": "Y"}).run("AP-MAIN")])
        gaps = missing(p, cov)
        self.assertEqual(len(gaps["untouched"]), 0, "it was evaluated")
        self.assertEqual(len(gaps["one_way_only"]), 1, "but only one way")

    def test_negating_a_condition_name_excludes_every_value(self):
        # F-OFF is 'N' or ' '. Making it false must rule out both; ruling out
        # only the first lets the solver pick the other and leave it true.
        from frameladder.ladder import _resolve_88
        atom = ir.Atom(ir.Term("var", name="F-OFF"), "!=",
                       ir.Term("const", value=True))
        p = program(self.SRC)
        resolved = _resolve_88(atom, p.model)
        self.assertEqual(len(resolved), 2)
        self.assertTrue(all(a.op == "!=" for a in resolved))

    def test_a_condition_name_value_may_contain_a_space(self):
        p = program(self.SRC)
        _parent, values = p.model.condition_names["F-OFF"]
        self.assertIn("' '", values, "a quoted space is one value, not two")

    def test_the_entry_paragraph_can_be_planned(self):
        # The entry always runs, so reporting its own decisions unreachable
        # is plainly wrong - and it is where a mainline keeps its dispatch.
        p = program(self.SRC)
        plan = build_plan(p, "AP-MAIN", entry="AP-MAIN")
        self.assertEqual(plan.chain, ["AP-MAIN"])
        self.assertTrue(plan.solved)

    def test_branch_obligations_reach_inside_an_evaluate(self):
        from frameladder.graph import obligations_for_branch
        p = program(HEADER + """       01  WS-S PIC X(2).
       PROCEDURE DIVISION.
       AQ-MAIN.
           EVALUATE WS-S
             WHEN 'AA'
               CONTINUE
             WHEN 'BB'
               CONTINUE
           END-EVALUATE
           GOBACK
           .
""")
        line = [s for s in p.paragraph("AQ-MAIN")["statements"]
                if s["type"] == "EVALUATE"][0]["children"][1]["line_start"]
        atoms = obligations_for_branch(p, "AQ-MAIN", line, True)
        rendered = [str(a) for a in atoms]
        self.assertIn("WS-S = 'BB'", rendered, "the arm's own condition")
        # EVALUATE takes the first matching arm, so reaching the second means
        # the first did not match.
        self.assertIn("WS-S != 'AA'", rendered, "and the one before it failed")
        self.assertLess(rendered.index("WS-S = 'BB'"),
                        rendered.index("WS-S != 'AA'"),
                        "the arm's own condition is settled first")


class TestFirstMatch(unittest.TestCase):
    """EVALUATE takes the first arm that matches - a language rule, not a
    property of any program."""

    SRC = HEADER + """       01  WS-A PIC X VALUE 'N'.
           88  A-ON VALUE 'Y'.
       01  WS-B PIC X VALUE 'N'.
           88  B-ON VALUE 'Y'.
       PROCEDURE DIVISION.
       AR-MAIN.
           EVALUATE TRUE
             WHEN A-ON
               PERFORM AR-FIRST
             WHEN B-ON
               PERFORM AR-SECOND
           END-EVALUATE
           GOBACK
           .
       AR-FIRST.
           CONTINUE
           .
       AR-SECOND.
           CONTINUE
           .
"""

    def test_a_later_arm_requires_the_earlier_ones_to_fail(self):
        from frameladder.graph import obligations_for_branch
        p = program(self.SRC)
        arms = [s for s in p.paragraph("AR-MAIN")["statements"]
                if s["type"] == "EVALUATE"][0]["children"]
        atoms = [str(a) for a in
                 obligations_for_branch(p, "AR-MAIN", arms[1]["line_start"], True)]
        self.assertIn("B-ON = True", atoms)
        self.assertIn("A-ON != True", atoms,
                      "without this the second arm looks reachable on its own")

    def test_the_first_arm_needs_nothing_before_it(self):
        from frameladder.graph import obligations_for_branch
        p = program(self.SRC)
        arms = [s for s in p.paragraph("AR-MAIN")["statements"]
                if s["type"] == "EVALUATE"][0]["children"]
        atoms = [str(a) for a in
                 obligations_for_branch(p, "AR-MAIN", arms[0]["line_start"], True)]
        self.assertEqual(atoms, ["A-ON = True"])

    def test_the_second_arm_is_actually_reachable(self):
        from frameladder.graph import obligations_for_branch
        p = program(self.SRC)
        arms = [s for s in p.paragraph("AR-MAIN")["statements"]
                if s["type"] == "EVALUATE"][0]["children"]
        extra = obligations_for_branch(p, "AR-MAIN", arms[1]["line_start"], True)
        plan = build_plan(p, "AR-MAIN", entry="AR-MAIN", extra=extra)
        state = plan.flat_state()
        self.assertEqual(state.get("WS-B"), "Y")
        self.assertNotEqual(state.get("WS-A"), "Y")
        from frameladder.interpreter import Interpreter
        entered = Interpreter(p, plan.flat_state()).run("AR-MAIN").entered_set
        self.assertIn("AR-SECOND", entered, "the second arm must actually run")
        self.assertNotIn("AR-FIRST", entered, "and the first must not")


class TestCopyExpansion(unittest.TestCase):
    """COPY ... REPLACING is how one copybook becomes many paragraphs."""

    def _program_with_copybook(self, member: str, body: str, main: str):
        import tempfile
        root = tempfile.mkdtemp()
        os.makedirs(os.path.join(root, "cpy"))
        with open(os.path.join(root, "cpy", member + ".cpy"), "w") as fh:
            fh.write(body)
        path = os.path.join(root, "P.cbl")
        with open(path, "w") as fh:
            fh.write(main)
        return cobol.load_program(path)

    def test_replacing_produces_real_branches(self):
        from frameladder.coverage import branches_of
        p = self._program_with_copybook(
            "CHK",
            "           IF FLG-(NAME1)-BAD\n"
            "              CONTINUE\n"
            "           END-IF\n",
            HEADER + """       01  WS-X PIC X.
       PROCEDURE DIVISION.
       AS-MAIN.
           COPY CHK REPLACING ==(NAME1)== BY ==ALPHA==.
           COPY CHK REPLACING ==(NAME1)== BY ==BETA==.
           GOBACK
           .
""")
        conditions = [b.condition for b in branches_of(p)]
        # Unexpanded, this paragraph has no branches at all and the coverage
        # denominator silently understates the program.
        self.assertIn("FLG-ALPHA-BAD", " ".join(conditions))
        self.assertIn("FLG-BETA-BAD", " ".join(conditions))
        self.assertEqual(len(conditions), 2)

    def test_an_unresolvable_copy_is_dropped_not_guessed(self):
        p = program(HEADER + """       01  WS-X PIC X.
       PROCEDURE DIVISION.
       AT-MAIN.
           COPY NOSUCHMEMBER.
           GOBACK
           .
""")
        self.assertIn("AT-MAIN", p.paragraph_names)


class TestFigurativeValues(unittest.TestCase):
    def test_value_low_values_is_not_the_word(self):
        # `VALUE LOW-VALUES` names a figurative constant. Storing the ten
        # letters makes every later comparison against it wrong - and wrong
        # in the flattering direction, since conditions start matching that
        # should not.
        p = program(HEADER + """       01  WS-A PIC X(4) VALUE LOW-VALUES.
       01  WS-B PIC X(4) VALUE SPACES.
       01  WS-C PIC 9(2) VALUE ZERO.
       01  WS-D PIC X(2) VALUE 'AB'.
       PROCEDURE DIVISION.
       AU-MAIN.
           GOBACK
           .
""")
        self.assertEqual(p.model.initial["WS-A"], "\x00")
        self.assertEqual(p.model.initial["WS-B"], " ")
        self.assertEqual(p.model.initial["WS-C"], 0)
        self.assertEqual(p.model.initial["WS-D"], "AB")


class TestPerVariableSolving(unittest.TestCase):
    """A variable is the unit that gets solved, not an obligation."""

    def test_two_negations_on_one_field_are_satisfiable(self):
        from frameladder.ladder import constraints_on, solve_variable
        p = program(HEADER + """       01  WS-F PIC X.
           88  F-ZERO  VALUE '0'.
           88  F-BLANK VALUE ' '.
       PROCEDURE DIVISION.
       AV-MAIN.
           IF NOT F-ZERO
              IF NOT F-BLANK
                 PERFORM AV-DEEP
              END-IF
           END-IF
           GOBACK
           .
       AV-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "AV-DEEP", entry="AV-MAIN")
        value = plan.flat_state().get("WS-F")
        # Choosing a value for `!= '0'` in isolation happily returns ' ',
        # which then breaks `!= ' '` and the whole system reports itself
        # infeasible although any third value satisfies both.
        self.assertNotIn(value, ("0", " "))
        self.assertTrue(verify(p, plan, "AV-MAIN")["reached"])

    def test_constraints_are_gathered_per_variable(self):
        from frameladder.ladder import constraints_on
        atoms = [ir.Atom(ir.Term("var", name="X"), "!=", ir.Term("const", value="0")),
                 ir.Atom(ir.Term("var", name="X"), "!=", ir.Term("const", value=" ")),
                 ir.Atom(ir.Term("var", name="Y"), "=", ir.Term("const", value="A"))]
        p = program(HEADER + """       01  WS-Z PIC X.
       PROCEDURE DIVISION.
       AW-MAIN.
           GOBACK
           .
""")
        found = constraints_on(atoms, p.model)
        self.assertEqual(sorted(found["X"]), [("!=", " "), ("!=", "0")])
        self.assertEqual(found["Y"], [("=", "A")])

    def test_a_declared_default_does_not_win_over_the_whole_system(self):
        # WS-F starts as ' ', which satisfies `!= '0'` on its own and breaks
        # `!= ' '`. The default is a preference, not an answer.
        p = program(HEADER + """       01  WS-F PIC X VALUE ' '.
       PROCEDURE DIVISION.
       AX-MAIN.
           IF WS-F NOT = '0'
              IF WS-F NOT = ' '
                 PERFORM AX-DEEP
              END-IF
           END-IF
           GOBACK
           .
       AX-DEEP.
           EXIT
           .
""")
        plan = build_plan(p, "AX-DEEP", entry="AX-MAIN")
        self.assertNotIn(plan.flat_state().get("WS-F"), ("0", " "))
        self.assertTrue(verify(p, plan, "AX-MAIN")["reached"])


class TestDisjunctiveNormalForm(unittest.TestCase):
    """`(A OR B) AND C` is two alternatives, not one.

    Keeping only the first disjunct of each conjunct is a different
    condition, and GnuCOBOL takes the branch the interpreter refused.
    """

    def test_or_inside_and_keeps_both_alternatives(self):
        atoms = conditions.condition_atoms("(A = 1 OR B = 2) AND C = 3")
        self.assertEqual([sorted(str(x) for x in alt) for alt in atoms],
                         [["A = 1", "C = 3"], ["B = 2", "C = 3"]])

    def test_the_interpreter_takes_the_second_disjunct(self):
        p = program(HEADER + """       01  WS-A PIC X VALUE 'N'.
       01  WS-B PIC X VALUE 'Y'.
       01  WS-C PIC X VALUE 'Y'.
       PROCEDURE DIVISION.
       DN-MAIN.
           IF (WS-A = 'Y' OR WS-B = 'Y') AND WS-C = 'Y'
              PERFORM DN-DEEP
           END-IF
           GOBACK
           .
       DN-DEEP.
           EXIT
           .
""")
        trace = Interpreter(p, {}).run("DN-MAIN")
        self.assertTrue(trace.guards[0].result)
        self.assertIn("DN-DEEP", trace.entered_set)

    def test_cross_product_is_capped(self):
        # Six two-way conjuncts is 64 alternatives; seven would be 128 and
        # the extra ones are dropped rather than allowed to dominate a run.
        wide = " AND ".join("(A%d = 1 OR B%d = 2)" % (i, i) for i in range(8))
        self.assertLessEqual(len(conditions.condition_atoms(wide)),
                             conditions.MAX_ALTERNATIVES)


class TestOrigins(unittest.TestCase):
    def test_slice_composes(self):
        from frameladder.origins import Origin
        whole = Origin("REC", 0, None)
        self.assertEqual(whole.slice(4, 24), Origin("REC", 4, 24))
        self.assertEqual(whole.slice(4, 24).slice(2, 4), Origin("REC", 6, 8))

    def test_slice_past_the_end_is_nothing(self):
        from frameladder.origins import Origin
        self.assertIsNone(Origin("REC", 0, 8).slice(9, 12))

    def test_splice_grows_a_short_base(self):
        from frameladder.origins import splice
        self.assertEqual(splice("", 4, 6, "AB"), "    AB")
        self.assertEqual(splice("XXXXXXXX", 2, 4, "ab"), "XXabXXXX")

    def test_a_group_move_relocates_the_obligation(self):
        # The shape that loses every deep target: the entry value of a field
        # is destroyed by a move over the group it lives in. The obligation
        # is not gone, it has moved to a byte range of the source.
        p = program(HEADER + """       01  WS-IN  PIC X(8).
       01  WS-REC.
           05  WS-ONE PIC X(4).
           05  WS-TWO PIC X(4).
       PROCEDURE DIVISION.
       OG-MAIN.
           MOVE WS-IN TO WS-REC
           IF WS-TWO = 'ZZZZ'
              PERFORM OG-DEEP
           END-IF
           GOBACK
           .
       OG-DEEP.
           EXIT
           .
""")
        from frameladder.origins import Origin
        trace = Interpreter(p, {"WS-IN": "AAAAAAAA"}, track_origins=True).run("OG-MAIN")
        self.assertEqual(trace.guards[0].origins["WS-TWO"], Origin("WS-IN", 4, 8))

    def test_a_computed_value_is_opaque(self):
        p = program(HEADER + """       01  WS-N PIC 9(4).
       PROCEDURE DIVISION.
       OP-MAIN.
           ADD 1 TO WS-N
           IF WS-N = 7
              CONTINUE
           END-IF
           GOBACK
           .
""")
        trace = Interpreter(p, {"WS-N": 1}, track_origins=True).run("OP-MAIN")
        self.assertIsNone(trace.guards[0].origins["WS-N"])


class TestLift(unittest.TestCase):
    def _run(self, source, entry, budget=60):
        from frameladder.conformance_defaults import io_defaults, WORLDS
        from frameladder.coverage import accumulate
        from frameladder.lift import lift
        p = program(source)
        result = lift(p, entry, seeds=[({}, w) for w in WORLDS],
                      defaults_for=lambda w: io_defaults(p, w), budget=budget)
        return p, result, accumulate(p, result["traces"])

    def test_it_solves_through_the_write_that_destroyed_the_plan(self):
        source = HEADER + """       01  WS-IN  PIC X(8).
       01  WS-REC.
           05  WS-ONE PIC X(4).
           05  WS-TWO PIC X(4).
       PROCEDURE DIVISION.
       LF-MAIN.
           MOVE WS-IN TO WS-REC
           IF WS-TWO = 'ZZZZ'
              PERFORM LF-DEEP
           END-IF
           GOBACK
           .
       LF-DEEP.
           EXIT
           .
"""
        p, _result, cov = self._run(source, "LF-MAIN")
        self.assertIn("LF-DEEP", cov.paragraphs_hit)
        self.assertEqual(cov.direction_pct, 100.0)

    def test_it_walks_a_chain_of_guards(self):
        # Three gates in a row, each on a different field. Derivation from
        # the entry point has to satisfy all three at once; the frontier
        # search solves one per run and keeps what it had.
        source = HEADER + """       01  WS-A PIC X.
       01  WS-B PIC X.
       01  WS-C PIC X.
       PROCEDURE DIVISION.
       CH-MAIN.
           IF WS-A = 'A'
              IF WS-B = 'B'
                 IF WS-C = 'C'
                    PERFORM CH-DEEP
                 END-IF
              END-IF
           END-IF
           GOBACK
           .
       CH-DEEP.
           EXIT
           .
"""
        _p, _result, cov = self._run(source, "CH-MAIN")
        self.assertIn("CH-DEEP", cov.paragraphs_hit)

    def test_an_input_independent_guard_is_reported_not_retried(self):
        source = HEADER + """       01  WS-N PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
       IN-MAIN.
           MOVE 5 TO WS-N
           IF WS-N = 7
              PERFORM IN-DEEP
           END-IF
           GOBACK
           .
       IN-DEEP.
           EXIT
           .
"""
        _p, result, cov = self._run(source, "IN-MAIN")
        self.assertNotIn("IN-DEEP", cov.paragraphs_hit)
        self.assertEqual(result["stats"]["unliftable"], 1)

    def test_the_same_command_gives_the_same_runs(self):
        source = HEADER + """       01  WS-A PIC X.
       01  WS-B PIC X.
       PROCEDURE DIVISION.
       DT-MAIN.
           IF WS-A = 'A'
              IF WS-B = 'B'
                 CONTINUE
              END-IF
           END-IF
           GOBACK
           .
"""
        first = self._run(source, "DT-MAIN")[2]
        second = self._run(source, "DT-MAIN")[2]
        self.assertEqual(sorted(map(str, first.directions_hit)),
                         sorted(map(str, second.directions_hit)))

    def test_every_run_carries_a_replayable_recipe(self):
        # `on_run` hands back the trace *and* what produced it. The claim it
        # exists for - a lift run starts at entry with an edited entry state,
        # so the recipe replays - is checked here rather than assumed: every
        # recipe re-run through a fresh interpreter takes the same directions.
        from frameladder.conformance_defaults import io_defaults, WORLDS
        from frameladder.lift import direction_key, lift
        p = program(HEADER + """       01  WS-IN  PIC X(8).
       01  WS-REC.
           05  WS-ONE PIC X(4).
           05  WS-TWO PIC X(4).
       PROCEDURE DIVISION.
       RC-MAIN.
           MOVE WS-IN TO WS-REC
           IF WS-TWO = 'ZZZZ'
              PERFORM RC-DEEP
           END-IF
           GOBACK
           .
       RC-DEEP.
           EXIT
           .
""")
        recipes = []
        lift(p, "RC-MAIN", seeds=[({}, w) for w in WORLDS],
             defaults_for=lambda w: io_defaults(p, w), budget=40,
             on_run=lambda *run: recipes.append(run))
        self.assertTrue(recipes)
        for trace, state, world, stubs, terminals in recipes:
            fresh = Interpreter(p, dict(state), stubs=stubs,
                                terminals=terminals,
                                defaults=io_defaults(p, world)).run("RC-MAIN")
            self.assertEqual({direction_key(g) for g in trace.guards},
                             {direction_key(g) for g in fresh.guards})
        # And at least one recipe is the one only the frontier finds: the
        # guard reads bytes the entry state reaches through the group move.
        self.assertTrue(any(
            direction_key(g) == ("RC-MAIN", g.ordinal, "IF", True)
            for trace, *_rest in recipes for g in trace.guards))


class TestWitnessLift(unittest.TestCase):
    """The witness battery's third phase: lift runs, credited via replay."""

    SOURCE = HEADER + """       01  WS-IN  PIC X(8).
       01  WS-REC.
           05  WS-ONE PIC X(4).
           05  WS-TWO PIC X(4).
       PROCEDURE DIVISION.
       WL-MAIN.
           MOVE WS-IN TO WS-REC
           IF WS-TWO = 'ZZZZ'
              PERFORM WL-DEEP
           END-IF
           GOBACK
           .
       WL-DEEP.
           EXIT
           .
"""

    def _witnesses(self, path, *extra):
        from frameladder.cli import build_parser, cmd_witnesses
        args = build_parser().parse_args([path, "--json", "witnesses",
                                          *extra])
        import contextlib
        import io
        with contextlib.redirect_stdout(io.StringIO()):
            return cmd_witnesses(args)

    def test_lift_witnesses_a_direction_the_battery_misses(self):
        # The guard needs mid-run state: the MOVE destroys anything placed
        # in WS-TWO at entry, and WS-IN is compared against nothing so no
        # overlay draws it. Plans and worlds miss the True direction; the
        # frontier search reaches it through the group move's origins, and
        # the witness it leaves must be a recipe that replays.
        p = program(self.SOURCE)
        before = self._witnesses(p.source_path, "--lift", "0")
        self.assertIsNone(before["lift"])
        missing = {(m["paragraph"], m["direction"]) for m in before["missing"]}
        self.assertIn(("WL-MAIN", True), missing)

        after = self._witnesses(p.source_path, "--lift", "40")
        left = {(m["paragraph"], m["direction"]) for m in after["missing"]}
        self.assertNotIn(("WL-MAIN", True), left)
        self.assertGreater(after["witnessed"], before["witnessed"])

    def test_lifted_recipes_reproduce_and_the_rate_is_reported(self):
        p = program(self.SOURCE)
        payload = self._witnesses(p.source_path, "--lift", "40")
        rep = payload["lift"]["reproduction"]
        self.assertGreater(rep["directions_attempted"], 0)
        self.assertEqual(rep["directions_reproduced"],
                         rep["directions_attempted"])
        self.assertEqual(rep["rate_pct"], 100.0)


class TestInspect(unittest.TestCase):
    """INSPECT, against the standard's own rules rather than one corpus."""

    def test_all_counts_every_occurrence(self):
        items = [{"kind": "ALL", "arg": "A", "lo": 0, "hi": 6}]
        self.assertEqual(interpreter.inspect_tally("AABAAB", items), [4])

    def test_all_consumes_what_it_matched(self):
        # 'AA' occurs once in 'AAA': the scan resumes past the match.
        items = [{"kind": "ALL", "arg": "AA", "lo": 0, "hi": 3}]
        self.assertEqual(interpreter.inspect_tally("AAA", items), [1])

    def test_leading_stops_at_the_first_miss(self):
        items = [{"kind": "LEADING", "arg": "A", "lo": 0, "hi": 6}]
        self.assertEqual(interpreter.inspect_tally("AABAAB", items), [2])

    def test_characters_counts_the_region(self):
        items = [{"kind": "CHARACTERS", "arg": "", "lo": 2, "hi": 5}]
        self.assertEqual(interpreter.inspect_tally("ABCDEF", items), [3])

    def test_items_share_one_pass_and_first_match_wins(self):
        items = [{"kind": "ALL", "arg": "AB", "lo": 0, "hi": 6},
                 {"kind": "ALL", "arg": "B", "lo": 0, "hi": 6}]
        # 'ABABBB': AB at 0 and 2, then B at 4 and 5.
        self.assertEqual(interpreter.inspect_tally("ABABBB", items), [2, 2])

    def test_region_after_missing_delimiter_is_empty(self):
        self.assertEqual(interpreter._inspect_region("ABCDEF", None, "/"),
                         (6, 6))
        self.assertEqual(interpreter._inspect_region("AB/DEF", None, "/"),
                         (3, 6))
        self.assertEqual(interpreter._inspect_region("AB/DEF", "/", None),
                         (0, 2))

    def test_replacing_first_retires_and_leading_stops(self):
        first = [{"kind": "FIRST", "arg": "B", "to": "Z", "lo": 0, "hi": 6}]
        self.assertEqual(interpreter.inspect_replace("ABABAB", first), "AZABAB")
        leading = [{"kind": "LEADING", "arg": "0", "to": " ", "lo": 0, "hi": 6}]
        self.assertEqual(interpreter.inspect_replace("00A00B", leading),
                         "  A00B")

    def test_replacement_is_not_rescanned(self):
        items = [{"kind": "ALL", "arg": "A", "to": "B", "lo": 0, "hi": 3}]
        self.assertEqual(interpreter.inspect_replace("AAA", items), "BBB")

    def test_converting_maps_by_position(self):
        self.assertEqual(
            interpreter.inspect_convert("abcde", "abc", "ABC", 0, 5), "ABCde")
        # A one-character target - what a figurative constant gives - applies
        # to every source character.
        self.assertEqual(
            interpreter.inspect_convert("abcde", "abc", " ", 0, 5), "   de")

    def test_parse_picks_up_all_three_formats(self):
        plan = interpreter.parse_inspect(
            "WS-A TALLYING WS-N FOR LEADING 'A' AFTER INITIAL '/' "
            "REPLACING FIRST 'B' BY 'Z' BEFORE INITIAL '#'")
        self.assertEqual(plan["subject"], "WS-A")
        self.assertEqual(plan["tallying"],
                         [{"counter": "WS-N", "kind": "LEADING", "arg": "'A'",
                           "before": None, "after": "'/'"}])
        self.assertEqual(plan["replacing"],
                         [{"kind": "FIRST", "arg": "'B'", "to": "'Z'",
                           "before": "'#'", "after": None}])

    def test_parse_two_counters(self):
        plan = interpreter.parse_inspect(
            "WS-A TALLYING N1 FOR ALL 'A' N2 FOR ALL 'B'")
        self.assertEqual([t["counter"] for t in plan["tallying"]],
                         ["N1", "N2"])

    def test_counter_is_added_to_not_set(self):
        source = HEADER + """       01  WS-A PIC X(4) VALUE 'ABAB'.
       01  WS-N PIC 9(2) VALUE 5.
       PROCEDURE DIVISION.
       IN-MAIN.
           INSPECT WS-A TALLYING WS-N FOR ALL 'A'
           GOBACK
           .
"""
        prog = program(source)
        interp = Interpreter(prog, {})
        interp.run("IN-MAIN")
        self.assertEqual(interp.state["WS-N"], 7)

    def test_numeric_subject_is_scanned_as_its_bytes(self):
        source = HEADER + """       01  WS-V PIC 9(5) VALUE 102.
       01  WS-N PIC 9(2) VALUE 0.
       PROCEDURE DIVISION.
       IN-MAIN.
           INSPECT WS-V TALLYING WS-N FOR ALL '0'
           GOBACK
           .
"""
        prog = program(source)
        interp = Interpreter(prog, {})
        interp.run("IN-MAIN")
        self.assertEqual(interp.state["WS-N"], 3)


class TestSearch(unittest.TestCase):
    """SEARCH and SEARCH ALL. One site in the corpora and the reason to have
    a micro-fixture harness: this measures the language."""

    TABLE = HEADER + """       01  WS-T.
           05  WS-E OCCURS 4 TIMES ASCENDING KEY IS WS-K
               INDEXED BY IX.
               10  WS-K PIC 9(2).
               10  WS-V PIC X(3).
       01  J PIC 9(2) VALUE 0.
       PROCEDURE DIVISION.
       SE-MAIN.
"""

    def test_key_and_index_clauses_are_read(self):
        prog = program(self.TABLE + "           GOBACK\n           .\n")
        self.assertEqual(prog.model.occurs["WS-E"], 4)
        self.assertEqual(prog.model.keys["WS-E"], [("ASCENDING", "WS-K")])
        self.assertEqual(prog.model.indexes["WS-E"], ["IX"])

    def test_descending_and_compound_keys_keep_their_order(self):
        self.assertEqual(
            cobol.occurs_keys("OCCURS 3 ASCENDING KEY IS K1 K2 "
                              "DESCENDING KEY IS K3 INDEXED BY IX"),
            [("ASCENDING", "K1"), ("ASCENDING", "K2"),
             ("DESCENDING", "K3")])
        self.assertEqual(
            cobol.indexed_by("OCCURS 3 INDEXED BY IX IY"), ["IX", "IY"])

    def test_arms_are_parsed_as_decisions(self):
        prog = program(self.TABLE + """           SEARCH WS-E VARYING J
              AT END PERFORM SE-NO
              WHEN WS-K (IX) = 5
                 PERFORM SE-YES
              WHEN WS-K (IX) = 9
                 PERFORM SE-YES
           END-SEARCH
           GOBACK
           .
       SE-YES.
           EXIT
           .
       SE-NO.
           EXIT
           .
""")
        stmt = prog.paragraph("SE-MAIN")["statements"][0]
        self.assertEqual(stmt["type"], "SEARCH")
        self.assertEqual(stmt["attributes"]["table"], "WS-E")
        self.assertEqual(stmt["attributes"]["varying"], "J")
        self.assertFalse(stmt["attributes"]["all"])
        kinds = [c["type"] for c in stmt["children"]]
        self.assertEqual(kinds, ["PHRASE", "WHEN", "WHEN"])
        # Every one of them is a direction a test can go.
        from frameladder.coverage import branches_of
        found = [(b.kind, b.condition) for b in branches_of(prog)
                 if b.paragraph == "SE-MAIN"]
        self.assertEqual(sorted(found), sorted([("PHRASE", "at_end"),
                                                ("WHEN", "WS-K (IX) = 5"),
                                                ("WHEN", "WS-K (IX) = 9")]))

    def _serial(self, start, arm):
        source = self.TABLE + ("""           SET IX TO %d
           SEARCH WS-E VARYING J
              AT END PERFORM SE-NO
              WHEN %s
                 PERFORM SE-YES
           END-SEARCH
           GOBACK
           .
       SE-YES.
           EXIT
           .
       SE-NO.
           EXIT
           .
""" % (start, arm))
        prog = program(source)
        interp = Interpreter(prog, {})
        trace = interp.run("SE-MAIN")
        return trace.entered_set, interp.state

    def test_serial_advances_the_index(self):
        entered, state = self._serial(1, "IX = 3")
        self.assertIn("SE-YES", entered)
        self.assertEqual(state["IX"], 3)
        self.assertEqual(state["J"], 3)

    def test_serial_resumes_from_where_the_index_is(self):
        entered, _state = self._serial(3, "IX = 2")
        self.assertIn("SE-NO", entered)

    def test_at_end_leaves_the_index_past_the_table(self):
        entered, state = self._serial(1, "IX = 9")
        self.assertIn("SE-NO", entered)
        self.assertNotIn("SE-YES", entered)
        self.assertEqual(state["IX"], 5)

    def test_search_all_bisects_and_the_key_decides_the_step(self):
        """The bisection itself, with element reads standing in.

        `SEARCH ALL` has to read the key of the occurrence it is probing, and
        subscripted element access belongs to the storage model rather than to
        this verb. The probe is substituted here so the *search* is what is
        being tested: given a table ordered 2, 4, 6, 8 it must find 6 in two
        probes and report AT END for 5.
        """
        prog = program(self.TABLE + """           SEARCH ALL WS-E
              AT END PERFORM SE-NO
              WHEN WS-K (IX) = %d
                 PERFORM SE-YES
           END-SEARCH
           GOBACK
           .
       SE-YES.
           EXIT
           .
       SE-NO.
           EXIT
           .
""")
        del prog

        table = {1: 2, 2: 4, 3: 6, 4: 8}

        def run_for(wanted):
            fresh = program(self.TABLE + ("""           SEARCH ALL WS-E
              AT END PERFORM SE-NO
              WHEN WS-K (IX) = %d
                 PERFORM SE-YES
           END-SEARCH
           GOBACK
           .
       SE-YES.
           EXIT
           .
       SE-NO.
           EXIT
           .
""" % wanted))
            interp = Interpreter(fresh, {})
            original = interp.value_of

            def value_of(term):
                if term.kind == "var" and term.name == "WS-K" and term.index:
                    return table.get(int(interp.state.get("IX", 1)), 0)
                return original(term)

            interp.value_of = value_of
            trace = interp.run("SE-MAIN")
            return trace.entered_set, interp.state, trace

        entered, state, _t = run_for(6)
        self.assertIn("SE-YES", entered)
        self.assertEqual(state["IX"], 3)
        entered, _state, _t = run_for(2)
        self.assertIn("SE-YES", entered)
        entered, _state, _t = run_for(5)
        self.assertIn("SE-NO", entered)
        self.assertNotIn("SE-YES", entered)

    def test_a_key_step_uses_the_declared_direction(self):
        prog = program(self.TABLE + "           GOBACK\n           .\n")
        interp = Interpreter(prog, {"WS-K": 4})
        self.assertEqual(interp._key_step("WS-K = 9", ["WS-K"],
                                          {"WS-K": "ASCENDING"}), 1)
        self.assertEqual(interp._key_step("WS-K = 1", ["WS-K"],
                                          {"WS-K": "ASCENDING"}), -1)
        self.assertEqual(interp._key_step("WS-K = 9", ["WS-K"],
                                          {"WS-K": "DESCENDING"}), -1)
        # Nothing to bisect on is reported, not guessed at.
        self.assertEqual(interp._key_step("WS-V = 'X'", ["WS-K"],
                                          {"WS-K": "ASCENDING"}), 0)

    def test_a_compound_key_steps_on_the_most_significant_difference(self):
        prog = program(self.TABLE + "           GOBACK\n           .\n")
        keys, way = ["K1", "K2"], {"K1": "ASCENDING", "K2": "ASCENDING"}
        interp = Interpreter(prog, {"K1": 4, "K2": 9})
        # K1 already matches, so K2 decides.
        self.assertEqual(interp._key_step("K1 = 4 AND K2 = 2", keys, way), -1)
        # K1 does not, so K2 is not consulted however it compares.
        self.assertEqual(interp._key_step("K1 = 7 AND K2 = 2", keys, way), 1)
        # The order is the declaration's, not the condition's.
        self.assertEqual(interp._key_step("K2 = 2 AND K1 = 7", keys, way), 1)

    def test_the_side_the_key_is_on_does_not_change_the_step(self):
        prog = program(self.TABLE + "           GOBACK\n           .\n")
        interp = Interpreter(prog, {"WS-K": 4})
        self.assertEqual(interp._key_step("9 = WS-K", ["WS-K"],
                                          {"WS-K": "ASCENDING"}), 1)


class TestOutcomeSequences(unittest.TestCase):
    """An operation returns a sequence, and the sequence is derived."""

    SOURCE = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INF
           ORGANIZATION IS SEQUENTIAL
           FILE STATUS IS IN-STATUS.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-AREA PIC X(12).
       WORKING-STORAGE SECTION.
       01  IN-STATUS PIC X(2) VALUE '00'.
       01  WS-REC.
           05  WS-KEY  PIC 9(4).
           05  WS-KIND PIC X(1).
           05  WS-REST PIC X(7).
       01  WS-PREV PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
       SQ-MAIN.
           OPEN INPUT IN-FILE
           PERFORM UNTIL IN-STATUS = '10'
              READ IN-FILE INTO WS-REC
              IF IN-STATUS = '00'
                 IF WS-KIND = 'X'
                    PERFORM SQ-SPECIAL
                 END-IF
                 IF WS-KEY NOT = WS-PREV
                    PERFORM SQ-BREAK
                 END-IF
                 MOVE WS-KEY TO WS-PREV
              END-IF
           END-PERFORM
           CLOSE IN-FILE
           GOBACK
           .
       SQ-SPECIAL.
           EXIT
           .
       SQ-BREAK.
           EXIT
           .
"""

    def _worlds(self, **kw):
        from frameladder.ladder import analyse
        from frameladder import sequences
        prog = program(self.SOURCE)
        _g, prov = analyse(prog)
        return prog, prov, sequences.sequence_worlds(prog, prov,
                                                     prov.literals, **kw)

    def test_the_read_target_is_the_area_named_in_the_statement(self):
        from frameladder import sequences
        prog, prov, _w = self._worlds()
        self.assertEqual(sequences.read_targets(prog, "IN-FILE"), ["WS-REC"])
        self.assertIn(("WS-REC", "WS-REC"),
                      sequences.fill_layouts(prog, prov, "IN-FILE"))

    def test_a_sequence_ends_in_end_of_file(self):
        _p, _prov, worlds = self._worlds(lengths=(3,))
        self.assertEqual(len(worlds), 1)
        entries = worlds[0]["stubs"]["READ:IN-FILE"]
        self.assertEqual(len(entries), 3)
        self.assertTrue(all(e["set"]["IN-STATUS"] == "00" for e in entries))
        self.assertEqual(worlds[0]["terminals"]["READ:IN-FILE"],
                         {"IN-STATUS": "10"})

    def test_consecutive_records_differ(self):
        _p, _prov, worlds = self._worlds(lengths=(3,))
        images = [e["set"]["WS-REC"]
                  for e in worlds[0]["stubs"]["READ:IN-FILE"]]
        self.assertEqual(len(set(images)), 3)

    def test_the_program_sees_a_control_break_and_an_end(self):
        prog, _prov, worlds = self._worlds(lengths=(3,))
        interp = Interpreter(prog, {}, stubs=worlds[0]["stubs"],
                             terminals=worlds[0]["terminals"],
                             defaults={"OPEN-INPUT:IN-FILE":
                                       {"IN-STATUS": "00"}})
        trace = interp.run("SQ-MAIN")
        self.assertEqual(interp.calls["READ:IN-FILE"], 4)
        self.assertIn("SQ-BREAK", trace.entered_set)
        results = {}
        for event in trace.guards:
            results.setdefault(event.condition, set()).add(bool(event.result))
        # Records, then end of file, in one run: a world that names one status
        # per operation can produce either direction but never both.
        self.assertEqual(results["IN-STATUS = '00'"], {True, False})
        # The payload reached a decision: 'X' is a value the program names, so
        # the rotation puts it on a record and the special path is entered.
        self.assertIn("SQ-SPECIAL", trace.entered_set)

    def test_a_fault_lands_on_the_call_it_names(self):
        from frameladder.ladder import analyse
        from frameladder import sequences
        prog = program(self.SOURCE)
        _g, prov = analyse(prog)
        worlds = sequences.fault_worlds(prog, prov, prov.literals, length=3,
                                        codes=2)
        named = {w["name"]: w for w in worlds}
        self.assertIn("READ:IN-FILE=23@2", named)
        entries = named["READ:IN-FILE=23@2"]["stubs"]["READ:IN-FILE"]
        self.assertEqual([e["set"]["IN-STATUS"] for e in entries],
                         ["00", "23", "00"])
        # The fault is transient: the operation succeeds again afterwards, so
        # what the program does with the later records stays reachable.
        self.assertEqual(named["READ:IN-FILE=23@2"]["terminals"]
                         ["READ:IN-FILE"], {"IN-STATUS": "10"})

    def test_an_operation_issued_once_gets_no_second_position(self):
        from frameladder.ladder import analyse
        from frameladder import sequences
        prog = program(self.SOURCE)
        _g, prov = analyse(prog)
        names = {w["name"] for w in
                 sequences.fault_worlds(prog, prov, prov.literals, codes=1)}
        self.assertTrue(any(n.startswith("OPEN-INPUT:IN-FILE") for n in names))
        self.assertFalse(any(n.startswith("OPEN-INPUT:IN-FILE=") and
                             n.endswith("@2") for n in names))

    def test_an_operation_named_after_its_record_is_still_that_file(self):
        """`WRITE ws-record` names the record, which the standard requires.

        The operation's key is therefore `WRITE:<record>` while the status
        field belongs to the file, and nothing joined the two: the fixed
        worlds build `WRITE:<file>` keys that match no statement, so no world
        could make a WRITE fail and every `IF status NOT = '00'` after one
        had a single reachable direction.
        """
        from frameladder.ladder import analyse
        from frameladder import sequences
        source = self.SOURCE.replace(
            "           CLOSE IN-FILE",
            "           WRITE IN-AREA\n           CLOSE IN-FILE")
        prog = program(source)
        _g, prov = analyse(prog)
        self.assertIn("WRITE:IN-AREA",
                      sequences.file_operations(prog).get("IN-FILE", []))
        names = {w["name"] for w in
                 sequences.fault_worlds(prog, prov, prov.literals, codes=1)}
        self.assertTrue(any(n.startswith("WRITE:IN-AREA=") for n in names))

    def test_sequences_are_the_same_on_every_run(self):
        first = self._worlds(lengths=(1, 2, 3))[2]
        second = self._worlds(lengths=(1, 2, 3))[2]
        self.assertEqual(repr(first), repr(second))

    def test_a_program_with_no_files_gets_no_sequences(self):
        from frameladder.ladder import analyse
        from frameladder import sequences
        prog = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       NF-MAIN.
           GOBACK
           .
""")
        _g, prov = analyse(prog)
        self.assertEqual(sequences.sequence_worlds(prog, prov, prov.literals),
                         [])
        self.assertEqual(sequences.fault_worlds(prog, prov, prov.literals), [])


class TestSequencesOffCorpus(unittest.TestCase):
    """The sequence mechanism on a program neither corpus author wrote.

    It has to be checked somewhere other than where it was built, and the
    unrelated corpus cannot do it: only one of its seventeen programs declares
    a `FILE STATUS` at all and that one was already at 100%. So the check is
    a program written here, in a shape the batch corpus does not use - an
    indexed file read by key with `INVALID KEY`, a `REWRITE` that can be
    rejected, and a counter that only a second record can move.
    """

    SOURCE = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT MASTER-FILE ASSIGN TO MSTR
           ORGANIZATION IS INDEXED
           ACCESS MODE IS RANDOM
           RECORD KEY IS MST-KEY
           FILE STATUS IS MST-STATUS.
       DATA DIVISION.
       FILE SECTION.
       FD  MASTER-FILE.
       01  MST-AREA.
           05  MST-KEY  PIC 9(4).
           05  MST-BODY PIC X(6).
       WORKING-STORAGE SECTION.
       01  MST-STATUS PIC X(2) VALUE '00'.
       01  WS-SEEN    PIC 9(3) VALUE 0.
       01  WS-DONE    PIC X    VALUE 'N'.
           88  ALL-DONE VALUE 'Y'.
       PROCEDURE DIVISION.
       OC-MAIN.
           OPEN I-O MASTER-FILE
           IF MST-STATUS NOT = '00'
              PERFORM OC-OPEN-FAILED
              GOBACK
           END-IF
           PERFORM UNTIL ALL-DONE
              READ MASTER-FILE
                 INVALID KEY PERFORM OC-NOT-FOUND
                 NOT INVALID KEY PERFORM OC-GOT-ONE
              END-READ
              IF MST-STATUS = '10'
                 SET ALL-DONE TO TRUE
              END-IF
           END-PERFORM
           IF WS-SEEN = 2
              PERFORM OC-EXACTLY-TWO
           END-IF
           CLOSE MASTER-FILE
           GOBACK
           .
       OC-GOT-ONE.
           ADD 1 TO WS-SEEN
           REWRITE MST-AREA
           IF MST-STATUS NOT = '00'
              PERFORM OC-REWRITE-FAILED
           END-IF
           .
       OC-NOT-FOUND.
           EXIT
           .
       OC-OPEN-FAILED.
           EXIT
           .
       OC-REWRITE-FAILED.
           EXIT
           .
       OC-EXACTLY-TWO.
           EXIT
           .
"""

    def _cover(self, sequences_on):
        from frameladder.conformance_defaults import io_defaults, WORLDS
        from frameladder.coverage import accumulate
        from frameladder.ladder import analyse
        from frameladder import sequences as seq
        prog = program(self.SOURCE)
        _g, prov = analyse(prog)
        worlds = []
        if sequences_on:
            worlds = (seq.sequence_worlds(prog, prov, prov.literals)
                      + seq.fault_worlds(prog, prov, prov.literals))
        traces = []
        for world in WORLDS:
            interp = Interpreter(prog, {}, defaults=io_defaults(prog, world))
            traces.append(interp.run("OC-MAIN"))
        for world in worlds:
            interp = Interpreter(prog, {}, stubs=world["stubs"],
                                 terminals=world["terminals"],
                                 defaults=io_defaults(prog, world["world"]))
            traces.append(interp.run("OC-MAIN"))
        return prog, accumulate(prog, traces)

    def test_the_fixed_worlds_leave_the_error_paths_dark(self):
        _prog, cov = self._cover(False)
        # "exactly two records" is not a world a fixed outcome can describe -
        # one status per operation gives none, one, or as many as the loop
        # budget allows - and no fixed world names a record-not-found status.
        for dark in ("OC-EXACTLY-TWO", "OC-NOT-FOUND"):
            self.assertNotIn(dark, cov.paragraphs_hit)

    def test_sequences_reach_them(self):
        _prog, cov = self._cover(True)
        # A record, another, then end of file: only a sequence can say "two".
        self.assertIn("OC-EXACTLY-TWO", cov.paragraphs_hit)
        # A failure on one call of an operation that succeeds on the others.
        self.assertIn("OC-REWRITE-FAILED", cov.paragraphs_hit)
        # INVALID KEY is a status the platform fixes, not a name we guessed.
        self.assertIn("OC-NOT-FOUND", cov.paragraphs_hit)
        self.assertIn("OC-OPEN-FAILED", cov.paragraphs_hit)

    def test_sequences_strictly_add(self):
        _p, without = self._cover(False)
        _q, with_them = self._cover(True)
        self.assertTrue(without.directions_hit < with_them.directions_hit)


class TestConditionalPhrases(unittest.TestCase):
    """A phrase is found where it begins, not peeled off the end.

    Peeling works for the first phrase of a statement and silently loses the
    second, because the statement inside the first handler runs to the next
    verb and swallows the keywords on its way.
    """

    def _statement(self, body: str):
        prog = program(HEADER + """       01  A PIC 9(3) VALUE 1.
       PROCEDURE DIVISION.
       CP-MAIN.
""" + body + """           GOBACK
           .
       CP-YES.
           EXIT
           .
       CP-NO.
           EXIT
           .
""")
        return prog, prog.paragraph("CP-MAIN")["statements"][0]

    def test_the_second_phrase_survives_a_perform(self):
        _p, stmt = self._statement("""           ADD 1 TO A
              ON SIZE ERROR PERFORM CP-NO
              NOT ON SIZE ERROR PERFORM CP-YES
           END-ADD
""")
        arms = [(c["attributes"]["phrase"],
                 [g["attributes"].get("target") for g in c["children"]])
                for c in stmt["children"] if c["type"] == "PHRASE"]
        self.assertEqual(arms, [("on_size_error", ["CP-NO"]),
                                ("not_on_size_error", ["CP-YES"])])

    def test_a_condition_keeps_its_own_not(self):
        # `IF A NOT = 1` must not be cut at the NOT: conditions are read with
        # the phrase scan off, and this is what makes that safe.
        _p, stmt = self._statement("""           IF A NOT = 1
              PERFORM CP-NO
           END-IF
""")
        self.assertEqual(stmt["attributes"]["condition"], "A NOT = 1")

    def test_the_handler_the_outcome_selects_is_the_one_that_runs(self):
        prog, _s = self._statement("""           ADD 1 TO A
              ON SIZE ERROR PERFORM CP-NO
              NOT ON SIZE ERROR PERFORM CP-YES
           END-ADD
""")
        interp = Interpreter(prog, {})
        trace = interp.run("CP-MAIN")
        self.assertIn("CP-YES", trace.entered_set)
        self.assertNotIn("CP-NO", trace.entered_set)
        # Both directions are in the denominator, so the arm that did not run
        # has to be recorded as a decision that went the other way.
        phrases = {(g.condition, g.result) for g in trace.guards
                   if g.kind == "PHRASE"}
        self.assertEqual(phrases, {("on_size_error", False),
                                   ("not_on_size_error", True)})

    def test_a_statement_that_ends_the_source_does_not_crash(self):
        # The phrase scan looks one token past the statement; at the end of a
        # paragraph there is no such token. Parsing must not raise - a parse
        # that raises drops the whole program out of every measurement, which
        # is worse than any wrong answer because it looks like a smaller
        # corpus rather than like a bug.
        prog = program(HEADER + """       01  A PIC 9 VALUE 1.
       PROCEDURE DIVISION.
       CP-TAIL.
           DISPLAY A
""")
        self.assertEqual(prog.paragraph("CP-TAIL")["statements"][0]["type"],
                         "DISPLAY")


class TestCapabilityProfile(unittest.TestCase):
    """What the harness can do is a constraint, not a filter applied later."""

    def _plan(self):
        from frameladder.ladder import build_plan
        p = program(HEADER + """       01  WS-IN PIC X.
       PROCEDURE DIVISION.
       CP-MAIN.
           IF WS-IN = 'A'
              PERFORM CP-DEEP
           END-IF
           GOBACK
           .
       CP-DEEP.
           EXIT
           .
""")
        return build_plan(p, "CP-DEEP", entry="CP-MAIN")

    def test_absent_section_states_no_constraint(self):
        from frameladder.capability import load, unrepresentable
        cap = load({"schema_version": "1.0"})
        self.assertTrue(cap.can_inject("ANYTHING"))
        self.assertTrue(cap.can_replay("READ:F"))
        self.assertEqual(unrepresentable(self._plan(), cap), [])

    def test_empty_section_states_it_can_do_none(self):
        # The difference matters: a harness must be able to say "I cannot
        # inject anything, plan around it". Reading an empty list as "no
        # constraint" silently re-enables everything it just ruled out.
        from frameladder.capability import load, unrepresentable
        cap = load({"schema_version": "1.0", "injectable_variables": []})
        self.assertFalse(cap.can_inject("WS-IN"))
        self.assertTrue(unrepresentable(self._plan(), cap),
                        "a plan binding WS-IN cannot be represented")

    def test_reason_names_the_capability_not_the_symptom(self):
        from frameladder.capability import load, unrepresentable
        cap = load({"schema_version": "1.0", "injectable_variables": ["OTHER"]})
        reasons = unrepresentable(self._plan(), cap)
        self.assertTrue(any("WS-IN" in r for r in reasons), reasons)

    def test_a_qualified_name_is_matched_by_its_declaration(self):
        # The harness lists what it declares; a plan may bind the qualified
        # spelling of the same field.
        from frameladder.capability import load
        cap = load({"schema_version": "1.0", "injectable_variables": ["ACCT-ID"]})
        self.assertTrue(cap.can_inject("ACCT-ID OF MAPAI"))

    def test_a_newer_harness_does_not_break_an_older_planner(self):
        from frameladder.capability import load
        cap = load({"schema_version": "1.0", "something_from_the_future": [1]})
        self.assertTrue(cap.stated)

    def test_a_different_major_version_is_refused(self):
        from frameladder.capability import load
        with self.assertRaises(ValueError):
            load({"schema_version": "2.0"})


class TestDirectionResolution(unittest.TestCase):
    """Naming one decision, when the two tools count decisions differently."""

    SRC = HEADER + """       01  WS-A PIC X.
       01  WS-B PIC X.
       PROCEDURE DIVISION.
       DR-MAIN.
           IF WS-A = 'A'
              MOVE 'X' TO WS-B
           END-IF
           IF WS-B = 'B'
              MOVE 'Y' TO WS-A
           END-IF
           IF WS-A = 'C'
              MOVE 'Z' TO WS-B
           END-IF
           GOBACK
           .
"""

    def _program(self):
        return program(self.SRC)

    def _branches(self):
        from frameladder.coverage import branches_of
        return branches_of(self._program())

    def test_a_foreign_ordinal_is_never_read_as_an_identity(self):
        # The failure this module exists to prevent. A harness numbering per
        # (paragraph, kind) calls the third IF ordinal 2; this tool numbers by
        # statement position, where ordinal 2 is a different decision that
        # usually exists. Nothing detects that from the number alone, so the
        # number is not trusted.
        from frameladder.capability import load
        prog, branches = self._program(), self._branches()
        third = branches[2]
        cap = load({"schema_version": "1.0", "uncovered_directions": [
            {"paragraph": "DR-MAIN", "ordinal": 2, "kind": "IF",
             "condition": third.condition, "direction": True}]})
        resolution = cap.resolve_uncovered(prog)
        self.assertEqual(resolution.wanted,
                         {("DR-MAIN", third.ordinal, "IF", True)})
        self.assertTrue(resolution.conflicts,
                        "an ordinal that disagrees with the text is reported")

    def test_our_own_ordinals_are_trusted_when_stamped(self):
        from frameladder.capability import load
        prog, branches = self._program(), self._branches()
        cap = load({"schema_version": "1.0",
                    "ordinal_source": "frameladder",
                    "uncovered_directions": [
                        {"paragraph": "DR-MAIN", "ordinal": branches[1].ordinal,
                         "kind": "IF", "direction": False}]})
        self.assertTrue(cap.trust_ordinals)
        self.assertEqual(cap.resolve_uncovered(prog).wanted,
                         {("DR-MAIN", branches[1].ordinal, "IF", False)})

    def test_the_same_condition_written_differently_still_matches(self):
        from frameladder.capability import load
        prog, branches = self._program(), self._branches()
        cap = load({"schema_version": "1.0", "uncovered_directions": [
            {"paragraph": "dr-main",
             "condition": '( if ws-a is equal to "A" ).',
             "direction": "T"}]})
        resolution = cap.resolve_uncovered(prog)
        self.assertEqual(resolution.wanted,
                         {("DR-MAIN", branches[0].ordinal, "IF", True)})

    def test_no_direction_named_means_both(self):
        # A decision named without a direction is wholly open. Picking one
        # would be a guess that shows up later as a witness on the direction
        # nobody wanted.
        from frameladder.capability import load
        prog, branches = self._program(), self._branches()
        cap = load({"schema_version": "1.0", "uncovered_directions": [
            {"paragraph": "DR-MAIN", "condition": branches[0].condition}]})
        self.assertEqual(cap.resolve_uncovered(prog).wanted,
                         {("DR-MAIN", branches[0].ordinal, "IF", True),
                          ("DR-MAIN", branches[0].ordinal, "IF", False)})

    def test_a_paragraph_alone_is_rejected_not_spread(self):
        # This asserted the opposite until a real integration showed what the
        # spread costs. Targeting every decision in the paragraph looked like
        # the safe direction, and it destroys attribution on the way back: ten
        # distinct internal successes collapsed onto two probes and none could
        # be credited to the entry that asked for it.
        from frameladder.capability import load
        prog = self._program()
        cap = load({"schema_version": "1.0",
                    "uncovered_directions": [{"paragraph": "DR-MAIN"}]})
        resolution = cap.resolve_uncovered(prog)
        self.assertEqual(resolution.wanted, set())
        self.assertEqual(len(resolution.unresolved), 1)
        self.assertIn("names 3 decisions", resolution.unresolved[0]["reason"])

    def test_the_spread_is_still_available_for_coverage_hunting(self):
        # An unattributable hit is still a hit when the goal is coverage
        # rather than answering a specific probe.
        from frameladder.capability import load
        prog = self._program()
        cap = load({"schema_version": "1.0",
                    "uncovered_directions": [{"paragraph": "DR-MAIN"}]})
        resolution = cap.resolve_uncovered(prog, strict=False)
        self.assertEqual(len(resolution.wanted), 6)   # 3 decisions, both ways

    def test_a_paragraph_with_one_decision_is_not_ambiguous(self):
        from frameladder.capability import load
        prog = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       SD-MAIN.
           IF WS-A = 'A'
              CONTINUE
           END-IF
           GOBACK
           .
""")
        cap = load({"schema_version": "1.0",
                    "uncovered_directions": [{"paragraph": "SD-MAIN"}]})
        self.assertEqual(len(cap.resolve_uncovered(prog).wanted), 2)

    def test_an_unknown_paragraph_is_reported_not_dropped(self):
        from frameladder.capability import load
        prog = self._program()
        cap = load({"schema_version": "1.0", "uncovered_directions": [
            {"paragraph": "NO-SUCH-PARA", "condition": "X = 1"}]})
        resolution = cap.resolve_uncovered(prog)
        self.assertEqual(resolution.wanted, set())
        self.assertEqual(len(resolution.unresolved), 1)
        self.assertIn("no such paragraph", resolution.unresolved[0]["reason"])

    def test_a_probe_id_survives_the_round_trip(self):
        # The harness must be able to join results back to its own identity
        # without either side adopting the other's numbering.
        from frameladder.capability import load
        prog, branches = self._program(), self._branches()
        cap = load({"schema_version": "1.0", "uncovered_directions": [
            {"paragraph": "DR-MAIN", "condition": branches[0].condition,
             "direction": True, "probe_id": "@@B:41:T"}]})
        matches = cap.resolve_uncovered(prog).matches
        self.assertEqual([m.probe for m in matches], ["@@B:41:T"])

    def test_kind_aliases_are_accepted(self):
        from frameladder.directions import normalize_kind
        self.assertEqual(normalize_kind("EVALUATE"), "WHEN")
        self.assertEqual(normalize_kind("PERFORM UNTIL"), "LOOP")
        self.assertEqual(normalize_kind("AT END"), "PHRASE")

    def test_a_profile_for_another_program_is_reported(self):
        # Paragraph names repeat across a shop's programs, so a mismatched
        # profile resolves rather than fails: COTRN02C's work list run against
        # COSGN00C matched 16 of 40 entries and exported 7 meaningless
        # candidates before this said anything.
        from frameladder.capability import load
        from frameladder.directions import program_mismatch
        prog = self._program()
        cap = load({"schema_version": "1.0", "program": "SOME-OTHER-PGM"})
        self.assertIn("SOME-OTHER-PGM", program_mismatch(cap, prog))

    def test_a_spelling_difference_is_not_a_mismatch(self):
        # The two sides disagree about what a program is called - a file stem,
        # a PROGRAM-ID, a member name, with or without an extension - and
        # crying wolf on that would train the reader to ignore the warning.
        from frameladder.capability import load
        from frameladder.directions import program_mismatch
        prog = self._program()
        for spelling in (prog.name, prog.name + ".cbl", prog.name.lower(),
                         "/some/path/" + prog.name + ".CBL"):
            cap = load({"schema_version": "1.0", "program": spelling})
            self.assertEqual(program_mismatch(cap, prog), "", spelling)

    def test_no_program_stated_is_not_a_mismatch(self):
        from frameladder.capability import load
        from frameladder.directions import program_mismatch
        cap = load({"schema_version": "1.0"})
        self.assertEqual(program_mismatch(cap, self._program()), "")


class TestDirectionVerification(unittest.TestCase):
    """Reaching a paragraph is not the request.

    The request is that one decision goes one way. A run can enter the
    paragraph without evaluating that decision, evaluate it the other way, or
    stop on a limit before arriving - and all three were reported as exported
    candidates until this existed. On COTRN02C it caught one of ten.
    """

    SRC = HEADER + """       01  WS-A PIC X.
       01  WS-B PIC X.
       PROCEDURE DIVISION.
       DV-MAIN.
           IF WS-A = 'A'
              PERFORM DV-INNER
           END-IF
           GOBACK
           .
       DV-INNER.
           IF WS-B = 'B'
              MOVE 'Z' TO WS-A
           END-IF
           GOBACK
           .
"""

    def _branch(self, prog, paragraph, index=0):
        from frameladder.coverage import branches_of
        hits = [b for b in branches_of(prog) if b.paragraph == paragraph]
        return hits[index]

    def _verify(self, prog, plan, branch, direction):
        from frameladder.cli import _verify_direction
        return _verify_direction(prog, plan, branch, direction,
                                 prog.paragraph_names[0])

    def test_the_requested_direction_is_confirmed_by_running_it(self):
        from frameladder.ladder import plan_for_branch
        prog = program(self.SRC)
        branch = self._branch(prog, "DV-INNER")
        plan = plan_for_branch(prog, "DV-INNER", branch.line, True,
                               entry="DV-MAIN", ordinal=branch.ordinal)
        verdict, _detail = self._verify(prog, plan, branch, True)
        self.assertEqual(verdict, "verified")

    def test_a_plan_that_takes_the_other_way_is_not_a_success(self):
        # The plan is built for True and checked against False, which is the
        # shape of the defect: solved, representable, reaches the paragraph,
        # and covers the direction nobody asked for.
        from frameladder.ladder import plan_for_branch
        prog = program(self.SRC)
        branch = self._branch(prog, "DV-INNER")
        plan = plan_for_branch(prog, "DV-INNER", branch.line, True,
                               entry="DV-MAIN", ordinal=branch.ordinal)
        verdict, detail = self._verify(prog, plan, branch, False)
        self.assertEqual(verdict, "wrong_direction")
        self.assertIn("DV-INNER", detail)

    def test_never_entering_the_paragraph_is_its_own_disposition(self):
        # Distinct from wrong_direction on purpose: this one is fixed by
        # routing, that one by the solver.
        from frameladder.ir import Plan
        prog = program(self.SRC)
        branch = self._branch(prog, "DV-INNER")
        empty = Plan(target="DV-INNER", chain=[], edges=[], atoms=[],
                     bindings=[], rendezvous=[], open_obligations=[])
        verdict, detail = self._verify(prog, empty, branch, True)
        self.assertEqual(verdict, "target_not_reached")
        self.assertIn("DV-INNER", detail)

    def test_a_settled_obligation_reaches_the_emitted_entry_state(self):
        # How this was found: the two tests above failed with
        # target_not_reached, and the cause was not in verification at all.
        # `IF WS-A = 'A'` guards the PERFORM, and a later `MOVE 'Z' TO WS-A`
        # made provenance name a `literal` producer for WS-A. The solver
        # bound the correct value against it - and `input_state()` emits only
        # input/unknown producers, so the value was solved, reported as no
        # open obligation, and dropped on the way out. The plan then reached
        # nothing, for a reason nothing in it recorded.
        from frameladder.ladder import plan_for_branch
        prog = program(self.SRC)
        branch = self._branch(prog, "DV-INNER")
        plan = plan_for_branch(prog, "DV-INNER", branch.line, True,
                               entry="DV-MAIN", ordinal=branch.ordinal)
        self.assertEqual(plan.input_state().get("WS-A"), "A",
                         "the guard reaching the target must be emitted, not "
                         "merely solved")

    def test_every_disposition_is_a_declared_stage(self):
        # The accounting invariant: a verdict the summary has no column for
        # would vanish from the totals, which is the failure being fixed.
        from frameladder.cli import _RUN_STAGES, _STAGES
        for stage in _RUN_STAGES:
            self.assertIn(stage, _STAGES)

    def test_a_loop_kind_can_be_verified_at_all(self):
        # The interpreter names a loop PERFORM_UNTIL and branches_of names it
        # LOOP. Without the join every loop direction is unverifiable and
        # reports as never observed.
        from frameladder.cli import _KIND_OF_GUARD
        self.assertEqual(_KIND_OF_GUARD.get("PERFORM_UNTIL"), "LOOP")
        self.assertEqual(_KIND_OF_GUARD.get("PERFORM_VARYING"), "LOOP")


class TestVerificationWorld(unittest.TestCase):
    """A plan is verified in a world, and `bare` is not the only honest one.

    The shape of batch COBOL: open the files, abend if that failed, then loop.
    Under `bare` the files are absent, so an indexed OPEN INPUT gives 35, the
    program abends in its prologue, and every decision past it is unreachable
    no matter what the plan binds. Verification ran only in `bare` while
    `coverage` had been running every plan in every world since the worlds
    were named - so the two disagreed about what the same plan reached, and
    the disagreement was reported as a fact about the solver.

    Measured on the ten CardDemo batch programs: 202 of the 222 plans that
    stopped short did so on `CEE3ABD`, and 190 of them had entered exactly one
    frame of their own chain. Corpus-wide the change is 804 -> 938 verified.
    """

    SRC = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INFILE
                  ORGANIZATION IS INDEXED
                  ACCESS MODE IS SEQUENTIAL
                  RECORD KEY IS IN-KEY
                  FILE STATUS IS WS-ST.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-REC.
           05  IN-KEY PIC X(8).
       WORKING-STORAGE SECTION.
       01  WS-ST PIC XX.
       01  WS-EOF PIC X VALUE 'N'.
       01  WS-A PIC X.
       PROCEDURE DIVISION.
       WV-MAIN.
           OPEN INPUT IN-FILE
           IF WS-ST NOT = '00'
              PERFORM WV-ABEND
           END-IF
           PERFORM WV-WORK
           GOBACK
           .
       WV-ABEND.
           CALL 'CEE3ABD'
           .
       WV-WORK.
           IF WS-A = 'A'
              MOVE 'Z' TO WS-A
           END-IF
           GOBACK
           .
"""

    def _branch(self, prog):
        from frameladder.coverage import branches_of
        hits = [b for b in branches_of(prog) if b.paragraph == "WV-WORK"]
        return hits[0]

    def _plan(self, prog, branch):
        from frameladder.ladder import plan_for_branch
        return plan_for_branch(prog, "WV-WORK", branch.line, True,
                               entry="WV-MAIN", ordinal=branch.ordinal)

    def test_bare_alone_cannot_reach_past_a_failed_open(self):
        # Not a fact about the plan: the run never got the chance.
        from frameladder.cli import _verify_direction
        prog = program(self.SRC)
        branch = self._branch(prog)
        verdict, detail = _verify_direction(
            prog, self._plan(prog, branch), branch, True, "WV-MAIN",
            worlds=("bare",))
        self.assertEqual(verdict, "target_not_reached")
        # Why it stopped, which is the discriminator between this defect and
        # the last-hop guard problem. The sentence carries the reach profile;
        # the stop reason rides in the sink.
        sink = {}
        _verify_direction(prog, self._plan(prog, branch), branch, True,
                          "WV-MAIN", sink=sink, worlds=("bare",))
        self.assertIn("CEE3ABD", str(sink.get("stopped", "")) + detail)

    def test_a_world_where_the_files_open_verifies_the_same_plan(self):
        from frameladder.cli import _verify_direction
        prog = program(self.SRC)
        branch = self._branch(prog)
        sink = {}
        from frameladder.conformance_defaults import WORLDS
        verdict, _detail = _verify_direction(
            prog, self._plan(prog, branch), branch, True, "WV-MAIN",
            sink=sink, worlds=WORLDS)
        self.assertEqual(verdict, "verified")
        # And it says which world, because a witness that needs the files to
        # open is a witness the harness has to be told about.
        self.assertEqual(sink.get("world"), "populated")

    def test_bare_is_tried_first_so_a_witness_asks_for_the_least(self):
        # Ordering is meaning here: the cheapest world that works is the one
        # reported, so nothing demands staged data it does not need.
        from frameladder.cli import _verify_direction
        from frameladder.conformance_defaults import WORLDS
        from frameladder.coverage import branches_of
        from frameladder.ladder import plan_for_branch
        self.assertEqual(WORLDS[0], "bare")
        prog = program(TestDirectionVerification.SRC)
        branch = [b for b in branches_of(prog)
                  if b.paragraph == "DV-INNER"][0]
        plan = plan_for_branch(prog, "DV-INNER", branch.line, True,
                               entry="DV-MAIN", ordinal=branch.ordinal)
        sink = {}
        verdict, _detail = _verify_direction(prog, plan, branch, True,
                                             "DV-MAIN", sink=sink)
        self.assertEqual(verdict, "verified")
        self.assertEqual(sink.get("world"), "bare")

    def test_the_world_never_overrides_what_the_plan_forced(self):
        # The free/forced invariant, applied to the outside world: defaults
        # fill only operations the plan planned no outcome for. A world that
        # could overwrite a planned status would let a convenience contradict
        # something the program requires.
        from frameladder.interpreter import Interpreter
        from frameladder.conformance_defaults import io_defaults
        prog = program(self.SRC)
        stubs = {"OPEN-INPUT:IN-FILE": [{"when": {}, "set": {"WS-ST": "35"},
                                         "seq": 0, "inferred": False}]}
        trace = Interpreter(prog, {}, stubs=stubs,
                            defaults=io_defaults(prog, "populated")
                            ).run("WV-MAIN")
        self.assertIn("WV-ABEND", trace.entered_set,
                      "a planned failure must survive a populated world")

    def test_every_world_is_a_declared_world(self):
        from frameladder.conformance_defaults import WORLDS
        from frameladder.cli import _HOW_FAR as _REACH_RANK
        self.assertEqual(set(WORLDS), {"bare", "populated", "empty"})
        # The rank exists to pick which run to *report*; it must never be able
        # to promote something to verified, which the guard event alone
        # decides. So verified is strictly the top and nothing ties with it.
        self.assertEqual(_REACH_RANK[0], "verified")   # best first
        self.assertEqual(_REACH_RANK.count("verified"), 1)
        self.assertEqual(len(set(_REACH_RANK)), len(_REACH_RANK))


class TestRefusalKinds(unittest.TestCase):
    """A refusal's *kind* is what says who fixes it."""

    def test_each_refusal_maps_to_the_capability_it_names(self):
        from frameladder.capability import refusal_kind
        self.assertEqual(refusal_kind("cannot replay READ:F (needed to set X)"),
                         "unsupported_operation")
        self.assertEqual(refusal_kind("cannot inject WS-X"),
                         "unrepresentable_input")
        self.assertEqual(refusal_kind("READ:F cannot set CUST-ID"),
                         "unsupported_output_field")
        self.assertEqual(refusal_kind("READ:F needs 4 outcomes, harness holds 2"),
                         "replay_sequence_too_long")

    def test_a_series_longer_than_the_harness_holds_is_refused(self):
        # The outcomes past the limit are the ones that end the loop, so a
        # truncated series does not run short - it runs wrong.
        from frameladder.capability import load, unrepresentable

        class _Plan:
            bindings = ()

            def stub_plan(self):
                return {"READ:F": [{"WS-ST": "00"}, {"WS-ST": "00"},
                                   {"WS-ST": "10"}]}

        cap = load({"schema_version": "1.0", "replayable_operations": [
            {"op_key": "READ:F", "max_outcomes": 2}]})
        reasons = unrepresentable(_Plan(), cap)
        self.assertTrue(any("outcomes" in r for r in reasons), reasons)


class TestFrameHeadroom(unittest.TestCase):
    """Whether resuming from a harness's frames could add reach at all.

    Re-planning from a failed attempt's `first_missing_frame` only pays if the
    harness gets somewhere derivation cannot already start. That is a property
    of the estate, not of the idea, so it is measured rather than assumed.
    """

    SRC = HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       FH-MAIN.
           IF WS-A = 'A'
              PERFORM FH-REACHED
           END-IF
           GOBACK
           .
       FH-REACHED.
           GOBACK
           .
       FH-ORPHAN.
           EXIT
           .
"""
    # FH-REACHED ends in GOBACK on purpose. With a bare EXIT, COBOL falls
    # through into FH-ORPHAN and the "orphan" is reachable after all - which
    # is the fixture being wrong, not the analysis.

    def _args(self, capability_path=None):
        import argparse
        return argparse.Namespace(entry=None, capability=capability_path,
                                  conventions=None, proxy=None)

    def test_a_frame_we_cannot_reach_is_worth_resuming_from(self):
        from frameladder.capability import load
        from frameladder.cli import _frame_headroom
        prog = program(self.SRC)
        cap = load({"schema_version": "1.0", "attempts": [
            {"target": "FH-ORPHAN", "reached_frames": ["FH-MAIN", "FH-ORPHAN"]}]})
        result = _frame_headroom(cap, prog, self._args())
        self.assertEqual(result["beyond_us"], ["FH-ORPHAN"])
        self.assertIn("worth doing", result["verdict"])

    def test_frames_we_already_reach_only_rank_seeds(self):
        from frameladder.capability import load
        from frameladder.cli import _frame_headroom
        prog = program(self.SRC)
        cap = load({"schema_version": "1.0", "attempts": [
            {"target": "FH-REACHED", "reached_frames": ["FH-MAIN", "FH-REACHED"]}]})
        result = _frame_headroom(cap, prog, self._args())
        self.assertEqual(result["beyond_us"], [])
        self.assertIn("ranks seeds", result["verdict"])

    def test_a_frame_this_program_does_not_have_is_not_counted_as_reach(self):
        # A name we do not know is a vocabulary gap, not new ground, and
        # counting it as reach would argue for the feature on false evidence.
        from frameladder.capability import load
        from frameladder.cli import _frame_headroom
        prog = program(self.SRC)
        cap = load({"schema_version": "1.0", "attempts": [
            {"target": "X", "reached_frames": ["NOT-IN-THIS-PROGRAM"]}]})
        result = _frame_headroom(cap, prog, self._args())
        self.assertEqual(result["beyond_us"], [])
        self.assertEqual(result["unknown"], ["NOT-IN-THIS-PROGRAM"])

    def test_no_attempts_says_so_rather_than_implying_a_verdict(self):
        from frameladder.capability import load
        from frameladder.cli import _frame_headroom
        cap = load({"schema_version": "1.0"})
        result = _frame_headroom(cap, program(self.SRC), self._args())
        self.assertEqual(result["attempts"], 0)
        self.assertIn("no attempts", result["verdict"])


class TestOperationAliases(unittest.TestCase):
    """The two sides key one mock differently, and say so rather than guess."""

    def test_punctuation_and_case_need_no_alias(self):
        from frameladder.capability import load
        cap = load({"schema_version": "1.0", "replayable_operations": [
            {"op_key": "EXEC:CICS:READ"}]})
        for spelling in ("EXEC CICS READ", "exec/cics/read", "Exec.Cics.Read"):
            self.assertTrue(cap.can_replay(spelling), spelling)

    def test_a_declared_alias_is_honoured(self):
        from frameladder.capability import load
        cap = load({"schema_version": "1.0", "replayable_operations": [
            {"op_key": "READ:CUSTOMER-FILE", "aliases": ["READ:CUSTDD"],
             "fields": ["CUST-ID"]}]})
        self.assertTrue(cap.can_replay("READ:CUSTDD"))
        self.assertTrue(cap.can_set("READ:CUSTDD", "CUST-ID"))
        self.assertFalse(cap.can_set("READ:CUSTDD", "SOMETHING-ELSE"))

    def test_an_undeclared_name_is_still_refused(self):
        # Aliasing widens what the harness said, never what it did not.
        from frameladder.capability import load
        cap = load({"schema_version": "1.0", "replayable_operations": [
            {"op_key": "READ:CUSTOMER-FILE"}]})
        self.assertFalse(cap.can_replay("READ:ORDER-FILE"))

    def test_a_real_op_key_wins_a_collision_with_an_alias(self):
        from frameladder.capability import load
        cap = load({"schema_version": "1.0", "replayable_operations": [
            {"op_key": "READ:A", "aliases": ["READ:B"]},
            {"op_key": "READ:B", "max_outcomes": 7}]})
        self.assertEqual(cap.outcome_limit("READ:B"), 7)

    def test_aliases_stay_last_in_the_field_order(self):
        # `represent.py` and several tests construct an Operation
        # positionally. A field inserted above `aliases` silently changes what
        # their fourth argument means, which is exactly how this arrived.
        import dataclasses
        from frameladder.capability import Operation
        names = [f.name for f in dataclasses.fields(Operation)]
        self.assertEqual(names[-1], "aliases")
        self.assertEqual(names[:4],
                         ["op_key", "fields", "max_outcomes",
                          "matches_on_state"])


class TestRepresentability(unittest.TestCase):
    """Classifying what the harness could run, in the harness's own words."""

    HEADER_SRC = HEADER + """       01  WS-OPEN PIC X VALUE ' '.
       01  WS-SHUT PIC X VALUE ' '.
       PROCEDURE DIVISION.
       RP-MAIN.
           IF WS-SHUT = 'Y'
              PERFORM RP-TARGET
           END-IF
           PERFORM RP-GATE
           GO TO RP-DONE
           .
       RP-GATE.
           IF WS-OPEN = 'Y'
              PERFORM RP-TARGET
           END-IF
           GO TO RP-DONE
           .
       RP-TARGET.
           DISPLAY 'X'
           GO TO RP-DONE
           .
       RP-DONE.
           GOBACK
           .
"""

    def _cap(self):
        from frameladder.capability import Capability
        return Capability(injectable=frozenset({"WS-OPEN"}), stated=True)

    def test_the_proxy_profile_reads_evidence_not_names(self):
        from frameladder.ladder import analyse
        from frameladder.represent import proxy_profile
        prog = program(TestReplayExport.FILE_SRC)
        _graph, prov = analyse(prog)
        profile = proxy_profile(prog, prov)
        # Compared against '10' in the source, so the harness has something to
        # aim at; the record field is compared against nothing at all.
        self.assertTrue(profile.can_inject("WS-FS"))
        self.assertFalse(profile.can_inject("IN-KEY"))
        # The SELECT put WS-FS in the file-status channel, which is what makes
        # the READ replayable - and the record area is not in any channel, so
        # a mock that carries a status cannot hand it back.
        self.assertTrue(profile.can_replay("READ:IN-FILE"))
        self.assertTrue(profile.can_set("READ:IN-FILE", "WS-FS"))
        self.assertFalse(profile.can_set("READ:IN-FILE", "IN-KEY"))

    def test_an_operation_with_nothing_in_a_status_channel_is_left_out(self):
        # An empty field set means "any field" in the profile, so an operation
        # whose outcome is entirely out of the harness's control is left out
        # rather than registered with nothing - registering it would turn the
        # strictest case into the most permissive one.
        #
        # The residual, measured rather than hidden: when *no* operation in a
        # program has a status channel the proxy *omits* the section rather
        # than emptying it, and an absent section states no constraint. The
        # distinction is deliberate - an empty section would claim the harness
        # can replay nothing, which the proxy has not earned - so every figure
        # it produces for such a program is an over-estimate of what would
        # replay.
        from frameladder.represent import proxy_profile, stub_outputs_by_operation
        from frameladder.ladder import analyse
        prog = program(HEADER + """       01  WS-A PIC X VALUE ' '.
       PROCEDURE DIVISION.
       RN-MAIN.
           CALL 'SUBPROG' USING WS-A
           IF WS-A = 'Y'
              PERFORM RN-END
           END-IF
           GO TO RN-DONE
           .
       RN-END.
           DISPLAY 'E'
           GO TO RN-DONE
           .
       RN-DONE.
           GOBACK
           .
""")
        _graph, prov = analyse(prog)
        self.assertIn("CALL:SUBPROG", stub_outputs_by_operation(prov))
        profile = proxy_profile(prog, prov)
        self.assertIsNone(profile.operations)
        # Documented consequence, not a wish: with nothing stated about
        # operations the contract answers "yes" rather than "no".
        self.assertTrue(profile.can_replay("CALL:SUBPROG"))

    def test_precheck_names_the_refusal_before_any_solving(self):
        from frameladder.ladder import precheck
        prog = program(self.HEADER_SRC)
        reasons = [why for _atom, why in
                   precheck(prog, "RP-TARGET", self._cap())]
        self.assertEqual(reasons, ["cannot inject WS-SHUT"])

    def test_precheck_says_nothing_when_no_profile_is_stated(self):
        from frameladder.capability import Capability
        from frameladder.ladder import precheck
        prog = program(self.HEADER_SRC)
        self.assertEqual(precheck(prog, "RP-TARGET", Capability()), [])

    def test_precheck_agrees_with_the_verdict_on_the_finished_plan(self):
        # The cheap filter and the full solve have to reach the same answer on
        # the same route, or the saving is bought with a wrong refusal.
        from frameladder.capability import unrepresentable
        from frameladder.ladder import precheck
        prog = program(self.HEADER_SRC)
        cap = self._cap()
        plan = build_plan(prog, "RP-TARGET")
        self.assertEqual([why for _a, why in precheck(prog, "RP-TARGET", cap)],
                         unrepresentable(plan, cap))

    def test_the_planner_prefers_a_route_the_profile_permits(self):
        from frameladder.capability import unrepresentable
        from frameladder.ladder import plan_representable
        prog = program(self.HEADER_SRC)
        cap = self._cap()
        self.assertEqual(build_plan(prog, "RP-TARGET").input_state(),
                         {"WS-SHUT": "Y"})
        plan = plan_representable(prog, "RP-TARGET", capability=cap)
        self.assertEqual(plan.input_state(), {"WS-OPEN": "Y"})
        self.assertEqual(unrepresentable(plan, cap), [])
        self.assertIn("RP-GATE", plan.chain)

    def test_an_or_takes_the_branch_the_harness_can_deliver(self):
        # Both branches satisfy the program equally; only one can be run.
        prog = program(HEADER + """       01  WS-OPEN PIC X VALUE ' '.
       01  WS-SHUT PIC X VALUE ' '.
       PROCEDURE DIVISION.
       RQ-MAIN.
           IF WS-SHUT = 'Y' OR WS-OPEN = 'Y'
              PERFORM RQ-TARGET
           END-IF
           GO TO RQ-DONE
           .
       RQ-TARGET.
           DISPLAY 'X'
           GO TO RQ-DONE
           .
       RQ-DONE.
           GOBACK
           .
""")
        self.assertEqual(build_plan(prog, "RQ-TARGET").input_state(),
                         {"WS-SHUT": "Y"})
        self.assertEqual(build_plan(prog, "RQ-TARGET",
                                    capability=self._cap()).input_state(),
                         {"WS-OPEN": "Y"})

    def test_a_route_refused_everywhere_is_still_derived_and_then_reported(self):
        # The filter is not a proof, so losing the plan on its say-so would be
        # the expensive kind of wrong. The plan comes back, and comes back
        # carrying the reason it cannot be run.
        from frameladder.capability import Capability, unrepresentable
        from frameladder.ladder import plan_representable
        prog = program(self.HEADER_SRC)
        cap = Capability(injectable=frozenset({"WS-NOTHING"}), stated=True)
        plan = plan_representable(prog, "RP-TARGET", capability=cap)
        self.assertTrue(plan.chain)
        self.assertEqual(unrepresentable(plan, cap), ["cannot inject WS-SHUT"])

    def test_classify_counts_both_denominators_and_the_reasons(self):
        from frameladder.represent import classify
        prog = program(self.HEADER_SRC)
        report = classify(prog, self._cap(), measure_precheck=True)
        self.assertEqual(report["emitted"]["plans"], 3)
        self.assertEqual(report["emitted"]["unrepresentable"], 1)
        self.assertEqual(report["reason_categories"],
                         {"cannot inject a variable": 1})
        self.assertEqual(report["precheck_false_refusals"], [])
        aware = classify(prog, self._cap(), profile_aware=True)
        self.assertEqual(aware["emitted"]["unrepresentable"], 0)
        self.assertGreater(aware["runnable"], report["runnable"])

    def test_a_refusal_names_the_unit_of_work_it_would_take_to_clear_it(self):
        # A missing mock and a missing field on a mock that exists are two
        # different pieces of work for two different people, and the sentences
        # differ only in shape - so the mapping is pinned rather than assumed.
        from frameladder.represent import capability_needed
        self.assertEqual(
            capability_needed("cannot replay READ:F (needed to set CUST-ID)"),
            "replay READ:F")
        self.assertEqual(capability_needed("READ:F cannot set CUST-ID"),
                         "READ:F must set CUST-ID")
        self.assertEqual(capability_needed("cannot inject WS-SHUT"),
                         "inject WS-SHUT")

    def test_unlock_covers_reason_sets_rather_than_ranking_reasons(self):
        # The commonest reason is not the most valuable addition when it is
        # one of several a plan is waiting on. Here `inject A` appears in
        # three plans and unlocks none of them alone; `inject C` appears in
        # one and unlocks it outright, so a cover must open with C.
        from frameladder.represent import unlock
        rows = [{"target": "T1", "representable": False,
                 "reasons": ["cannot inject A", "cannot inject B"]},
                {"target": "T2", "representable": False,
                 "reasons": ["cannot inject A", "cannot inject B"]},
                {"target": "T3", "representable": False,
                 "reasons": ["cannot inject A", "cannot inject D"]},
                {"target": "T4", "representable": False,
                 "reasons": ["cannot inject C"]},
                {"target": "T5", "representable": True, "reasons": []}]
        report = unlock(rows, limit=3)
        self.assertEqual(report["blocked"], 4)
        self.assertEqual(report["additions"][0]["capability"], "inject C")
        self.assertEqual(report["additions"][0]["unlocks"], 1)
        # A plan waiting on two things is not unblocked by one of them.
        self.assertEqual(report["needs_median"], 2)
        self.assertEqual(report["needs_max"], 2)

    def test_unlock_keeps_going_when_no_single_addition_unblocks_anything(self):
        # Greedy stalls as soon as every remaining plan needs two at once,
        # which is the common case. Stopping there would report nothing to do
        # while three plans wait on one obvious field.
        from frameladder.represent import unlock
        rows = [{"target": "T%d" % i, "representable": False,
                 "reasons": ["cannot inject A", "cannot inject B%d" % i]}
                for i in range(3)]
        report = unlock(rows, limit=2)
        self.assertEqual(report["additions"][0]["capability"], "inject A")
        self.assertEqual(report["additions"][0]["unlocks"], 0)
        self.assertEqual(report["additions"][1]["unlocks"], 1)
        self.assertEqual(report["unlocked"], 1)

    def test_unlock_reports_nothing_when_every_plan_is_representable(self):
        from frameladder.represent import unlock
        report = unlock([{"target": "T", "representable": True, "reasons": []}])
        self.assertEqual(report["blocked"], 0)
        self.assertEqual(report["additions"], [])
        self.assertEqual(unlock([], limit=0)["additions"], [])

    def test_an_unstated_profile_classifies_everything_as_representable(self):
        from frameladder.capability import Capability
        from frameladder.represent import classify
        prog = program(self.HEADER_SRC)
        report = classify(prog, Capability())
        self.assertEqual(report["emitted"]["unrepresentable"], 0)

    def test_a_branch_plan_takes_a_route_the_profile_permits(self):
        # The branch planner already retried other routes when the chain
        # settled the decision the wrong way. With a profile it has a second
        # criterion, and the first one has to survive: representable and
        # deciding the wrong way is not an improvement.
        from frameladder.capability import Capability, unrepresentable
        from frameladder.coverage import branches_of
        from frameladder.ladder import plan_for_branch
        prog = program(HEADER + """       01  WS-OPEN PIC X VALUE ' '.
       01  WS-SHUT PIC X VALUE ' '.
       01  WS-PICK PIC X VALUE ' '.
       PROCEDURE DIVISION.
       RT-MAIN.
           IF WS-SHUT = 'Y'
              PERFORM RT-TARGET
           END-IF
           PERFORM RT-GATE
           GO TO RT-DONE
           .
       RT-GATE.
           IF WS-OPEN = 'Y'
              PERFORM RT-TARGET
           END-IF
           GO TO RT-DONE
           .
       RT-TARGET.
           IF WS-PICK = 'A'
              DISPLAY 'Y'
           END-IF
           GO TO RT-DONE
           .
       RT-DONE.
           GOBACK
           .
""")
        branch = next(b for b in branches_of(prog) if b.paragraph == "RT-TARGET")
        cap = Capability(injectable=frozenset({"WS-OPEN", "WS-PICK"}),
                         stated=True)
        plain = plan_for_branch(prog, branch.paragraph, branch.line, True,
                                ordinal=branch.ordinal)
        self.assertEqual(plain.input_state().get("WS-SHUT"), "Y")
        plan = plan_for_branch(prog, branch.paragraph, branch.line, True,
                               ordinal=branch.ordinal, capability=cap)
        self.assertEqual(plan.input_state(),
                         {"WS-OPEN": "Y", "WS-PICK": "A"})
        self.assertEqual(unrepresentable(plan, cap), [])

class TestReplayExport(unittest.TestCase):
    """The series a harness runs, and what happens to what it cannot run."""

    FILE_SRC = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INDD
               ORGANIZATION IS SEQUENTIAL
               FILE STATUS IS WS-FS.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-REC.
           05  IN-KEY PIC X(4).
       WORKING-STORAGE SECTION.
       01  WS-FS PIC XX VALUE '00'.
       PROCEDURE DIVISION.
       RS-MAIN.
           READ IN-FILE
           IF WS-FS = '10'
              PERFORM RS-END
           END-IF
           GO TO RS-DONE
           .
       RS-END.
           DISPLAY 'E'
           GO TO RS-DONE
           .
       RS-DONE.
           GOBACK
           .
"""

    ENTRIES = [{"when": {}, "set": {"WS-FS": "00", "IN-KEY": "AAAA"}, "seq": 0},
               {"when": {}, "set": {"WS-FS": "00", "IN-KEY": "BBBB"}, "seq": 1},
               {"when": {}, "set": {"WS-FS": "23"}, "seq": 2}]

    def _capability(self, **kw):
        from frameladder import capability
        return capability.Capability(**kw)

    def test_nothing_stated_refuses_nothing(self):
        from frameladder.replay import operation_series
        series = operation_series("READ:IN-FILE", self.ENTRIES,
                                  {"WS-FS": "10"}, self._capability())
        self.assertEqual(series["refusals"], [])
        self.assertEqual([o["set"]["WS-FS"] for o in series["outcomes"]],
                         ["00", "00", "23"])
        self.assertEqual(series["terminal"], {"WS-FS": "10"})

    def test_the_terminal_is_part_of_the_series(self):
        # A mock returning one fixed status describes a file that never ends,
        # so the ending has to travel with the outcomes rather than be
        # inferred by whoever runs them.
        from frameladder.replay import operation_series
        series = operation_series("READ:IN-FILE", self.ENTRIES, None,
                                  self._capability())
        self.assertIsNone(series["terminal"])
        self.assertTrue(any("no terminal" in n for n in series["notes"]))

    def test_an_unsettable_field_is_reported_and_its_call_stays_put(self):
        # Removing the outcome would shift every later one onto an earlier
        # call, which changes what the plan says without changing what it
        # claims. The empty delivery keeps the positions honest.
        from frameladder.capability import Operation
        from frameladder.replay import operation_series
        cap = self._capability(
            operations={"READ:IN-FILE": Operation("READ:IN-FILE",
                                                  frozenset({"WS-FS"}))},
            stated=True)
        series = operation_series("READ:IN-FILE", self.ENTRIES,
                                  {"WS-FS": "10"}, cap)
        self.assertEqual([o["call"] for o in series["outcomes"]], [1, 2, 3])
        self.assertEqual([sorted(o["set"]) for o in series["outcomes"]],
                         [["WS-FS"], ["WS-FS"], ["WS-FS"]])
        self.assertIn("READ:IN-FILE cannot set IN-KEY", series["refusals"])

    def test_max_outcomes_truncates_and_says_so(self):
        from frameladder.capability import Operation
        from frameladder.replay import operation_series
        cap = self._capability(
            operations={"READ:IN-FILE": Operation("READ:IN-FILE",
                                                  frozenset(), 2)},
            stated=True)
        series = operation_series("READ:IN-FILE", self.ENTRIES, None, cap)
        self.assertEqual(len(series["outcomes"]), 2)
        self.assertTrue(any("at most 2" in r for r in series["refusals"]))

    def test_an_operation_the_harness_cannot_replay_is_not_silently_empty(self):
        from frameladder.capability import Operation
        from frameladder.replay import operation_series
        cap = self._capability(
            operations={"READ:OTHER-FILE": Operation("READ:OTHER-FILE")},
            stated=True)
        series = operation_series("READ:IN-FILE", self.ENTRIES, None, cap)
        self.assertFalse(series["replayable"])
        self.assertEqual(series["refusals"], ["cannot replay READ:IN-FILE"])
        self.assertEqual(series["outcomes"], [])

    def test_outcomes_are_ordered_by_seq_not_by_dictionary_order(self):
        from frameladder.replay import operation_series
        shuffled = [self.ENTRIES[2], self.ENTRIES[0], self.ENTRIES[1]]
        series = operation_series("READ:IN-FILE", shuffled, None,
                                  self._capability())
        self.assertEqual([o["set"]["WS-FS"] for o in series["outcomes"]],
                         ["00", "00", "23"])

    def test_a_terminal_for_an_operation_with_no_outcomes_still_travels(self):
        from frameladder.replay import replay_script
        prog = program(self.FILE_SRC)
        plan = build_plan(prog, "RS-END")
        plan.terminals = {"OPEN-INPUT:IN-FILE": {"WS-FS": "35"}}
        script = replay_script(plan, self._capability(), program=prog)
        keys = [op["op_key"] for op in script["operations"]]
        self.assertIn("OPEN-INPUT:IN-FILE", keys)

    def test_a_plan_needing_an_unreplayable_operation_is_refused(self):
        from frameladder.capability import Operation
        from frameladder.replay import replay_script
        prog = program(self.FILE_SRC)
        plan = build_plan(prog, "RS-END")
        cap = self._capability(
            operations={"READ:OTHER-FILE": Operation("READ:OTHER-FILE")},
            stated=True)
        script = replay_script(plan, cap, program=prog)
        self.assertFalse(script["representable"])
        self.assertIn("cannot replay READ:IN-FILE (needed to set WS-FS)",
                      script["reasons"])

    def test_an_uninjectable_entry_value_is_listed_rather_than_dropped(self):
        # The whole point: the value does not quietly disappear from
        # `input_state` leaving a case that runs and means nothing.
        from frameladder.replay import replay_script
        prog = program(TestRepresentability.HEADER_SRC)
        plan = build_plan(prog, "RP-TARGET")
        cap = self._capability(injectable=frozenset({"WS-OPEN"}), stated=True)
        script = replay_script(plan, cap, program=prog)
        self.assertEqual(script["input_state"], {})
        self.assertEqual([r["variable"] for r in script["refused_inputs"]],
                         ["WS-SHUT"])
        self.assertFalse(script["representable"])
        self.assertIn("cannot inject WS-SHUT", script["reasons"])

    def test_the_export_carries_a_derived_fault_world(self):
        # "the operation fails on its second call and succeeds either side"
        # is an outcome list and there is no other way to state it.
        from frameladder.ladder import analyse
        from frameladder.replay import replay_script
        from frameladder.sequences import fault_worlds
        prog = program(self.FILE_SRC)
        _graph, prov = analyse(prog)
        worlds = fault_worlds(prog, prov, prov.literals, length=3)
        self.assertTrue(worlds)
        plan = build_plan(prog, "RS-END")
        script = replay_script(plan, self._capability(), program=prog,
                               world=worlds[0])
        series = script["operations"][0]
        self.assertEqual(series["op_key"], "READ:IN-FILE")
        self.assertGreater(len(series["outcomes"]), 1)
        self.assertTrue(series["terminal"])


class TestCapabilityDiscriminators(unittest.TestCase):
    """Silence about a capability is not a refusal of it."""

    def test_absent_is_unknown_not_no(self):
        from frameladder.capability import load
        cap = load({"schema_version": "1.0",
                    "replayable_operations": [{"op_key": "READ:F"}]})
        self.assertIsNone(cap.discriminates("READ:F"))

    def test_a_harness_can_say_it_only_replays_in_order(self):
        from frameladder.capability import load
        cap = load({"schema_version": "1.0",
                    "replayable_operations": [
                        {"op_key": "READ:F", "matches_on_state": False}]})
        self.assertIs(cap.discriminates("READ:F"), False)


class TestLabelParsing(unittest.TestCase):
    """Labels the parser must not lose, and namesakes it must not hide."""

    def test_a_space_before_the_period_still_starts_a_paragraph(self):
        # `1000-INIT .` is legal and appears in real source. Requiring the
        # period to touch the name does not raise - it silently absorbs the
        # paragraph's statements into whichever one came before, so the label
        # is unreachable and the body is attributed to a neighbour.
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       LP-MAIN.
           PERFORM LP-SPACED
           GOBACK
           .
       LP-SPACED .
           MOVE 'A' TO WS-A
           .
""")
        self.assertIn("LP-SPACED", p.paragraph_names)

    def test_a_space_before_the_period_still_starts_a_section(self):
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       LP-MAIN.
           GOBACK
           .
       LP-SECT SECTION .
           MOVE 'A' TO WS-A
           .
""")
        self.assertIn("LP-SECT", p.paragraph_names)

    def test_duplicate_paragraph_names_are_reported_not_hidden(self):
        # Legal COBOL, and this parser keeps a flat list: `paragraph()`
        # returns the first, so every later namesake is parsed, indexed and
        # unreachable by name. Stated, because a silent wrong answer is worse
        # than a known limitation.
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       LP-MAIN.
           GOBACK
           .
       LP-TWICE.
           MOVE 'A' TO WS-A
           .
       LP-TWICE.
           MOVE 'B' TO WS-A
           .
""")
        self.assertEqual(p.duplicate_paragraphs, {"LP-TWICE": 2})

    def test_a_program_without_namesakes_reports_none(self):
        p = program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       LP-ONLY.
           GOBACK
           .
""")
        self.assertEqual(p.duplicate_paragraphs, {})


class TestConditionTails(unittest.TestCase):
    """Words that end a statement, not a comparison."""

    def _atoms(self, text):
        from frameladder.conditions import condition_atoms
        return [(getattr(a.lhs, "name", None), a.op, getattr(a.rhs, "value", None))
                for alt in condition_atoms(text) for a in alt]

    def test_a_trailing_then_is_not_part_of_the_literal(self):
        # Left in place the right-hand side becomes the literal "'00' THEN",
        # which nothing the program can hold ever equals - so the direction is
        # not merely mis-parsed, it is permanently unsatisfiable, silently.
        self.assertEqual(self._atoms("WS-STATUS = '00' THEN"),
                         [("WS-STATUS", "=", "00")])

    def test_a_trailing_next_sentence_is_not_part_of_the_literal(self):
        self.assertEqual(self._atoms("WS-A = 'X' NEXT SENTENCE"),
                         [("WS-A", "=", "X")])

    def test_both_tails_at_once(self):
        self.assertEqual(self._atoms("WS-A = 'X' THEN NEXT SENTENCE"),
                         [("WS-A", "=", "X")])

    def test_a_name_ending_in_then_is_left_alone(self):
        # The tail is a separate word. A field called WS-THEN is not a tail,
        # and stripping by substring would eat it.
        self.assertEqual(self._atoms("WS-THEN = '1'"), [("WS-THEN", "=", "1")])


class TestParenthesisedRelationLists(unittest.TestCase):
    """`X NOT EQUAL ('00' AND '04')` is one abbreviated combined relation."""

    def _atoms(self, text):
        from frameladder.conditions import condition_atoms
        return [[(getattr(a.lhs, "name", None), a.op, getattr(a.rhs, "value", None))
                 for a in alt] for alt in condition_atoms(text)]

    def test_an_and_list_becomes_a_conjunction(self):
        self.assertEqual(self._atoms("WS-N NOT EQUAL ('00' AND '04' AND '05')"),
                         [[("WS-N", "!=", "00"), ("WS-N", "!=", "04"),
                           ("WS-N", "!=", "05")]])

    def test_an_or_list_becomes_alternatives(self):
        alts = self._atoms("WS-N = ('00' OR '04')")
        self.assertEqual(sorted(alts), [[("WS-N", "=", "00")],
                                        [("WS-N", "=", "04")]])

    def test_a_real_expression_is_left_for_the_ordinary_parser(self):
        # `(WS-B + 1)` is arithmetic, not a list of operands. Rewriting it
        # would invent comparisons the program does not make.
        from frameladder.conditions import _expand_paren_list
        self.assertEqual(_expand_paren_list("WS-A = (WS-B + 1)"),
                         "WS-A = (WS-B + 1)")

    def test_an_ordinary_parenthesised_condition_is_untouched(self):
        from frameladder.conditions import _expand_paren_list
        text = "(WS-A = 1 AND WS-B = 2)"
        self.assertEqual(_expand_paren_list(text), text)

    def test_a_mixed_connector_list_is_left_alone(self):
        # `('00' AND '04' OR '05')` has no single distribution, so it is
        # reported unchanged rather than guessed at.
        from frameladder.conditions import _expand_paren_list
        text = "WS-N NOT EQUAL ('00' AND '04' OR '05')"
        self.assertEqual(_expand_paren_list(text), text)


class TestOutOfLineLoops(unittest.TestCase):
    """`PERFORM <para> VARYING/TIMES/TEST AFTER` is a loop over that paragraph.

    The clause was parsed off an out-of-line PERFORM and discarded, leaving
    only the UNTIL - so the induction variable was never initialised and never
    stepped, and the body ran *zero* times rather than a wrong number of
    times. Every expected count here was confirmed against GnuCOBOL.
    """

    def _run(self, mainline, body="           ADD 1 TO WS-C\n"):
        from frameladder.conformance_defaults import io_defaults
        from frameladder.interpreter import Interpreter
        p = program(HEADER + """       01  WS-I PIC 9(4).
       01  WS-J PIC 9(4).
       01  WS-N PIC 9(4).
       01  WS-C PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
       OL-MAIN.
""" + mainline + """           GOBACK
           .
       OL-BODY.
""" + body + """           .
""")
        interp = Interpreter(p, {}, defaults=io_defaults(p, "bare"))
        interp.run("OL-MAIN")
        return interp.state

    def test_varying_runs_the_body_once_per_value(self):
        state = self._run("           PERFORM OL-BODY VARYING WS-I "
                          "FROM 1 BY 1 UNTIL WS-I > 3\n")
        self.assertEqual(state.get("WS-C"), 3)
        self.assertEqual(state.get("WS-I"), 4)

    def test_a_negative_step_counts_down(self):
        state = self._run("           PERFORM OL-BODY VARYING WS-I "
                          "FROM 3 BY -1 UNTIL WS-I < 1\n")
        self.assertEqual(state.get("WS-C"), 3)
        self.assertEqual(state.get("WS-I"), 0)

    def test_after_nests_inside_varying(self):
        # COBOL runs the inner range in full for every value of the outer one.
        state = self._run("           PERFORM OL-BODY VARYING WS-I "
                          "FROM 1 BY 1 UNTIL WS-I > 2\n"
                          "              AFTER WS-J FROM 1 BY 1 UNTIL WS-J > 2\n")
        self.assertEqual(state.get("WS-C"), 4)

    def test_a_literal_times_count(self):
        state = self._run("           PERFORM OL-BODY 3 TIMES\n")
        self.assertEqual(state.get("WS-C"), 3)

    def test_a_named_times_count(self):
        state = self._run("           MOVE 3 TO WS-N\n"
                          "           PERFORM OL-BODY WS-N TIMES\n")
        self.assertEqual(state.get("WS-C"), 3)

    def test_test_after_runs_the_body_before_looking(self):
        state = self._run("           MOVE 1 TO WS-I\n"
                          "           PERFORM OL-BODY WITH TEST AFTER "
                          "UNTIL WS-I > 3\n",
                          body="           ADD 1 TO WS-C\n"
                               "           ADD 1 TO WS-I\n")
        self.assertEqual(state.get("WS-C"), 3)

    def test_a_targeted_loop_does_not_swallow_the_next_statement(self):
        # The parser read the statements *after* a targeted PERFORM ... UNTIL
        # as its inline body. COBOL has no form with both a target and an
        # inline body, so a GOBACK written on the next line became the loop
        # body and ended the run on the first iteration - before the target
        # had run at all.
        p = program(HEADER + """       01  WS-I PIC 9(4).
       PROCEDURE DIVISION.
       OL-MAIN.
           PERFORM OL-BODY UNTIL WS-I > 3
           GOBACK
           .
       OL-BODY.
           ADD 1 TO WS-I
           .
""")
        perform = [s for s in p.paragraph("OL-MAIN")["statements"]
                   if s.get("type") == "PERFORM"][0]
        self.assertEqual(perform.get("children"), [])

    def test_a_label_sharing_its_line_with_a_sentence(self):
        # `B1. ADD 1 TO WS-C.` is one paragraph and one sentence. Requiring
        # the label to own its line loses the paragraph silently: nothing can
        # PERFORM it, so every call does nothing and the body is attributed
        # to whichever paragraph came before.
        p = program(HEADER + """       01  WS-C PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
       IL-MAIN.
           PERFORM IL-BODY
           GOBACK
           .
       IL-BODY. ADD 1 TO WS-C.
""")
        self.assertIn("IL-BODY", p.paragraph_names)
        from frameladder.conformance_defaults import io_defaults
        from frameladder.interpreter import Interpreter
        interp = Interpreter(p, {}, defaults=io_defaults(p, "bare"))
        interp.run("IL-MAIN")
        self.assertEqual(interp.state.get("WS-C"), 1)

    def test_a_sentence_verb_is_not_mistaken_for_a_label(self):
        # `EXIT. MOVE ...` must not declare a paragraph called EXIT.
        from frameladder.cobol import _PARA_INLINE, _RESERVED_SENTENCE
        m = _PARA_INLINE.match("EXIT. MOVE 'A' TO WS-C")
        self.assertTrue(m)
        self.assertTrue(_RESERVED_SENTENCE.match(m.group(1)))


class TestCursorSequences(unittest.TestCase):
    """A cursor is a read loop whose status channel is SQLCODE."""

    SRC = HEADER + """       01  SQLCODE PIC S9(9) COMP.
       01  WS-ROWS PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
       CS-MAIN.
           EXEC SQL OPEN C1 END-EXEC
           PERFORM CS-FETCH UNTIL SQLCODE = 100
           GOBACK
           .
       CS-FETCH.
           EXEC SQL FETCH C1 INTO :WS-ROWS END-EXEC
           ADD 1 TO WS-ROWS
           .
"""

    def _worlds(self):
        from frameladder.ladder import analyse
        from frameladder.sequences import sequence_worlds
        p = program(self.SRC)
        _graph, prov = analyse(p)
        return p, sequence_worlds(p, prov, prov.literals)

    def test_a_fetch_is_found_by_the_statement_not_by_a_name(self):
        from frameladder.sequences import cursor_keys
        self.assertEqual(cursor_keys(program(self.SRC)), ["EXEC:SQL:FETCH"])

    def test_a_program_without_a_cursor_gets_none(self):
        self.assertEqual(
            __import__("frameladder.sequences", fromlist=["x"]).cursor_keys(
                program(HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       NC-MAIN.
           GOBACK
           .
""")), [])

    def test_the_cadence_is_rows_then_no_more_rows(self):
        # `0, 0, 0, 100` is a series, not a value. Only files had sequences,
        # so SQLCODE could hold one value for a whole run and a fetch loop
        # was reachable only by making the first fetch return no rows - a
        # different route through the program, or none.
        _p, worlds = self._worlds()
        byname = {w["name"]: w for w in worlds}
        self.assertIn("records:3", byname)
        world = byname["records:3"]
        self.assertEqual([e["set"] for e in world["stubs"]["EXEC:SQL:FETCH"]],
                         [{"SQLCODE": 0}] * 3)
        self.assertEqual(world["terminals"]["EXEC:SQL:FETCH"], {"SQLCODE": 100})

    def test_a_db2_program_with_no_files_still_gets_sequences(self):
        # The early return on "no FILE STATUS" skipped cursors entirely -
        # which is exactly the set of programs that need them.
        p, worlds = self._worlds()
        self.assertEqual(p.model.file_status, {})
        self.assertTrue(worlds)

    def test_the_loop_actually_ends_on_the_terminal(self):
        from frameladder.conformance_defaults import io_defaults
        from frameladder.interpreter import Interpreter
        p, worlds = self._worlds()
        world = {w["name"]: w for w in worlds}["records:3"]
        interp = Interpreter(p, {}, stubs=world["stubs"],
                             terminals=world["terminals"],
                             defaults=io_defaults(p, world["world"]))
        trace = interp.run("CS-MAIN")
        self.assertEqual(interp.state.get("SQLCODE"), 100)
        self.assertFalse(trace.runaway)


class TestOccurrenceIdentity(unittest.TestCase):
    """`FIELD(1)` and `FIELD(2)` are different bytes, not one knob."""

    SRC = HEADER + """       01  WS-TAB.
           05  WS-CELL PIC X OCCURS 5 TIMES.
       01  WS-OK PIC X.
       PROCEDURE DIVISION.
       OC-MAIN.
           IF WS-CELL(1) = 'A' AND WS-CELL(2) = 'B'
              MOVE 'Y' TO WS-OK
           END-IF
           GOBACK
           .
"""

    def _plan(self, src=None):
        from frameladder.coverage import branches_of
        from frameladder.ladder import plan_for_branch
        p = program(src or self.SRC)
        branch = [b for b in branches_of(p) if b.paragraph == "OC-MAIN"][0]
        return p, plan_for_branch(p, "OC-MAIN", branch.line, True,
                                  entry=None, ordinal=branch.ordinal)

    def test_two_occurrences_are_not_a_conflict(self):
        # Keyed on the base name they collided: the first was bound and the
        # second reported as an open obligation, so a plainly satisfiable
        # condition came back unsolvable.
        _p, plan = self._plan()
        self.assertEqual(plan.open_obligations, [])

    def test_the_group_carries_both_occurrences(self):
        _p, plan = self._plan()
        self.assertEqual(plan.input_state(), {"WS-TAB": "AB   "})

    def test_the_plan_actually_takes_the_direction(self):
        from frameladder.conformance_defaults import io_defaults
        from frameladder.interpreter import Interpreter
        p, plan = self._plan()
        interp = Interpreter(p, plan.input_state(), stubs=plan.stub_plan(),
                             terminals=plan.terminals,
                             defaults=io_defaults(p, "bare"))
        interp.run("OC-MAIN")
        self.assertEqual(interp.state.get("WS-OK"), "Y")

    def test_composition_matches_what_the_interpreter_would_write(self):
        # The composed bytes must equal what two MOVEs produce, or the plan
        # is describing a record the program cannot hold.
        from frameladder.conformance_defaults import io_defaults
        from frameladder.interpreter import Interpreter
        p = program(HEADER + """       01  WS-TAB.
           05  WS-CELL PIC X OCCURS 5 TIMES.
       PROCEDURE DIVISION.
       OC-MAIN.
           MOVE 'A' TO WS-CELL(1)
           MOVE 'B' TO WS-CELL(2)
           GOBACK
           .
""")
        interp = Interpreter(p, {}, defaults=io_defaults(p, "bare"))
        interp.run("OC-MAIN")
        from frameladder.layout import place_occurrences
        self.assertEqual(place_occurrences(p.model, "WS-CELL", {1: "A", 2: "B"}),
                         interp.state.get("WS-TAB"))

    def test_a_variable_subscript_is_left_alone(self):
        # `WS-CELL(WS-I)` names whichever occurrence the index holds at that
        # moment. That is a different question and is not guessed at.
        from frameladder.layout import occurrence_span
        p = program(self.SRC)
        self.assertIsNotNone(occurrence_span(p.model, "WS-CELL"))
        _p, plan = self._plan(self.SRC.replace("WS-CELL(2)", "WS-CELL(WS-IDX)"))
        self.assertNotIn("WS-TAB", plan.input_state())

    def test_a_field_that_does_not_occur_has_no_span(self):
        from frameladder.layout import occurrence_span
        p = program(self.SRC)
        self.assertIsNone(occurrence_span(p.model, "WS-OK"))


class TestReachProfile(unittest.TestCase):
    """How far along its own chain a failing plan actually got."""

    SRC = HEADER + """       01  WS-A PIC X.
       01  WS-B PIC X.
       PROCEDURE DIVISION.
       RP-MAIN.
           IF WS-A = 'A'
              PERFORM RP-MID
           END-IF
           GOBACK
           .
       RP-MID.
           IF WS-B = 'B'
              PERFORM RP-DEEP
           END-IF
           GOBACK
           .
       RP-DEEP.
           CONTINUE
           .
"""

    def test_the_sink_records_the_reached_prefix(self):
        # The distribution is the whole diagnosis for the largest
        # disposition: a run that gets 2/3 of the way failed at the guard
        # admitting the last hop, and one that gets 1/3 never got going.
        # Those want completely different fixes.
        from frameladder.cli import _verify_direction
        from frameladder.coverage import branches_of
        from frameladder.ir import Plan
        prog = program(self.SRC)
        branch = [b for b in branches_of(prog) if b.paragraph == "RP-DEEP"] or \
            [b for b in branches_of(prog) if b.paragraph == "RP-MID"]
        empty = Plan(target="RP-MID", chain=["RP-MAIN", "RP-MID"], edges=[],
                     atoms=[], bindings=[], rendezvous=[], open_obligations=[])
        sink: dict = {}
        verdict, detail = _verify_direction(prog, empty, branch[0], True,
                                            "RP-MAIN", sink=sink)
        self.assertEqual(verdict, "target_not_reached")
        self.assertEqual(sink["chain"], 2)
        self.assertEqual(sink["reached"], 1)      # RP-MAIN entered, RP-MID not
        self.assertEqual(sink["missing"], "RP-MID")
        self.assertIn("1/2", detail)

    def test_the_sink_is_optional(self):
        from frameladder.cli import _verify_direction
        from frameladder.coverage import branches_of
        from frameladder.ir import Plan
        prog = program(self.SRC)
        branch = branches_of(prog)[0]
        empty = Plan(target="RP-MID", chain=["RP-MAIN"], edges=[], atoms=[],
                     bindings=[], rendezvous=[], open_obligations=[])
        verdict, _detail = _verify_direction(prog, empty, branch, True,
                                             "RP-MAIN")
        self.assertIn(verdict, ("target_not_reached", "verified",
                                "wrong_direction", "decision_not_observed"))


class TestReachingDefinition(unittest.TestCase):
    """The nearest preceding write is the value at the read.

    Everything a caller does between paragraph entry and the PERFORM matters:
    its guards, its earlier exits, and its state changes. The first two were
    already modelled; the third was not, and the failure was silent.
    """

    def _plan(self, caller_body):
        from frameladder.ladder import build_plan
        p = program(HEADER + """       01  WS-FLAG PIC X.
       01  WS-IN   PIC X.
       01  WS-HIT  PIC X.
       PROCEDURE DIVISION.
       RD-MAIN.
           PERFORM RD-CALLER
           GOBACK
           .
       RD-CALLER.
""" + caller_body + """           .
       RD-TARGET.
           MOVE 'Y' TO WS-HIT
           .
       RD-DONE.
           EXIT
           .
""")
        return p, build_plan(p, "RD-TARGET", entry="RD-MAIN")

    def _runs(self, p, plan):
        from frameladder.conformance_defaults import io_defaults
        from frameladder.interpreter import Interpreter
        interp = Interpreter(p, plan.input_state(), stubs=plan.stub_plan(),
                             terminals=plan.terminals,
                             defaults=io_defaults(p, "bare"))
        interp.run("RD-MAIN")
        return interp.state.get("WS-HIT") == "Y"

    def test_a_later_unconditional_literal_is_not_walked_past(self):
        # The plan used to bind WS-IN through the *first* MOVE, ignore the
        # second, report no open obligation, and never reach the target.
        # Bound, unreported, and wrong - the worst shape there is.
        _p, plan = self._plan("""           MOVE WS-IN TO WS-FLAG
           MOVE 'N' TO WS-FLAG
           IF WS-FLAG = 'Y'
              PERFORM RD-TARGET
           END-IF""")
        self.assertTrue(plan.open_obligations,
                        "the route is impossible and must say so")
        self.assertNotIn("WS-IN", plan.input_state())

    def test_a_guard_on_the_callsite_still_solves(self):
        p, plan = self._plan("""           IF WS-FLAG = 'Y'
              PERFORM RD-TARGET
           END-IF""")
        self.assertEqual(plan.open_obligations, [])
        self.assertTrue(self._runs(p, plan))

    def test_a_state_change_before_the_callsite_still_lifts(self):
        # The write is a rename, so the obligation transfers to its source.
        p, plan = self._plan("""           MOVE WS-IN TO WS-FLAG
           IF WS-FLAG = 'Y'
              PERFORM RD-TARGET
           END-IF""")
        self.assertEqual(plan.input_state().get("WS-IN"), "Y")
        self.assertTrue(self._runs(p, plan))

    def test_an_earlier_exit_is_still_avoided(self):
        p, plan = self._plan("""           IF WS-IN = 'Q'
              GO TO RD-DONE
           END-IF
           IF WS-FLAG = 'Y'
              PERFORM RD-TARGET
           END-IF""")
        self.assertNotEqual(plan.input_state().get("WS-IN"), "Q")
        self.assertTrue(self._runs(p, plan))

    def test_a_conditional_literal_is_still_steerable(self):
        # A write under a guard can be avoided, so it must NOT become the
        # reaching definition - that is `blocking_writes`' job, and turning it
        # into a hard literal would call a solvable route impossible.
        p, plan = self._plan("""           MOVE WS-IN TO WS-FLAG
           IF WS-IN = 'Z'
              MOVE 'N' TO WS-FLAG
           END-IF
           IF WS-FLAG = 'Y'
              PERFORM RD-TARGET
           END-IF""")
        self.assertEqual(plan.open_obligations, [])
        self.assertTrue(self._runs(p, plan))


class TestProducerBacktracking(unittest.TestCase):
    """A refused producer is not a dead end when the field has another writer.

    Choosing between writers is choosing between alternatives the *program*
    left open - the same licence route ordering already has. What it must
    never do is decide that a target is unreachable because the harness is
    narrow; see the invariant in AGENTS.md.
    """

    SRC = HEADER + """       01  WS-KEY  PIC X(4).
       01  WS-IN   PIC X(4).
       01  WS-MODE PIC X.
       01  WS-HIT  PIC X.
       PROCEDURE DIVISION.
       PB-MAIN.
           IF WS-MODE = 'F'
              PERFORM PB-LOAD
           END-IF
           IF WS-MODE = 'M'
              MOVE WS-IN TO WS-KEY
           END-IF
           IF WS-KEY = 'GOOD'
              PERFORM PB-TARGET
           END-IF
           GOBACK
           .
       PB-LOAD.
           READ INFILE INTO WS-KEY
           .
       PB-TARGET.
           MOVE 'Y' TO WS-HIT
           .
"""

    def test_a_narrow_harness_never_makes_a_target_unsolvable(self):
        # The invariant. Walking past every producer and returning nothing
        # would let a harness limitation decide what is required. Measured
        # before the fallback existed: one program lost 11 of 12 solved plans.
        from frameladder.capability import load
        from frameladder.ladder import build_plan
        cap = load({"schema_version": "1.0",
                    "injectable_variables": [],
                    "replayable_operations": []})
        plan = build_plan(program(self.SRC), "PB-TARGET", entry="PB-MAIN",
                          capability=cap)
        self.assertTrue(plan.chain, "a narrow profile must not lose the route")

    def test_no_profile_leaves_the_walk_untouched(self):
        # The whole mechanism is inert unless a harness has stated limits:
        # dispositions over 3,288 corpus directions are identical either way.
        from frameladder.ladder import build_plan
        bare = build_plan(program(self.SRC), "PB-TARGET", entry="PB-MAIN")
        stated = build_plan(program(self.SRC), "PB-TARGET", entry="PB-MAIN",
                            capability=None)
        self.assertEqual(bare.input_state(), stated.input_state())

    def test_the_walk_prefers_a_producer_the_harness_can_deliver(self):
        from frameladder.capability import load, unrepresentable
        from frameladder.ladder import build_plan
        cap = load({"schema_version": "1.0",
                    "injectable_variables": ["WS-IN", "WS-MODE", "WS-KEY"],
                    "replayable_operations": []})
        plan = build_plan(program(self.SRC), "PB-TARGET", entry="PB-MAIN",
                          capability=cap)
        self.assertEqual(unrepresentable(plan, cap), [])
class TestFreeIOSlots(unittest.TestCase):
    """A plan pins the operations its obligations reached; the rest take the
    world, and `bare` was the only world the verification path ever tried.

    Measured over CardDemo's 3,288 branch directions, `bare` alone verifies
    804 and the three worlds verify 938 - all of the difference on the ten
    programs that declare a file, and exactly zero on the other nineteen.
    """

    SRC = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INF
               ORGANIZATION IS INDEXED
               ACCESS MODE IS SEQUENTIAL
               RECORD KEY IS IN-KEY
               FILE STATUS IS WS-ST.
       DATA DIVISION.
       FILE SECTION.
       FD IN-FILE.
       01 IN-REC.
          05 IN-KEY  PIC X(4).
       WORKING-STORAGE SECTION.
       01 WS-ST  PIC X(2).
       01 WS-EOF PIC X(1) VALUE 'N'.
       PROCEDURE DIVISION.
       FIO-MAIN.
           OPEN INPUT IN-FILE
           PERFORM UNTIL WS-EOF = 'Y'
              READ IN-FILE
                 AT END MOVE 'Y' TO WS-EOF
              END-READ
           END-PERFORM
           GOBACK
           .
"""

    def _bits(self):
        # The `AT END` of the read loop, which is the shape of batch COBOL and
        # the one decision no entry state can reach: the value that decides it
        # comes from the READ, and the plan pins no outcome for it. It is a
        # free I/O slot in exactly the sense a slot no obligation touched is a
        # free input slot.
        from frameladder.coverage import branches_of
        prog = program(self.SRC)
        branch = [b for b in branches_of(prog) if b.kind == "PHRASE"][0]
        return prog, branch

    def test_bare_alone_cannot_reach_the_end_of_an_indexed_file(self):
        # An indexed READ with no data staged gives 35, not 10, so `AT END`
        # never fires and the direction is reported as taken the other way.
        from frameladder.cli import _verify_direction
        from frameladder.ladder import plan_for_branch
        prog, branch = self._bits()
        plan = plan_for_branch(prog, branch.paragraph, branch.line, True,
                               entry="FIO-MAIN", ordinal=branch.ordinal)
        self.assertFalse(plan.stub_plan(), "the plan pins no outcome here")
        verdict, _detail = _verify_direction(prog, plan, branch, True,
                                             "FIO-MAIN")
        self.assertEqual(verdict, "wrong_direction")

    def test_offering_the_worlds_reaches_it(self):
        from frameladder.cli import _verify_direction
        from frameladder.conformance_defaults import WORLDS
        from frameladder.ladder import plan_for_branch
        prog, branch = self._bits()
        plan = plan_for_branch(prog, branch.paragraph, branch.line, True,
                               entry="FIO-MAIN", ordinal=branch.ordinal)
        sink: dict = {}
        verdict, _detail = _verify_direction(prog, plan, branch, True,
                                             "FIO-MAIN", sink=sink,
                                             worlds=WORLDS)
        self.assertEqual(verdict, "verified")
        # Which world it took is part of the answer: a candidate that does not
        # say so is one the harness will stage the wrong way.
        self.assertEqual(sink["world"], "empty")

    def test_the_other_direction_still_needs_the_other_world(self):
        # Both directions of one decision, and no single world gives both.
        # That is the mechanism stated as a property rather than a count.
        from frameladder.cli import _verify_direction
        from frameladder.conformance_defaults import WORLDS
        from frameladder.ladder import plan_for_branch
        prog, branch = self._bits()
        plan = plan_for_branch(prog, branch.paragraph, branch.line, False,
                               entry="FIO-MAIN", ordinal=branch.ordinal)
        sink: dict = {}
        verdict, _detail = _verify_direction(prog, plan, branch, False,
                                             "FIO-MAIN", sink=sink,
                                             worlds=WORLDS)
        self.assertEqual(verdict, "verified")
        self.assertNotEqual(sink["world"], "empty")

    def test_the_default_is_still_one_run_in_bare(self):
        # Every existing caller, and the conformance harnesses that compare
        # against GnuCOBOL with no files staged, must see what they saw.
        import inspect
        from frameladder.cli import _verify_direction
        signature = inspect.signature(_verify_direction)
        self.assertEqual(signature.parameters["worlds"].default, ("bare",))
        self.assertEqual(signature.parameters["states"].default, ())


class TestExecAxisWorlds(unittest.TestCase):
    """`io_defaults` spoke only about files, so a program with no SELECT got an
    empty dict and all three worlds were the identical run - 19 of CardDemo's
    29 programs, and 120 of its 218 external operations."""

    SRC = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 SQLCODE PIC S9(9) COMP.
       PROCEDURE DIVISION.
       EX-MAIN.
           EXEC SQL SELECT A INTO :SQLCODE FROM T END-EXEC
           IF SQLCODE = 100
              CONTINUE
           END-IF
           GOBACK
           .
"""

    def test_bare_says_nothing_about_an_exec(self):
        from frameladder.conformance_defaults import io_defaults
        prog = program(self.SRC)
        self.assertEqual(io_defaults(prog, "bare"), {})

    def test_the_empty_world_gives_sql_its_not_found_code(self):
        from frameladder.conformance_defaults import io_defaults
        prog = program(self.SRC)
        found = io_defaults(prog, "empty")
        self.assertTrue(found, "the EXEC axis should not be silent")
        self.assertTrue(any(v.get("SQLCODE") == 100 for v in found.values()))

    def test_the_populated_world_gives_sql_success(self):
        from frameladder.conformance_defaults import io_defaults
        prog = program(self.SRC)
        found = io_defaults(prog, "populated")
        self.assertTrue(any(v.get("SQLCODE") == 0 for v in found.values()))

    def test_a_channel_comes_from_the_source_not_the_name(self):
        # `faults.channel_of` is evidence-only, and this is the property that
        # keeps the world model from becoming a naming heuristic: a field
        # spelled like a status but never put in one gets nothing.
        from frameladder.conformance_defaults import exec_channels
        prog = program("""       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01 WS-FILE-STATUS PIC X(2).
       PROCEDURE DIVISION.
       EN-MAIN.
           CALL 'SUB' USING WS-FILE-STATUS
           GOBACK
           .
""")
        for channels in exec_channels(prog).values():
            self.assertNotIn("WS-FILE-STATUS", channels)


class TestFreeInputSlots(unittest.TestCase):
    """The obligations pin some slots and leave the rest; the export path
    never filled the remainder, so every run took the same defaults."""

    def test_the_pool_is_the_programs_own_literals(self):
        from frameladder.cli import _overlay_pool
        prog = program(HEADER + """       01 WS-A PIC X(1).
       01 WS-B PIC X(1).
       PROCEDURE DIVISION.
       OV-MAIN.
           IF WS-A = 'Y'
              CONTINUE
           END-IF
           GOBACK
           .
""")
        pool = _overlay_pool(prog)
        self.assertIn("Y", pool.get("WS-A", []))
        # And a complement, or the negative direction of its own comparison
        # has no value to be sampled into.
        self.assertGreater(len(pool.get("WS-A", [])), 1)

    def test_a_profile_that_cannot_inject_a_field_keeps_it_out(self):
        # An overlay the harness will drop in projection must never be the
        # reason a plan was called verified.
        from frameladder.capability import Capability
        from frameladder.cli import _overlay_pool
        prog = program(HEADER + """       01 WS-A PIC X(1).
       PROCEDURE DIVISION.
       OV-MAIN.
           IF WS-A = 'Y'
              CONTINUE
           END-IF
           GOBACK
           .
""")
        narrow = Capability(stated=True, injectable=frozenset({"WS-OTHER"}))
        self.assertNotIn("WS-A", _overlay_pool(prog, narrow))

    def test_overlays_keep_every_value_the_plan_derived(self):
        from frameladder.cli import _overlay_pool, _overlay_states
        from frameladder.ladder import build_plan
        prog = program(HEADER + """       01 WS-A PIC X(1).
       01 WS-B PIC X(1).
       PROCEDURE DIVISION.
       OS-MAIN.
           IF WS-A = 'Y'
              PERFORM OS-DEEP
           END-IF
           GOBACK
           .
       OS-DEEP.
           IF WS-B = 'Z'
              CONTINUE
           END-IF
           GOBACK
           .
""")
        plan = build_plan(prog, "OS-DEEP", entry="OS-MAIN")
        states = _overlay_states(plan, _overlay_pool(prog), 3, seed=7)
        self.assertEqual(len(states), 3)
        for state in states:
            for name, value in plan.input_state().items():
                self.assertEqual(state[name], value)

    def test_the_draws_are_seeded(self):
        from frameladder.cli import _overlay_pool, _overlay_states
        from frameladder.ladder import build_plan
        prog = program(HEADER + """       01 WS-A PIC X(1).
       PROCEDURE DIVISION.
       SD-MAIN.
           IF WS-A = 'Y'
              CONTINUE
           END-IF
           GOBACK
           .
""")
        plan = build_plan(prog, "SD-MAIN", entry="SD-MAIN")
        pool = _overlay_pool(prog)
        self.assertEqual(_overlay_states(plan, pool, 4, seed=3),
                         _overlay_states(plan, pool, 4, seed=3))


class TestTheWorldIsPartOfTheCandidate(unittest.TestCase):
    """A plan verified with the files present and replayed with them absent
    abends at its first OPEN and reports covering nothing. The world the
    verification used therefore travels with the candidate, and a harness that
    cannot set it up is told so rather than left to discover it."""

    def _plan(self):
        from frameladder.ir import Plan
        return Plan(target="X", chain=["A"], edges=[], atoms=[], bindings=[],
                    rendezvous=[], open_obligations=[])

    def test_the_world_is_named_and_spelled_out(self):
        from frameladder.replay import replay_script
        script = replay_script(self._plan(), entry="A", io_world="populated",
                               io_defaults={"READ:F": {"WS-ST": "00"}})
        self.assertEqual(script["io_world"], "populated")
        self.assertEqual(script["io_defaults"], {"READ:F": {"WS-ST": "00"}})

    def test_a_harness_that_cannot_drive_the_operation_is_refused(self):
        from frameladder.capability import Capability, Operation
        from frameladder.replay import replay_script
        narrow = Capability(stated=True,
                            operations={"WRITE:G": Operation("WRITE:G")})
        script = replay_script(self._plan(), narrow, entry="A",
                               io_world="populated",
                               io_defaults={"READ:F": {"WS-ST": "00"}})
        self.assertFalse(script["representable"])
        self.assertTrue(any("READ:F" in r for r in script["reasons"]))

    def test_an_overlaid_state_is_the_one_exported(self):
        from frameladder.replay import replay_script
        script = replay_script(self._plan(), entry="A",
                               entry_state={"WS-A": "Y"})
        self.assertTrue(script["overlaid"])
        self.assertEqual(script["input_state"], {"WS-A": "Y"})


class TestParagraphSummary(unittest.TestCase):
    """A paragraph as guarded commands, so composition replaces re-derivation.

    Not yet consumed by the planner. It is merged because the conformance
    harness that checks it is worth having in the tree and tracked, exactly as
    `microdiff` is at 24/202 - a bar you can drive down beats a number in a
    conversation.
    """

    SRC = HEADER + """       01  WS-A PIC X.
       01  WS-B PIC X.
       PROCEDURE DIVISION.
       PS-MAIN.
           IF WS-A = 'Y'
              MOVE 'X' TO WS-B
              PERFORM PS-DEEP
           END-IF
           GOBACK
           .
       PS-DEEP.
           CONTINUE
           .
       PS-TAIL.
           EXIT
           .
"""

    def _summary(self, name="PS-MAIN", src=None):
        from frameladder.summary import summarise
        return summarise(program(src or self.SRC), name)

    def test_both_ways_through_a_decision_are_paths(self):
        s = self._summary()
        self.assertEqual(len(s.paths), 2)
        self.assertTrue(s.complete)

    def test_only_one_path_performs_the_guarded_target(self):
        s = self._summary()
        reaching = s.paths_reaching("PS-DEEP")
        self.assertEqual(len(reaching), 1)
        self.assertTrue(reaching[0].condition)

    def test_writes_before_a_call_are_ordered_and_visible(self):
        # The last-hop question in one line: a value bound at paragraph entry
        # survives to the call only if nothing here overwrote it. That is what
        # the planner could not see.
        s = self._summary()
        path = s.paths_reaching("PS-DEEP")[0]
        self.assertEqual([w.var for w in path.writes_before("PS-DEEP")],
                         ["WS-B"])

    def test_a_thru_range_names_every_paragraph_it_runs(self):
        # Recorded as one call to a paragraph literally named "A THRU B" it
        # matches nothing, and the summary then predicts none of the calls the
        # range makes - worth 2.7 points of corpus agreement on its own.
        src = HEADER + """       01  WS-A PIC X.
       PROCEDURE DIVISION.
       PS-MAIN.
           PERFORM PS-DEEP THRU PS-TAIL
           GOBACK
           .
       PS-DEEP.
           CONTINUE
           .
       PS-MIDDLE.
           CONTINUE
           .
       PS-TAIL.
           EXIT
           .
"""
        calls = self._summary(src=src).summary()["calls"]
        self.assertEqual(calls, ["PS-DEEP", "PS-MIDDLE", "PS-TAIL"])

    def test_a_loop_makes_the_summary_incomplete_rather_than_wrong(self):
        # A caller may use an incomplete summary as evidence that a path
        # exists, never as evidence that one does not. That distinction is
        # the difference between "no plan on this chain" and "this is dead".
        src = HEADER + """       01  WS-I PIC 9(4).
       PROCEDURE DIVISION.
       PS-MAIN.
           PERFORM PS-DEEP UNTIL WS-I > 3
           GOBACK
           .
       PS-DEEP.
           ADD 1 TO WS-I
           .
"""
        s = self._summary(src=src)
        self.assertFalse(s.complete)
        self.assertIn("loop", s.why_partial)

    def test_an_unknown_paragraph_is_incomplete_not_empty(self):
        s = self._summary(name="NO-SUCH-PARA")
        self.assertFalse(s.complete)
        self.assertEqual(s.paths, ())

    def test_every_paragraph_of_a_program_is_summarised(self):
        from frameladder.summary import summarise_program
        prog = program(self.SRC)
        self.assertEqual(set(summarise_program(prog)),
                         set(prog.paragraph_names))


class TestConditionNamesAreNotOperands(unittest.TestCase):
    """`UNTIL WS-IDX >= 11 OR USER-EOF` tests the flag, not `WS-IDX >= flag`.

    The abbreviated-relation expansion restored the subject onto every bare
    part; a level-88 name became an operand, the comparison against its
    empty pseudo-value was true from the first iteration, and every read
    loop written in this (entirely standard) style ran zero times.
    """

    SRC = HEADER + """       01  WS-IDX PIC S9(4) COMP VALUE 0.
       01  WS-EOF-FLG PIC X VALUE 'N'.
           88 AT-EOF VALUE 'Y'.
       01  WS-COUNT PIC 9(4) VALUE 0.
       PROCEDURE DIVISION.
       MAIN-PARA.
           MOVE 1 TO WS-IDX
           PERFORM UNTIL WS-IDX >= 4 OR AT-EOF
               ADD 1 TO WS-COUNT
               ADD 1 TO WS-IDX
           END-PERFORM
           GOBACK
           .
"""

    def test_the_loop_runs_when_the_flag_is_off(self):
        from frameladder.interpreter import Interpreter
        from frameladder.ir import parse_term
        prog = program(self.SRC)
        interp = Interpreter(prog, {})
        interp.run("MAIN-PARA")
        self.assertEqual(interp.value_of(parse_term("WS-COUNT")), 3)

    def test_the_name_is_only_special_when_declared(self):
        from frameladder.conditions import condition_atoms
        with_names = condition_atoms("WS-IDX >= 4 OR AT-EOF",
                                     names=frozenset({"AT-EOF"}))
        self.assertEqual([str(a) for alt in with_names for a in alt],
                         ["WS-IDX >= 4", "AT-EOF = True"])
        without = condition_atoms("WS-IDX >= 4 OR AT-EOF")
        self.assertIn("WS-IDX >= AT-EOF",
                      [str(a) for alt in without for a in alt])


class TestStagedStubSearch(unittest.TestCase):
    """The battery phase that works backward from an unwitnessed direction
    to the operation whose staged outcome takes it."""

    SRC = HEADER + """       01  WS-RC PIC S9(8) COMP VALUE 0.
       PROCEDURE DIVISION.
       MAIN-PARA.
           PERFORM READ-THING
           GOBACK
           .
       READ-THING.
           EXEC CICS READ DATASET(WS-FILE) INTO(WS-REC) RESP(WS-RC)
           END-EXEC
           EVALUATE WS-RC
               WHEN DFHRESP(NORMAL)
                   CONTINUE
               WHEN DFHRESP(NOTFND)
                   CONTINUE
               WHEN OTHER
                   CONTINUE
           END-EVALUATE
           .
"""

    def _search(self, budget=60):
        from frameladder import stubsearch
        from frameladder.conformance_defaults import io_defaults
        from frameladder.interpreter import Interpreter
        from frameladder.ladder import analyse
        from frameladder.ledger import Ledger
        prog = program(self.SRC)
        graph, prov = analyse(prog)
        ledger = Ledger()

        def run(state, world, stubs, terminals, source):
            interp = Interpreter(prog, dict(state or {}), stubs=stubs,
                                 terminals=terminals,
                                 defaults=io_defaults(prog, world))
            trace = interp.run("MAIN-PARA")
            return ledger.credit(trace, state or {}, world, stubs,
                                 terminals, source)

        run({}, "populated", None, None, "seed")
        stats = stubsearch.search(prog, prov, graph, ledger, run,
                                  budget=budget)
        return prog, ledger, stats

    def test_every_arm_direction_is_witnessed_by_staging_the_resp(self):
        from frameladder.ledger import missing
        prog, ledger, stats = self._search()
        self.assertEqual(missing(prog, ledger), [])
        self.assertGreater(stats["directions_witnessed"], 0)

    def test_every_witness_reproduces_from_its_stored_recipe(self):
        from frameladder.conformance_defaults import io_defaults
        from frameladder.interpreter import Interpreter
        from frameladder.lift import direction_key
        prog, ledger, _stats = self._search()
        for key, recipe in ledger.witnesses.items():
            payload = recipe.payload()
            interp = Interpreter(prog, dict(payload["input_state"]),
                                 stubs=payload["stubs"],
                                 terminals=payload["terminals"],
                                 defaults=io_defaults(prog,
                                                      payload["world"]))
            trace = interp.run("MAIN-PARA")
            self.assertIn(key, {direction_key(g) for g in trace.guards})

    def test_the_index_names_every_arm(self):
        from frameladder import stubsearch
        prog = program(self.SRC)
        info = stubsearch.branch_index(prog)
        self.assertIn(("READ-THING", 2, "WHEN"), info)

    def test_staging_merges_over_the_base_recipes_own_stubs(self):
        # A base whose plan already stages the operation keeps its other
        # fields: replacing the entry list threw away the staging that made
        # the base reach anywhere.
        from frameladder import stubsearch
        prog = program(self.SRC)
        base = ({}, "populated",
                {"EXEC:CICS:READ": [{"when": {}, "set": {"WS-REC": "AA"},
                                     "seq": 0, "inferred": False}]},
                {})
        actions = [("stub", "EXEC:CICS:READ", {}, "WS-RC", 13,
                    "READ-THING")]
        state, world, stubs, terminals = next(iter(
            stubsearch.staged_recipes(prog.model, base, actions)))
        entry = stubs["EXEC:CICS:READ"][0]
        self.assertEqual(entry["set"].get("WS-REC"), "AA")
        self.assertEqual(entry["set"].get("WS-RC"), 13)


class TestReentry(unittest.TestCase):
    """Runs shaped to complete cycle 1 and re-enter (frameladder.reentry).

    A pseudo-conversational program keeps its state machine in the
    commarea and most of its source runs only on a second task. These pin
    the evidence the shapes are derived from, and the interpreter's task
    boundary: what cycle 1 saves is what cycle 2 receives, and the entry
    state speaks only at input boundaries - the first task's commarea and
    every RECEIVE - never over a later cycle's own writes.
    """

    SRC = """       IDENTIFICATION DIVISION.
       PROGRAM-ID. RE.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-TRANID PIC X(4) VALUE 'TT01'.
       01  CARDDEMO-COMMAREA.
           05  CDEMO-FLAG PIC X VALUE 'N'.
               88  CDEMO-REENTER VALUE 'Y'.
           05  CDEMO-FROM PIC X(8).
       01  SCREEN-AREA.
           05  NAMEI PIC X(2).
       PROCEDURE DIVISION.
       MAIN-PARA.
           IF EIBCALEN = 0
               GOBACK
           END-IF
           MOVE DFHCOMMAREA(1:EIBCALEN) TO CARDDEMO-COMMAREA
           IF NOT CDEMO-REENTER
               SET CDEMO-REENTER TO TRUE
               MOVE 'PGMONE' TO CDEMO-FROM
           ELSE
               EXEC CICS RECEIVE MAP('M') INTO(SCREEN-AREA) END-EXEC
               EVALUATE EIBAID
                   WHEN DFHENTER
                       PERFORM CHECK-NAME
                   WHEN DFHPF3
                       GOBACK
               END-EVALUATE
           END-IF
           EXEC CICS RETURN TRANSID(WS-TRANID)
                COMMAREA(CARDDEMO-COMMAREA) END-EXEC.
       CHECK-NAME.
           IF NAMEI = 'AB'
               CONTINUE
           END-IF
           IF CDEMO-FROM = 'PGMONE'
               CONTINUE
           END-IF.
"""

    def _directions(self, prog, state):
        from frameladder.ledger import Ledger
        led = Ledger()
        trace = Interpreter(prog, dict(state)).run("MAIN-PARA")
        led.credit(trace, state, "bare", {}, {}, "test")
        return {(p, k, d) for (p, _o, k, d) in led.witnesses}

    def test_return_commarea_is_the_evidence_gate(self):
        from frameladder import reentry
        prog = program(self.SRC)
        self.assertEqual(reentry.return_commareas(prog),
                         ["CARDDEMO-COMMAREA"])
        batch = program(HEADER + """       PROCEDURE DIVISION.
       B-MAIN.
           GOBACK.
""")
        self.assertEqual(reentry.return_commareas(batch), [])
        self.assertEqual(reentry.reentry_states(batch, {}), [])

    def test_aid_values_come_from_the_source_comparisons(self):
        from frameladder import reentry
        prog = program(self.SRC)
        # DFHENTER and DFHPF3 are compared; DFHPF12 is not, so its byte
        # must not be offered - the table only says what a name stands for.
        self.assertEqual(reentry.aid_comparisons(prog),
                         {"EIBAID": ["'", "3"]})

    def test_evaluate_true_spelling_is_the_same_evidence(self):
        from frameladder import reentry
        prog = program(HEADER + """       01  WS-T PIC X(4) VALUE 'TT'.
       01  CA.
           05  CA-F PIC X.
       PROCEDURE DIVISION.
       M-PARA.
           EVALUATE TRUE
               WHEN EIBAID IS EQUAL TO DFHPF5
                   CONTINUE
               WHEN OTHER
                   CONTINUE
           END-EVALUATE
           EXEC CICS RETURN TRANSID(WS-T) COMMAREA(CA) END-EXEC.
""")
        self.assertEqual(reentry.aid_comparisons(prog), {"EIBAID": ["5"]})

    def test_states_carry_a_commarea_length_and_one_key_each(self):
        from frameladder import reentry
        prog = program(self.SRC)
        states = reentry.reentry_states(prog, {"NAMEI": ["AB"]})
        self.assertTrue(states)
        for _name, state in states:
            self.assertEqual(state["EIBCALEN"], 9)     # X(1) + X(8)
            self.assertIn(state["EIBAID"], ("'", "3"))

    def test_one_recipe_spans_the_cycles(self):
        # Cycle 1 sets the re-enter flag and saves it; cycle 2 receives the
        # map and dispatches on the key. One entry state takes directions on
        # both sides of the task boundary - and the flag arrives set by the
        # program, not by the entry state, which never names it.
        prog = program(self.SRC)
        taken = self._directions(prog, {"EIBCALEN": 9, "EIBAID": "'",
                                        "NAMEI": "AB"})
        self.assertIn(("MAIN-PARA", "IF", False), taken)     # cycle 1: no flag
        self.assertIn(("CHECK-NAME", "IF", True), taken)     # cycle 2: dispatched
        # And replayable: a fresh interpreter takes the same directions.
        self.assertEqual(taken, self._directions(
            prog, {"EIBCALEN": 9, "EIBAID": "'", "NAMEI": "AB"}))

    def test_cycle_two_sees_what_cycle_one_wrote_not_the_entry(self):
        # Cycle 1 writes PGMONE over the entry's CDEMO-FROM. The second
        # cycle must see the program's value: the commarea belongs to the
        # previous cycle, and the entry state may not overwrite it.
        prog = program(self.SRC)
        taken = self._directions(prog, {"EIBCALEN": 9, "EIBAID": "'",
                                        "NAMEI": "AB",
                                        "CDEMO-FROM": "OTHERPGM"})
        self.assertIn(("CHECK-NAME", "IF", True), taken)

    def test_a_childless_saved_area_carries_bytes(self):
        # COACTUPC's pattern: the RETURN area is PIC X(n) assembled by
        # slices, so there are no child fields to carry - the bytes are the
        # only carrier, and dropping them makes every task look first.
        prog = program(HEADER + """       01  WS-T PIC X(4) VALUE 'TT'.
       01  WS-SAVE PIC X(9).
       01  CA.
           05  CA-FLAG PIC X.
               88  CA-REENTER VALUE 'Y'.
           05  CA-FROM PIC X(8).
       PROCEDURE DIVISION.
       M-PARA.
           MOVE DFHCOMMAREA(1:9) TO CA
           IF NOT CA-REENTER
               SET CA-REENTER TO TRUE
           ELSE
               PERFORM M-DEEP
           END-IF
           MOVE CA TO WS-SAVE
           EXEC CICS RETURN TRANSID(WS-T) COMMAREA(WS-SAVE) END-EXEC.
       M-DEEP.
           CONTINUE.
""")
        trace = Interpreter(prog, {"EIBCALEN": 9}).run("M-PARA")
        self.assertIn("M-DEEP", trace.entered)

    def test_entry_names_the_first_commarea_only(self):
        from frameladder import reentry
        prog = program(self.SRC)
        # CDEMO-FROM is a commarea target field: the entry state stands for
        # what the caller staged, so it survives the first task's move...
        taken = self._directions(prog, {"EIBCALEN": 9,
                                        "CDEMO-FROM": "PGMX"})
        self.assertIn(("MAIN-PARA", "IF", False), taken)
        # ...and the evidence walk offers the field a value at all.
        self.assertIn("CARDDEMO-COMMAREA", reentry.commarea_targets(prog))

    def test_refmod_slices_assemble_a_template(self):
        from frameladder import reentry
        prog = program(HEADER + """       01  WS-T PIC X(4) VALUE 'TT'.
       01  CA.
           05  CA-F PIC X.
       01  DATEI PIC X(5).
       PROCEDURE DIVISION.
       M-PARA.
           EVALUATE TRUE
               WHEN DATEI(1:2) IS NOT NUMERIC
                   CONTINUE
               WHEN DATEI(3:1) NOT EQUAL '-'
                   CONTINUE
               WHEN DATEI(4:2) IS NOT NUMERIC
                   CONTINUE
           END-EVALUATE
           EXEC CICS RETURN TRANSID(WS-T) COMMAREA(CA) END-EXEC.
""")
        self.assertEqual(reentry._refmod_templates(prog).get("DATEI"),
                         "11-11")

    def test_resp_fault_worlds_use_the_programs_own_codes(self):
        from frameladder import reentry
        prog = program(HEADER + """       01  WS-T PIC X(4) VALUE 'TT'.
       01  WS-RC PIC S9(8) COMP.
       01  CA.
           05  CA-F PIC X.
       01  REC.
           05  REC-F PIC X(4).
       PROCEDURE DIVISION.
       M-PARA.
           EXEC CICS READ DATASET('F') INTO(REC) RESP(WS-RC) END-EXEC
           EVALUATE WS-RC
               WHEN DFHRESP(NORMAL)
                   CONTINUE
               WHEN DFHRESP(NOTFND)
                   CONTINUE
           END-EVALUATE
           EXEC CICS RETURN TRANSID(WS-T) COMMAREA(CA) END-EXEC.
""")
        worlds = reentry.resp_fault_worlds(prog, {"WS-RC": [0, 13]})
        self.assertTrue(worlds)
        codes = {entry["set"]["WS-RC"]
                 for spec in worlds
                 for entry in spec["stubs"]["EXEC:CICS:READ"]}
        self.assertIn(13, codes)                      # the compared fault
        self.assertNotIn(19, codes)                   # never a whole table


class TestChain(unittest.TestCase):
    """Goal-directed backward chaining: local solve, producers, refusals."""

    SOURCE = HEADER + """       01  WS-IN            PIC X(2).
       01  WS-MODE          PIC X.
           88  MODE-GOOD    VALUE 'G'.
           88  MODE-BAD     VALUE 'B'.
       01  WS-FLAG          PIC X.
           88  FLAG-ON      VALUE 'Y'.
           88  FLAG-OFF     VALUE 'N'.
       PROCEDURE DIVISION.
       0000-MAIN.
           PERFORM 1000-PRODUCE THRU 1000-PRODUCE-EXIT
           PERFORM 2000-DECIDE THRU 2000-DECIDE-EXIT
           GOBACK.
       1000-PRODUCE.
           IF WS-IN EQUAL 'OK'
              SET FLAG-ON       TO TRUE
           ELSE
              SET FLAG-OFF      TO TRUE
           END-IF
           .
       1000-PRODUCE-EXIT.
           EXIT.
       2000-DECIDE.
           IF FLAG-ON
              CONTINUE
           ELSE
              CONTINUE
           END-IF
           .
       2000-DECIDE-EXIT.
           EXIT.
"""

    def _index(self, prog):
        from frameladder import chain
        return chain._Index(prog)

    def _analysed(self, prog):
        from frameladder.ladder import analyse
        return analyse(prog)

    def test_local_solve_fires_both_directions(self):
        from frameladder import chain
        prog = program(self.SOURCE)
        index = self._index(prog)
        _graph, prov = self._analysed(prog)
        branch = next(b for b in __import__("frameladder.coverage",
                                            fromlist=["branches_of"])
                      .branches_of(prog) if b.paragraph == "1000-PRODUCE")
        for direction in (True, False):
            goal = (branch.paragraph, branch.ordinal, branch.kind, direction)
            budget = chain._Budget(500)
            candidates, _runs = chain.local_solve(index, prov, goal,
                                                  budget, {})
            self.assertTrue(candidates, "direction %s" % direction)
            # and some minimal assignment names only the deciding variable
            self.assertTrue(any(set(found) <= {"WS-IN"}
                                for found, _st, _full in candidates))

    def test_producer_walk_derives_through_one_hop(self):
        """2000-DECIDE tests a flag only 1000-PRODUCE writes: the chain
        must classify it produced, solve the producer for the output, and
        compose a from-entry recipe that validates."""
        from frameladder import chain
        prog = program(self.SOURCE)
        report = chain.run_chain(prog, budget=2000)
        ledger = report["ledger"]
        decide = [k for k in ledger.witnesses if k[0] == "2000-DECIDE"]
        directions = {k[3] for k in decide}
        self.assertEqual(directions, {True, False})
        # from-disk shape: every witness replays to its direction
        for key, recipe in ledger.witnesses.items():
            payload = recipe.payload()
            interp = Interpreter(prog, dict(payload["input_state"]),
                                 stubs=payload["stubs"] or None,
                                 terminals=payload["terminals"] or None)
            trace = interp.run("0000-MAIN")
            took = {chain._direction_key(g) for g in trace.guards}
            self.assertIn(key, took)

    def test_output_constrained_solve(self):
        from frameladder import chain
        prog = program(self.SOURCE)
        index = self._index(prog)
        _graph, prov = self._analysed(prog)
        budget = chain._Budget(500)
        answer, _runs = chain.producer_solve(index, prov, "1000-PRODUCE",
                                             {"WS-FLAG": "Y"}, budget, {})
        self.assertEqual(answer, {"WS-IN": "OK"})
        # the conjunction case: two required outputs at once
        answer2, _runs = chain.producer_solve(index, prov, "1000-PRODUCE",
                                              {"WS-FLAG": "N"}, budget, {})
        self.assertIsNotNone(answer2)
        self.assertNotEqual(answer2.get("WS-IN"), "OK")

    def test_refusal_on_dead_direction(self):
        """A condition no value can satisfy refuses with a name, never
        credits."""
        from frameladder import chain
        dead = HEADER + """       01  WS-A     PIC X.
       PROCEDURE DIVISION.
       0000-MAIN.
           MOVE 'X' TO WS-A
           IF WS-A EQUAL 'Q'
              CONTINUE
           END-IF
           GOBACK.
"""
        prog = program(dead)
        from frameladder.coverage import branches_of
        branch = next(b for b in branches_of(prog))
        goal = (branch.paragraph, branch.ordinal, branch.kind, True)
        report = chain.run_chain(prog, goals=[goal], budget=600)
        self.assertEqual(report["witnessed"], 0)
        self.assertEqual(sum(report["refusals"].values()), 1)
        self.assertNotIn(goal, report["ledger"].witnesses)

    def test_memoised_sweep_is_shared_per_closure(self):
        from frameladder import chain
        prog = program(self.SOURCE)
        index = self._index(prog)
        _graph, prov = self._analysed(prog)
        from frameladder.coverage import branches_of
        branch = next(b for b in branches_of(prog)
                      if b.paragraph == "1000-PRODUCE")
        cache: dict = {}
        budget = chain._Budget(500)
        chain.local_solve(index, prov,
                          (branch.paragraph, branch.ordinal, branch.kind,
                           True), budget, cache)
        spent_first = budget.spent
        chain.local_solve(index, prov,
                          (branch.paragraph, branch.ordinal, branch.kind,
                           False), budget, cache)
        # the second direction is answered mostly from the shared sweep
        self.assertLess(budget.spent - spent_first, spent_first + 3)
