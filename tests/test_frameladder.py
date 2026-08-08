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
        self.assertEqual(channel_of("WS-RESP", model), "cics")
        # A field that merely looks status-ish is not one; guessing would put
        # file-status codes into fields that are not file statuses.
        self.assertIsNone(channel_of("WS-STATUS-MESSAGE", model))

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
