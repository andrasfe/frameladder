"""Micro-fixture differential: one generic COBOL construct per fixture.

Each fixture is standard COBOL that routes to a distinct paragraph depending
on how the construct behaves.  GnuCOBOL is the oracle; the interpreter is
the subject.  Reuses conformance.differential.compare so the comparison is
the same one the repository already trusts.
"""
import os, sys, tempfile, textwrap

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conformance.differential import compare

FIXTURES = {}


def fixture(name):
    def deco(fn):
        FIXTURES[name] = fn()
        return fn
    return deco


HEAD = """\
       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
"""

TAIL = """\
       YES-P.
           DISPLAY 'YES'
           GO TO DONE-P.
       NO-P.
           DISPLAY 'NO'
           GO TO DONE-P.
       DONE-P.
           GOBACK.
"""


def prog(ws, body):
    return HEAD + ws + "       PROCEDURE DIVISION.\n       MAIN.\n" + body + TAIL


CASES = {

"refmod_condition": prog(
"""       01 WS-A PIC X(10) VALUE 'ABCDEFGHIJ'.
""",
"""           IF WS-A(3:2) = 'CD'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"refmod_move": prog(
"""       01 WS-A PIC X(10) VALUE 'ABCDEFGHIJ'.
       01 WS-B PIC X(2)  VALUE SPACES.
""",
"""           MOVE WS-A(5:2) TO WS-B
           IF WS-B = 'EF'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"refmod_move_target": prog(
"""       01 WS-A PIC X(6) VALUE 'ABCDEF'.
""",
"""           MOVE 'ZZ' TO WS-A(3:2)
           IF WS-A = 'ABZZEF'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"initialize": prog(
"""       01 WS-G.
          05 WS-N PIC 9(3) VALUE 123.
          05 WS-C PIC X(3) VALUE 'XYZ'.
""",
"""           INITIALIZE WS-G
           IF WS-N = 0 AND WS-C = SPACES
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"compute": prog(
"""       01 WS-A PIC S9(5) VALUE 10.
       01 WS-B PIC S9(5) VALUE 3.
       01 WS-R PIC S9(5) VALUE 0.
""",
"""           COMPUTE WS-R = WS-A * WS-B + 2
           IF WS-R = 32
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_trim": prog(
"""       01 WS-A PIC X(10) VALUE 'AB        '.
""",
"""           IF FUNCTION TRIM(WS-A) = 'AB'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_length": prog(
"""       01 WS-A PIC X(7) VALUE 'ABCDEFG'.
""",
"""           IF FUNCTION LENGTH(WS-A) = 7
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_upper": prog(
"""       01 WS-A PIC X(3) VALUE 'abc'.
""",
"""           IF FUNCTION UPPER-CASE(WS-A) = 'ABC'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_numval": prog(
"""       01 WS-A PIC X(5) VALUE '00123'.
""",
"""           IF FUNCTION NUMVAL(WS-A) = 123
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"level88_thru": prog(
"""       01 WS-C PIC 9(2) VALUE 5.
          88 IN-RANGE VALUE 1 THRU 9.
""",
"""           IF IN-RANGE
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"level88_thru_outside": prog(
"""       01 WS-C PIC 9(2) VALUE 20.
          88 IN-RANGE VALUE 1 THRU 9.
""",
"""           IF IN-RANGE
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"when_thru": prog(
"""       01 WS-C PIC 9(2) VALUE 5.
""",
"""           EVALUATE WS-C
             WHEN 1 THRU 9
               PERFORM YES-P
             WHEN OTHER
               PERFORM NO-P
           END-EVALUATE
           GOBACK.
"""),

# `(A OR B) AND C` is two ways to be true, not one. Read as `A AND C` the
# second disjunct is unreachable, and every arm guarded that way is scored on
# the wrong side - which is a whole paragraph of COACTUPC.
"or_inside_and": prog(
"""       01 WS-A PIC X VALUE 'N'.
       01 WS-B PIC X VALUE 'Y'.
       01 WS-C PIC X VALUE 'Y'.
""",
"""           IF (WS-A = 'Y' OR WS-B = 'Y') AND WS-C = 'Y'
               PERFORM YES-P
           ELSE
               PERFORM NO-P
           END-IF
           GOBACK.
"""),

"and_inside_or": prog(
"""       01 WS-A PIC X VALUE 'N'.
       01 WS-B PIC X VALUE 'Y'.
       01 WS-C PIC X VALUE 'N'.
""",
"""           IF WS-A = 'Y' OR (WS-B = 'Y' AND WS-C = 'Y')
               PERFORM YES-P
           ELSE
               PERFORM NO-P
           END-IF
           GOBACK.
"""),

"length_of_in_refmod": prog(
"""       01 WS-SRC PIC X(8) VALUE 'ABCDEFGH'.
       01 WS-KEY PIC X(4) VALUE 'ABCD'.
       01 WS-OUT PIC X(4).
""",
"""           MOVE WS-SRC(LENGTH OF WS-KEY + 1:4) TO WS-OUT
           IF WS-OUT = 'EFGH'
               PERFORM YES-P
           ELSE
               PERFORM NO-P
           END-IF
           GOBACK.
"""),

"when_relational": prog(
"""       01 WS-C PIC 9(2) VALUE 15.
""",
"""           EVALUATE WS-C
             WHEN > 10
               PERFORM YES-P
             WHEN OTHER
               PERFORM NO-P
           END-EVALUATE
           GOBACK.
"""),

"perform_varying_after": prog(
"""       01 I PIC 9(2) VALUE 0.
       01 J PIC 9(2) VALUE 0.
       01 N PIC 9(3) VALUE 0.
""",
"""           PERFORM VARYING I FROM 1 BY 1 UNTIL I > 3
             AFTER J FROM 1 BY 1 UNTIL J > 4
               ADD 1 TO N
           END-PERFORM
           IF N = 12
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"string_verb": prog(
"""       01 WS-A PIC X(3) VALUE 'ABC'.
       01 WS-B PIC X(3) VALUE 'DEF'.
       01 WS-R PIC X(6) VALUE SPACES.
""",
"""           STRING WS-A DELIMITED BY SIZE
                  WS-B DELIMITED BY SIZE
             INTO WS-R
           END-STRING
           IF WS-R = 'ABCDEF'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_tallying": prog(
"""       01 WS-A PIC X(6) VALUE 'AABAAB'.
       01 WS-N PIC 9(2) VALUE 0.
""",
"""           INSPECT WS-A TALLYING WS-N FOR ALL 'A'
           IF WS-N = 4
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"alnum_pad_compare": prog(
"""       01 WS-A PIC X(5) VALUE 'AB'.
""",
"""           IF WS-A = 'AB'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"group_read_after_child_write": prog(
"""       01 WS-G.
          05 WS-1 PIC X(2) VALUE SPACES.
          05 WS-2 PIC X(2) VALUE SPACES.
""",
"""           MOVE 'AB' TO WS-1
           IF WS-G = 'AB  '
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"numeric_move_truncation": prog(
"""       01 WS-S PIC 9(5) VALUE 12345.
       01 WS-T PIC 9(2) VALUE 0.
""",
"""           MOVE WS-S TO WS-T
           IF WS-T = 45
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"alnum_move_truncation": prog(
"""       01 WS-S PIC X(5) VALUE 'ABCDE'.
       01 WS-T PIC X(2) VALUE SPACES.
""",
"""           MOVE WS-S TO WS-T
           IF WS-T = 'AB'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"abbrev_and_relation": prog(
"""       01 WS-C PIC 9(2) VALUE 7.
""",
"""           IF WS-C > 5 AND < 10
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"abbrev_and_relation_false": prog(
"""       01 WS-C PIC 9(2) VALUE 20.
""",
"""           IF WS-C > 5 AND < 10
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"abbrev_or_subject_only": prog(
"""       01 WS-C PIC X(2) VALUE '04'.
""",
"""           IF WS-C = '00' OR '04'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"set_88_multi": prog(
"""       01 WS-F PIC X VALUE 'N'.
          88 F-ON VALUE 'Y' 'y'.
""",
"""           SET F-ON TO TRUE
           IF WS-F = 'Y'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"add_to_multiple": prog(
"""       01 A PIC 9(3) VALUE 1.
       01 B PIC 9(3) VALUE 2.
""",
"""           ADD 1 TO A B
           IF A = 2 AND B = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"multiply_giving": prog(
"""       01 A PIC 9(3) VALUE 4.
       01 R PIC 9(3) VALUE 0.
""",
"""           MULTIPLY A BY 3 GIVING R
           IF R = 12
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"divide_into": prog(
"""       01 A PIC 9(3) VALUE 12.
       01 R PIC 9(3) VALUE 0.
""",
"""           DIVIDE A BY 4 GIVING R
           IF R = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"subtract_from_multi": prog(
"""       01 A PIC S9(3) VALUE 10.
""",
"""           SUBTRACT 3 FROM A
           IF A = 7
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"move_spaces_numeric_cmp": prog(
"""       01 WS-N PIC 9(3) VALUE 0.
""",
"""           IF WS-N = ZERO
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"nested_if_period": prog(
"""       01 A PIC 9 VALUE 1.
       01 B PIC 9 VALUE 0.
""",
"""           IF A = 1
              IF B = 1
                 PERFORM NO-P
              ELSE
                 PERFORM YES-P
              END-IF
           END-IF
           GOBACK.
"""),

"perform_thru": prog(
"""       01 A PIC 9 VALUE 0.
""",
"""           PERFORM P1 THRU P3
           IF A = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GO TO DONE-P.
       P1.
           ADD 1 TO A.
       P2.
           ADD 1 TO A.
       P3.
           ADD 1 TO A.
"""),

"redefines_alias": prog(
"""       01 WS-A PIC X(4) VALUE '1234'.
       01 WS-B REDEFINES WS-A PIC 9(4).
""",
"""           IF WS-B = 1234
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"occurs_index": prog(
"""       01 WS-T.
          05 WS-E PIC 9(2) OCCURS 3 TIMES.
       01 I PIC 9 VALUE 2.
""",
"""           MOVE 11 TO WS-E(1)
           MOVE 22 TO WS-E(2)
           IF WS-E(1) = 11
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"signed_compare": prog(
"""       01 A PIC S9(3) VALUE -5.
""",
"""           IF A < 0
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"class_numeric_spaces": prog(
"""       01 A PIC X(3) VALUE '   '.
""",
"""           IF A IS NUMERIC
              PERFORM NO-P
           ELSE
              PERFORM YES-P
           END-IF
           GOBACK.
"""),

"if_not_paren_or": prog(
"""       01 A PIC 9 VALUE 3.
""",
"""           IF NOT (A = 1 OR A = 2)
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"continue_stmt": prog(
"""       01 A PIC 9 VALUE 1.
""",
"""           IF A = 1
              CONTINUE
           ELSE
              PERFORM NO-P
           END-IF
           PERFORM YES-P
           GOBACK.
"""),

"go_to_depending": prog(
"""       01 K PIC 9 VALUE 2.
""",
"""           GO TO L1 L2 L3 DEPENDING ON K.
       L1.
           PERFORM NO-P
           GO TO DONE-P.
       L2.
           PERFORM YES-P
           GO TO DONE-P.
       L3.
           PERFORM NO-P
           GO TO DONE-P.
"""),

"search_all": prog(
"""       01 WS-T.
          05 WS-E OCCURS 3 TIMES ASCENDING KEY IS WS-K
             INDEXED BY IX.
             10 WS-K PIC 9(2).
             10 WS-V PIC X(3).
       01 I PIC 9 VALUE 0.
""",
"""           MOVE 01 TO WS-K(1)
           MOVE 05 TO WS-K(2)
           MOVE 09 TO WS-K(3)
           SEARCH ALL WS-E
              AT END PERFORM NO-P
              WHEN WS-K(IX) = 05
                 PERFORM YES-P
           END-SEARCH
           GOBACK.
"""),

"exit_paragraph": prog(
"""       01 A PIC 9 VALUE 1.
""",
"""           PERFORM SUBP
           IF A = 1
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GO TO DONE-P.
       SUBP.
           IF A = 1
              EXIT PARAGRAPH
           END-IF
           MOVE 9 TO A.
"""),

"perform_until_after": prog(
"""       01 A PIC 9(2) VALUE 9.
       01 N PIC 9(2) VALUE 0.
""",
"""           PERFORM WITH TEST AFTER UNTIL A > 5
              ADD 1 TO N
           END-PERFORM
           IF N = 1
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"move_zeroes_group": prog(
"""       01 WS-G.
          05 WS-N PIC 9(3) VALUE 999.
""",
"""           MOVE ZEROS TO WS-G
           IF WS-N = 0
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"eval_also": prog(
"""       01 A PIC 9 VALUE 1.
       01 B PIC 9 VALUE 2.
""",
"""           EVALUATE A ALSO B
             WHEN 1 ALSO 2
               PERFORM YES-P
             WHEN OTHER
               PERFORM NO-P
           END-EVALUATE
           GOBACK.
"""),

"eval_true_when": prog(
"""       01 A PIC 9 VALUE 4.
""",
"""           EVALUATE TRUE
             WHEN A > 3
               PERFORM YES-P
             WHEN OTHER
               PERFORM NO-P
           END-EVALUATE
           GOBACK.
"""),

"if_arith_expr": prog(
"""       01 A PIC 9(3) VALUE 5.
       01 B PIC 9(3) VALUE 6.
""",
"""           IF A + B > 10
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),
}


def main():
    only = sys.argv[1:] or sorted(CASES)
    work = tempfile.mkdtemp(prefix="fl-micro-")
    bad = []
    for name in only:
        src = os.path.join(work, "%s.cbl" % name)
        with open(src, "w") as fh:
            fh.write(CASES[name])
        r = compare(src)
        if "real_len" not in r:
            print("%-28s SKIP  %s" % (name, r["note"][:80]))
            continue
        if r["identical"]:
            print("%-28s ok" % name)
        else:
            d = r["first_divergence"]
            print("%-28s DIVERGES at %d: cobc=%s tool=%s" % (name, d["at"], d["real"], d["mine"]))
            print("%-28s   cobc: %s" % ("", r.get("_real", "")))
            bad.append(name)
    print("\n%d/%d fixtures diverge" % (len(bad), len(only)))
    print("diverging:", ", ".join(bad))


if __name__ == "__main__":
    main()
