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


def io_prog(select, fd, ws, body):
    return ("""\
       IDENTIFICATION DIVISION.
       PROGRAM-ID. T.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
""" + select + """\
       DATA DIVISION.
       FILE SECTION.
""" + fd + """\
       WORKING-STORAGE SECTION.
""" + ws + "       PROCEDURE DIVISION.\n       MAIN.\n" + body + TAIL)


SEQ_SELECT = """\
           SELECT FA ASSIGN TO FA
               ORGANIZATION IS LINE SEQUENTIAL
               FILE STATUS IS WS-ST.
"""
SEQ_FD = """\
       FD FA.
       01 FA-REC PIC X(10).
"""
IDX_SELECT = """\
           SELECT FB ASSIGN TO FB
               ORGANIZATION IS INDEXED
               ACCESS MODE IS DYNAMIC
               RECORD KEY IS FB-KEY
               FILE STATUS IS WS-ST.
"""
IDX_FD = """\
       FD FB.
       01 FB-REC.
          05 FB-KEY PIC X(4).
          05 FB-DAT PIC X(6).
"""


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

# The rest of INSPECT. TALLYING is only one of three formats and `ALL` only
# one of three arguments; a program that counts blanks with CHARACTERS, strips
# a prefix with LEADING or blanks a field with CONVERTING is doing something a
# later condition turns on, and each of those is a separate way to get it
# wrong. BEFORE/AFTER INITIAL is where the standard is least obvious: the
# region is *empty* when an AFTER delimiter is absent, rather than the whole
# item.
"inspect_tallying_leading": prog(
"""       01 WS-A PIC X(6) VALUE 'AABAAB'.
       01 WS-N PIC 9(2) VALUE 0.
""",
"""           INSPECT WS-A TALLYING WS-N FOR LEADING 'A'
           IF WS-N = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_tallying_characters": prog(
"""       01 WS-A PIC X(6) VALUE 'AB    '.
       01 WS-N PIC 9(2) VALUE 0.
""",
"""           INSPECT WS-A TALLYING WS-N FOR CHARACTERS
           IF WS-N = 6
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_tallying_after": prog(
"""       01 WS-A PIC X(7) VALUE 'AA/AAAB'.
       01 WS-N PIC 9(2) VALUE 0.
""",
"""           INSPECT WS-A TALLYING WS-N FOR ALL 'A' AFTER INITIAL '/'
           IF WS-N = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_tallying_before": prog(
"""       01 WS-A PIC X(7) VALUE 'AA/AAAB'.
       01 WS-N PIC 9(2) VALUE 0.
""",
"""           INSPECT WS-A TALLYING WS-N FOR ALL 'A' BEFORE INITIAL '/'
           IF WS-N = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# The counter is not initialised by INSPECT: two statements accumulate.
"inspect_tallying_accumulates": prog(
"""       01 WS-A PIC X(4) VALUE 'ABAB'.
       01 WS-N PIC 9(2) VALUE 0.
""",
"""           INSPECT WS-A TALLYING WS-N FOR ALL 'A'
           INSPECT WS-A TALLYING WS-N FOR ALL 'B'
           IF WS-N = 4
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# Overlapping arguments are consumed, not re-examined: 'AA' occurs once in
# 'AAA', because the scan resumes past what it matched.
"inspect_tallying_overlap": prog(
"""       01 WS-A PIC X(3) VALUE 'AAA'.
       01 WS-N PIC 9(2) VALUE 0.
""",
"""           INSPECT WS-A TALLYING WS-N FOR ALL 'AA'
           IF WS-N = 1
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_replacing_all": prog(
"""       01 WS-A PIC X(6) VALUE 'AABAAB'.
""",
"""           INSPECT WS-A REPLACING ALL 'A' BY 'X'
           IF WS-A = 'XXBXXB'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_replacing_leading": prog(
"""       01 WS-A PIC X(6) VALUE '00A00B'.
""",
"""           INSPECT WS-A REPLACING LEADING '0' BY ' '
           IF WS-A = '  A00B'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_replacing_first": prog(
"""       01 WS-A PIC X(6) VALUE 'ABABAB'.
""",
"""           INSPECT WS-A REPLACING FIRST 'B' BY 'Z'
           IF WS-A = 'AZABAB'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_replacing_characters_after": prog(
"""       01 WS-A PIC X(6) VALUE 'AB/CDE'.
""",
"""           INSPECT WS-A REPLACING CHARACTERS BY '*' AFTER INITIAL '/'
           IF WS-A = 'AB/***'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"inspect_converting": prog(
"""       01 WS-A PIC X(5) VALUE 'abcde'.
""",
"""           INSPECT WS-A CONVERTING 'abc' TO 'ABC'
           IF WS-A = 'ABCde'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A numeric item is scanned as its bytes, zero-filled on the left. Reading it
# as the decimal text of its value counts a different number of zeros.
"inspect_numeric_subject": prog(
"""       01 WS-N PIC 9(5) VALUE 102.
       01 WS-C PIC 9(2) VALUE 0.
""",
"""           INSPECT WS-N TALLYING WS-C FOR ALL '0'
           IF WS-C = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A statement inside a conditional handler must not run on past the phrase
# that ends the handler. `PERFORM NO-P NOT ON SIZE ERROR` is one PERFORM and
# one phrase; read as a PERFORM of five words the second phrase disappears and
# everything it guarded moves into the first arm, so both handlers fire on the
# same outcome. Every `READ ... AT END ... NOT AT END ...` has this shape.
"two_phrases_after_a_statement": prog(
"""       01 A PIC 9(3) VALUE 1.
""",
"""           ADD 1 TO A
              ON SIZE ERROR PERFORM NO-P
              NOT ON SIZE ERROR PERFORM YES-P
           END-ADD
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

# SEARCH has one site in these corpora and will measure at zero on them. The
# fixtures are the point: they measure the language rather than the sample,
# and an estate that uses table lookups uses this verb heavily. Each of these
# isolates one rule - where the scan starts, that it advances, that AT END is
# the arm taken when nothing matched, that VARYING steps with the index, that
# arms are tried in order - so a failure names which rule is wrong.
"search_serial_advances": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 4 TIMES INDEXED BY IX.
""",
"""           SET IX TO 1
           SEARCH WS-E
              AT END PERFORM NO-P
              WHEN IX = 3
                 PERFORM YES-P
           END-SEARCH
           GOBACK.
"""),

# The scan starts where the index is, not at one. A program that has already
# consumed the first two entries resumes; restarting would loop for ever.
"search_serial_resumes": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 4 TIMES INDEXED BY IX.
""",
"""           SET IX TO 3
           SEARCH WS-E
              AT END PERFORM NO-P
              WHEN IX = 2
                 PERFORM NO-P
              WHEN IX = 4
                 PERFORM YES-P
           END-SEARCH
           GOBACK.
"""),

"search_serial_at_end": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 3 TIMES INDEXED BY IX.
""",
"""           SET IX TO 1
           SEARCH WS-E
              AT END PERFORM YES-P
              WHEN IX = 9
                 PERFORM NO-P
           END-SEARCH
           GOBACK.
"""),

# Arms are compared in the order written and the first match wins.
"search_serial_arm_order": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 4 TIMES INDEXED BY IX.
""",
"""           SET IX TO 1
           SEARCH WS-E
              AT END PERFORM NO-P
              WHEN IX = 2
                 PERFORM YES-P
              WHEN IX = 2
                 PERFORM NO-P
           END-SEARCH
           GOBACK.
"""),

# AT END is optional. Without it a search that matches nothing simply falls
# through to the next statement.
"search_no_at_end": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 3 TIMES INDEXED BY IX.
""",
"""           SET IX TO 1
           SEARCH WS-E
              WHEN IX = 9
                 PERFORM NO-P
           END-SEARCH
           PERFORM YES-P
           GOBACK.
"""),

"search_varying": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 4 TIMES INDEXED BY IX.
       01 J PIC 9(2) VALUE 0.
""",
"""           SET IX TO 1
           SEARCH WS-E VARYING J
              AT END PERFORM NO-P
              WHEN IX = 3
                 CONTINUE
           END-SEARCH
           IF J = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# After a search that found nothing the index sits one past the table, which
# is what a program testing it afterwards relies on.
"search_index_after_at_end": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 3 TIMES INDEXED BY IX.
       01 J PIC 9(2) VALUE 0.
""",
"""           SET IX TO 1
           SEARCH WS-E VARYING J
              AT END CONTINUE
              WHEN IX = 9
                 CONTINUE
           END-SEARCH
           IF J = 4
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
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

# --- storage: a name is a window onto bytes -------------------------------
# These ask what a record *contains*, which a {name: value} store cannot
# answer: two names over one area, a USAGE that is not characters, and a
# subscript that has to pick a different set of bytes each time.

# S9(4) COMP is two bytes of big-endian two's complement. Read as a decimal
# cell it is indistinguishable from DISPLAY, and a migration that ports it as
# an int diverges exactly where the record is written out.
"usage_comp_bytes": prog(
"""       01 WS-B PIC S9(4) COMP VALUE 0.
       01 WS-X REDEFINES WS-B PIC X(2).
""",
"""           MOVE 258 TO WS-B
           IF FUNCTION ORD(WS-X(1:1)) = 2
              AND FUNCTION ORD(WS-X(2:1)) = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# S9(4) COMP holds two bytes, so a value needing five digits comes back
# truncated to the declared four. The width is a fact about the layout.
"usage_comp_truncation": prog(
"""       01 WS-B PIC S9(4) COMP VALUE 0.
""",
"""           MOVE 123456 TO WS-B
           IF WS-B = 3456
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# COMP-3 is two digits to a byte with a sign nibble at the end: 12345 is
# X'12345C' and -12345 is X'12345D'. Nothing about that is derivable from
# the PIC clause alone.
"usage_comp3_bytes": prog(
"""       01 WS-P PIC S9(5) COMP-3 VALUE 0.
       01 WS-X REDEFINES WS-P PIC X(3).
""",
"""           MOVE 12345 TO WS-P
           IF FUNCTION ORD(WS-X(1:1)) = 19
              AND FUNCTION ORD(WS-X(3:1)) = 93
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"usage_comp3_negative": prog(
"""       01 WS-P PIC S9(5) COMP-3 VALUE 0.
       01 WS-X REDEFINES WS-P PIC X(3).
""",
"""           MOVE -12345 TO WS-P
           IF FUNCTION ORD(WS-X(3:1)) = 94 AND WS-P = -12345
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A DISPLAY sign is overpunched onto the last digit rather than costing a
# byte, so a signed and an unsigned field of the same PIC are the same width
# and different bytes.
"display_sign_overpunch": prog(
"""       01 WS-N PIC S9(3) VALUE 0.
       01 WS-X REDEFINES WS-N PIC X(3).
""",
"""           MOVE -123 TO WS-N
           IF WS-X(1:2) = '12' AND FUNCTION ORD(WS-X(3:1)) = 116
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A packed field ahead of a character field decides where the character
# field starts. Three bytes, not five.
"comp3_shifts_offsets": prog(
"""       01 WS-G.
          05 WS-P PIC 9(5) COMP-3 VALUE 0.
          05 WS-T PIC X(4) VALUE SPACES.
       01 WS-R REDEFINES WS-G PIC X(7).
""",
"""           MOVE 'XXXYYYY' TO WS-R
           IF WS-T = 'YYYY'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A REDEFINES that is a different shape, not merely a different PIC of the
# same width. This is the ordinary way a date is held as text and read as
# parts, and value aliasing cannot express it.
"redefines_partial_overlay": prog(
"""       01 WS-DATE PIC X(8) VALUE '20240115'.
       01 WS-PARTS REDEFINES WS-DATE.
          05 WS-YY PIC X(4).
          05 WS-MM PIC X(2).
          05 WS-DD PIC X(2).
""",
"""           IF WS-MM = '01' AND WS-DD = '15'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# The same overlay written through the other name at run time.
"redefines_partial_write": prog(
"""       01 WS-A PIC X(6) VALUE SPACES.
       01 WS-B REDEFINES WS-A.
          05 WS-B1 PIC X(3).
          05 WS-B2 PIC X(3).
""",
"""           MOVE 'ABCDEF' TO WS-A
           IF WS-B2 = 'DEF' AND WS-B1 = 'ABC'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# Writing the narrow name changes only its own bytes of the wide one.
"redefines_write_back": prog(
"""       01 WS-A PIC X(6) VALUE 'ABCDEF'.
       01 WS-B REDEFINES WS-A.
          05 WS-B1 PIC X(3).
          05 WS-B2 PIC X(3).
""",
"""           MOVE 'ZZZ' TO WS-B2
           IF WS-A = 'ABCZZZ'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A table filled through a loop and read back at two subscripts. One cell per
# name answers this with whatever was written last.
"occurs_varying_fill": prog(
"""       01 WS-T.
          05 WS-E PIC 9(2) OCCURS 5 TIMES.
       01 I PIC 9(2) VALUE 0.
       01 N PIC 9(3) VALUE 0.
""",
"""           PERFORM VARYING I FROM 1 BY 1 UNTIL I > 5
              MOVE I TO WS-E(I)
           END-PERFORM
           COMPUTE N = WS-E(1) + WS-E(5)
           IF N = 6
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"occurs_add_subscript": prog(
"""       01 WS-T.
          05 WS-E PIC 9(3) OCCURS 3 TIMES.
       01 I PIC 9 VALUE 2.
""",
"""           MOVE 0 TO WS-E(1)
           MOVE 0 TO WS-E(2)
           MOVE 0 TO WS-E(3)
           ADD 5 TO WS-E(I)
           IF WS-E(2) = 5 AND WS-E(1) = 0
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"occurs_two_dimensions": prog(
"""       01 WS-T.
          05 WS-ROW OCCURS 2 TIMES.
             10 WS-CELL PIC 9(2) OCCURS 3 TIMES.
""",
"""           MOVE 11 TO WS-CELL(1 1)
           MOVE 23 TO WS-CELL(2 3)
           IF WS-CELL(1 1) = 11 AND WS-CELL(2 3) = 23
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A table sits inside the group's bytes, so the group sees every element.
"occurs_group_read": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 3 TIMES.
""",
"""           MOVE 'AB' TO WS-E(1)
           MOVE 'CD' TO WS-E(2)
           MOVE 'EF' TO WS-E(3)
           IF WS-T = 'ABCDEF'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# INITIALIZE reaches every occurrence, not the first one.
"initialize_table": prog(
"""       01 WS-T.
          05 WS-E PIC 9(2) OCCURS 3 TIMES.
""",
"""           MOVE 11 TO WS-E(1)
           MOVE 22 TO WS-E(2)
           MOVE 33 TO WS-E(3)
           INITIALIZE WS-T
           IF WS-E(3) = 0 AND WS-E(2) = 0
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A figurative constant is as wide as what receives it.
"move_all_literal": prog(
"""       01 WS-A PIC X(5) VALUE SPACES.
""",
"""           MOVE ALL 'Z' TO WS-A
           IF WS-A = 'ZZZZZ'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"move_zeros_alnum": prog(
"""       01 WS-A PIC X(3) VALUE SPACES.
""",
"""           MOVE ZEROS TO WS-A
           IF WS-A = '000'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A group MOVE is a byte copy, so each child takes the piece that lands on
# it - including a numeric child that ends up holding characters.
"group_move_splits_bytes": prog(
"""       01 WS-G.
          05 WS-1 PIC X(3) VALUE SPACES.
          05 WS-2 PIC 9(2) VALUE 0.
       01 WS-S PIC X(5) VALUE 'ABC49'.
""",
"""           MOVE WS-S TO WS-G
           IF WS-1 = 'ABC' AND WS-2 = 49
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A figurative constant is as wide as the item it meets, and LOW-VALUE is a
# byte rather than whitespace - so a field full of them is equal to the
# constant and not equal to SPACES. Both directions matter: the first is how
# an uninitialised CICS field is tested, the second is how it is told apart
# from a blank one.
"low_values_compare": prog(
"""       01 WS-A PIC X(3) VALUE LOW-VALUES.
""",
"""           IF WS-A = LOW-VALUES
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"low_values_not_spaces": prog(
"""       01 WS-A PIC X(3) VALUE LOW-VALUES.
""",
"""           IF WS-A = SPACES
              PERFORM NO-P
           ELSE
              PERFORM YES-P
           END-IF
           GOBACK.
"""),

"move_low_values": prog(
"""       01 WS-A PIC X(3) VALUE 'ABC'.
""",
"""           MOVE LOW-VALUES TO WS-A
           IF WS-A = LOW-VALUES
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# Clearing a record through the name that redefines it clears the record.
# This is the whole of what a screen program does before it sends a map, and
# a store that keeps the two descriptions as separate values says the first
# one still holds its old contents - so every field the screen would supply
# looks like it survived, and conditions on it are scored on data the
# program had already thrown away.
"redefines_cleared_through_alias": prog(
"""       01 WS-IN.
          05 WS-F1 PIC X(3) VALUE 'ABC'.
          05 WS-F2 PIC X(3) VALUE 'DEF'.
       01 WS-OUT REDEFINES WS-IN.
          05 WS-G1 PIC X(3).
          05 WS-G2 PIC X(3).
""",
"""           MOVE LOW-VALUES TO WS-OUT
           IF WS-F1 = LOW-VALUES AND WS-F2 = LOW-VALUES
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
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

# --------------------------------------------------------------------------
# Beyond the first pass. The set above reached 0/89 diverging, which is not a
# result - it is an instrument that has stopped discriminating. What follows
# is the COBOL those fixtures did not reach, written from the standard rather
# than from any program: the data description clauses that decide a field's
# bytes, the verbs that take a record apart, the loop and table forms, the
# comparison rules, and the file-status vocabulary. Several of these are
# constructs neither corpus uses, which is the point - a fixture set that
# only tests what the sample happens to contain measures the sample.
# --------------------------------------------------------------------------

# ---- data description ---------------------------------------------------

# `OCCURS 1 TO 5 DEPENDING ON N` reserves five entries and the counter says
# how many are current. Read as one entry, every reference past the first is
# out of range and everything laid out after the table is at the wrong offset.
"occurs_depending_on": prog(
"""       01 WS-N PIC 9(2) VALUE 3.
       01 WS-T.
          05 WS-E PIC X(2) OCCURS 1 TO 5 TIMES DEPENDING ON WS-N.
""",
"""           MOVE 'AB' TO WS-E(1)
           MOVE 'CD' TO WS-E(2)
           MOVE 'EF' TO WS-E(3)
           IF WS-T(1:6) = 'ABCDEF'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# The *current* length of a group containing an ODO table follows the
# counter, so LENGTH OF it changes as the program sets N. Still open:
# the layout reserves the maximum, which is right for offsets and wrong
# for this.
"odo_length_follows_counter": prog(
"""       01 WS-N PIC 9(2) VALUE 3.
       01 WS-T.
          05 WS-E PIC X(2) OCCURS 1 TO 5 TIMES DEPENDING ON WS-N.
""",
"""           IF FUNCTION LENGTH(WS-T) = 6
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# SIGN IS SEPARATE spends a byte on the sign instead of overpunching the
# last digit, so the field is one byte wider than its digit count.
"sign_separate_trailing": prog(
"""       01 WS-N PIC S9(3) SIGN IS TRAILING SEPARATE VALUE 0.
       01 WS-X REDEFINES WS-N PIC X(4).
""",
"""           MOVE -123 TO WS-N
           IF WS-X = '123-'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"sign_separate_leading": prog(
"""       01 WS-N PIC S9(3) SIGN IS LEADING SEPARATE VALUE 0.
       01 WS-X REDEFINES WS-N PIC X(4).
""",
"""           MOVE -123 TO WS-N
           IF WS-X = '-123'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# BLANK WHEN ZERO makes a zero read as spaces rather than as '000', which
# is how a report field is told apart from an unset one.
"blank_when_zero": prog(
"""       01 WS-N PIC 9(3) BLANK WHEN ZERO VALUE 0.
""",
"""           MOVE 0 TO WS-N
           IF WS-N = SPACES
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"justified_right": prog(
"""       01 WS-A PIC X(5) JUSTIFIED RIGHT VALUE SPACES.
""",
"""           MOVE 'AB' TO WS-A
           IF WS-A = '   AB'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# SYNCHRONIZED aligns a binary field on its natural boundary, inserting
# slack bytes ahead of it - so the group is wider than the sum of its
# fields and everything after the slack sits later than it looks.
"synchronized_pads": prog(
"""       01 WS-G.
          05 WS-C PIC X.
          05 WS-B PIC S9(4) COMP SYNCHRONIZED.
""",
"""           IF FUNCTION LENGTH(WS-G) = 4
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A 66-level names a span of an existing group: one name over the bytes of
# several others, with no storage of its own.
"renames_66": prog(
"""       01 WS-G.
          05 WS-A PIC X(2) VALUE 'AB'.
          05 WS-B PIC X(2) VALUE 'CD'.
          05 WS-C PIC X(2) VALUE 'EF'.
       66 WS-AB RENAMES WS-A THRU WS-B.
""",
"""           IF WS-AB = 'ABCD'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"usage_index_saved": prog(
"""       01 WS-T.
          05 WS-E PIC 9(2) OCCURS 5 TIMES INDEXED BY IX.
       01 WS-SV USAGE INDEX.
""",
"""           MOVE 11 TO WS-E(1)
           MOVE 44 TO WS-E(4)
           SET IX TO 4
           SET WS-SV TO IX
           SET IX TO 1
           SET IX TO WS-SV
           IF WS-E(IX) = 44
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"set_index_up_by": prog(
"""       01 WS-T.
          05 WS-E PIC 9(2) OCCURS 5 TIMES INDEXED BY IX.
""",
"""           MOVE 11 TO WS-E(1)
           MOVE 44 TO WS-E(4)
           SET IX TO 2
           SET IX UP BY 2
           IF WS-E(IX) = 44
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"index_plus_literal_subscript": prog(
"""       01 WS-T.
          05 WS-E PIC 9(2) OCCURS 5 TIMES INDEXED BY IX.
""",
"""           MOVE 33 TO WS-E(3)
           SET IX TO 2
           IF WS-E(IX + 1) = 33
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"comp1_keeps_fraction": prog(
"""       01 WS-F USAGE COMP-1.
       01 WS-I PIC 9(5) VALUE 0.
""",
"""           COMPUTE WS-F = 1 / 4
           COMPUTE WS-I = WS-F * 100
           IF WS-I = 25
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"comp2_keeps_fraction": prog(
"""       01 WS-F USAGE COMP-2.
       01 WS-I PIC 9(5) VALUE 0.
""",
"""           COMPUTE WS-F = 7 / 2
           COMPUTE WS-I = WS-F * 100
           IF WS-I = 350
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A P in a picture is a digit position that is not stored: PIC 9(3)PP
# holds three bytes and means a value a hundred times larger.
"scaled_p_picture": prog(
"""       01 WS-N PIC 9(3)PP VALUE 0.
       01 WS-X REDEFINES WS-N PIC X(3).
""",
"""           MOVE 12300 TO WS-N
           IF WS-X = '123' AND WS-N = 12300
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# A VALUE on a group initialises its bytes, and the children read their
# own piece of it.
"value_on_group": prog(
"""       01 WS-G VALUE 'ABCDEF'.
          05 WS-1 PIC X(3).
          05 WS-2 PIC X(3).
""",
"""           IF WS-2 = 'DEF' AND WS-1 = 'ABC'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# Moving to an edited picture is a formatting operation: suppression,
# insertion characters and the sign are all part of the receiver's value,
# and a later comparison is against the formatted text.
"numeric_edited_move": prog(
"""       01 WS-N PIC 9(5) VALUE 01234.
       01 WS-E PIC ZZ,ZZ9.
""",
"""           MOVE WS-N TO WS-E
           IF WS-E = ' 1,234'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"numeric_edited_cr": prog(
"""       01 WS-N PIC S9(3) VALUE -12.
       01 WS-E PIC 9(3)CR.
""",
"""           MOVE WS-N TO WS-E
           IF WS-E = '012CR'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"decimal_alignment_move": prog(
"""       01 WS-A PIC 9(3)V99 VALUE 0.
       01 WS-B PIC 9(5) VALUE 12345.
""",
"""           MOVE WS-B TO WS-A
           IF WS-A = 345.00
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"level_77": prog(
"""       77 WS-A PIC 9(3) VALUE 5.
""",
"""           ADD 1 TO WS-A
           IF WS-A = 6
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# ---- moves and arithmetic ------------------------------------------------
# MOVE CORRESPONDING pairs children by name. It needs qualified names to
# be distinct first - see `qualified_same_name`, which is the reason this
# one cannot be made to pass by working on the verb.
"move_corresponding": prog(
"""       01 WS-G1.
          05 WS-A PIC 9(2) VALUE 11.
          05 WS-B PIC X(2) VALUE 'XY'.
          05 WS-C PIC 9(2) VALUE 33.
       01 WS-G2.
          05 WS-B PIC X(2) VALUE SPACES.
          05 WS-A PIC 9(2) VALUE 0.
""",
"""           MOVE CORRESPONDING WS-G1 TO WS-G2
           IF WS-A OF WS-G2 = 11 AND WS-B OF WS-G2 = 'XY'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"add_corresponding": prog(
"""       01 WS-G1.
          05 WS-A PIC 9(3) VALUE 5.
          05 WS-B PIC 9(3) VALUE 7.
       01 WS-G2.
          05 WS-A PIC 9(3) VALUE 1.
          05 WS-B PIC 9(3) VALUE 2.
""",
"""           ADD CORRESPONDING WS-G1 TO WS-G2
           IF WS-A OF WS-G2 = 6 AND WS-B OF WS-G2 = 9
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"compute_rounded": prog(
"""       01 WS-R PIC 9(3) VALUE 0.
""",
"""           COMPUTE WS-R ROUNDED = 10 / 4
           IF WS-R = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"compute_unrounded_truncates": prog(
"""       01 WS-R PIC 9(3) VALUE 0.
""",
"""           COMPUTE WS-R = 10 / 4
           IF WS-R = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"rounded_mode_truncation": prog(
"""       01 WS-R PIC 9(3) VALUE 0.
""",
"""           COMPUTE WS-R ROUNDED MODE IS TRUNCATION = 10 / 4
           IF WS-R = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"rounded_mode_nearest_even": prog(
"""       01 WS-R PIC 9(3) VALUE 0.
""",
"""           COMPUTE WS-R ROUNDED MODE IS NEAREST-EVEN = 10 / 4
           IF WS-R = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"divide_remainder": prog(
"""       01 WS-Q PIC 9(3) VALUE 0.
       01 WS-R PIC 9(3) VALUE 0.
""",
"""           DIVIDE 17 BY 5 GIVING WS-Q REMAINDER WS-R
           IF WS-Q = 3 AND WS-R = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"giving_multiple_receivers": prog(
"""       01 WS-A PIC 9(3) VALUE 4.
       01 WS-B PIC 9(3) VALUE 5.
       01 WS-R1 PIC 9(3) VALUE 0.
       01 WS-R2 PIC 9(3) VALUE 0.
""",
"""           ADD WS-A WS-B GIVING WS-R1 WS-R2
           IF WS-R1 = 9 AND WS-R2 = 9
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"compute_size_error": prog(
"""       01 WS-R PIC 9(2) VALUE 0.
""",
"""           COMPUTE WS-R = 99 * 99
              ON SIZE ERROR PERFORM YES-P
              NOT ON SIZE ERROR PERFORM NO-P
           END-COMPUTE
           GOBACK.
"""),

"divide_by_zero_size_error": prog(
"""       01 WS-R PIC 9(3) VALUE 0.
       01 WS-D PIC 9(3) VALUE 0.
""",
"""           DIVIDE 10 BY WS-D GIVING WS-R
              ON SIZE ERROR PERFORM YES-P
              NOT ON SIZE ERROR PERFORM NO-P
           END-DIVIDE
           GOBACK.
"""),

# COBOL evaluates an intermediate result at full precision; a product of
# two nine-digit values is eighteen digits and every one of them is
# significant. Binary floating point loses the low end of that.
"intermediate_result_width": prog(
"""       01 WS-A PIC 9(9) VALUE 999999999.
       01 WS-B PIC 9(9) VALUE 999999999.
       01 WS-R PIC 9(18) VALUE 0.
""",
"""           COMPUTE WS-R = WS-A * WS-B
           IF WS-R = 999999998000000001
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"move_signed_to_unsigned": prog(
"""       01 WS-S PIC S9(3) VALUE -5.
       01 WS-U PIC 9(3) VALUE 0.
""",
"""           MOVE WS-S TO WS-U
           IF WS-U = 5
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# UNSTRING is how a delimited record, a screen field or a commarea is
# taken apart, and each receiver may carry its own COUNT IN and
# DELIMITER IN. The fields it produces are exactly the ones later
# conditions turn on.
"unstring_count_tallying": prog(
"""       01 WS-S PIC X(11) VALUE 'AB,CDE,FGHI'.
       01 WS-P1 PIC X(4) VALUE SPACES.
       01 WS-P2 PIC X(4) VALUE SPACES.
       01 WS-C1 PIC 9(2) VALUE 0.
       01 WS-N PIC 9(2) VALUE 0.
""",
"""           UNSTRING WS-S DELIMITED BY ','
              INTO WS-P1 COUNT IN WS-C1
                   WS-P2
              TALLYING IN WS-N
           END-UNSTRING
           IF WS-P1 = 'AB' AND WS-P2 = 'CDE' AND WS-C1 = 2 AND WS-N = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"unstring_delimiter_in": prog(
"""       01 WS-S PIC X(7) VALUE 'AB;CDEF'.
       01 WS-P1 PIC X(4) VALUE SPACES.
       01 WS-D1 PIC X VALUE SPACE.
""",
"""           UNSTRING WS-S DELIMITED BY ',' OR ';'
              INTO WS-P1 DELIMITER IN WS-D1
           END-UNSTRING
           IF WS-P1 = 'AB' AND WS-D1 = ';'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"unstring_pointer_overflow": prog(
"""       01 WS-S PIC X(5) VALUE 'AB,CD'.
       01 WS-P1 PIC X(4) VALUE SPACES.
       01 WS-PT PIC 9(2) VALUE 9.
""",
"""           UNSTRING WS-S DELIMITED BY ',' INTO WS-P1
              WITH POINTER WS-PT
              ON OVERFLOW PERFORM YES-P
              NOT ON OVERFLOW PERFORM NO-P
           END-UNSTRING
           GOBACK.
"""),

# WITH POINTER says where in the receiver to start and is left one past
# the last character stored, which is how a line is assembled in pieces.
"string_pointer": prog(
"""       01 WS-R PIC X(10) VALUE ALL '-'.
       01 WS-PT PIC 9(2) VALUE 3.
""",
"""           STRING 'AB' DELIMITED BY SIZE INTO WS-R
              WITH POINTER WS-PT
           END-STRING
           IF WS-R = '--AB------' AND WS-PT = 5
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"string_overflow": prog(
"""       01 WS-R PIC X(3) VALUE SPACES.
""",
"""           STRING 'ABCDE' DELIMITED BY SIZE INTO WS-R
              ON OVERFLOW PERFORM YES-P
              NOT ON OVERFLOW PERFORM NO-P
           END-STRING
           GOBACK.
"""),

"string_delimited_by_space": prog(
"""       01 WS-A PIC X(5) VALUE 'AB   '.
       01 WS-R PIC X(6) VALUE SPACES.
""",
"""           STRING WS-A DELIMITED BY SPACE
                  'CD' DELIMITED BY SIZE
              INTO WS-R
           END-STRING
           IF WS-R = 'ABCD  '
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"refmod_computed_length": prog(
"""       01 WS-A PIC X(10) VALUE 'ABCDEFGHIJ'.
       01 WS-S PIC 9(2) VALUE 2.
       01 WS-L PIC 9(2) VALUE 3.
       01 WS-R PIC X(3) VALUE SPACES.
""",
"""           MOVE WS-A(WS-S:WS-L) TO WS-R
           IF WS-R = 'BCD'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"refmod_open_length": prog(
"""       01 WS-A PIC X(6) VALUE 'ABCDEF'.
       01 WS-R PIC X(3) VALUE SPACES.
""",
"""           MOVE WS-A(4:) TO WS-R
           IF WS-R = 'DEF'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),


"compute_frac_truncates": prog(
"""       01 WS-R PIC 9(3)V9 VALUE 0.
""",
"""           COMPUTE WS-R = 1 / 3
           IF WS-R = 0.3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# ---- control flow --------------------------------------------------------
# `EXIT PERFORM` leaves the inline loop; its second word is also a verb,
# which is what makes it easy to split into two statements by accident.
"exit_perform": prog(
"""       01 I PIC 9(2) VALUE 0.
       01 N PIC 9(2) VALUE 0.
""",
"""           PERFORM VARYING I FROM 1 BY 1 UNTIL I > 10
              IF I = 3
                 EXIT PERFORM
              END-IF
              ADD 1 TO N
           END-PERFORM
           IF N = 2 AND I = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"exit_perform_cycle": prog(
"""       01 I PIC 9(2) VALUE 0.
       01 N PIC 9(2) VALUE 0.
""",
"""           PERFORM VARYING I FROM 1 BY 1 UNTIL I > 5
              IF I = 3
                 EXIT PERFORM CYCLE
              END-IF
              ADD 1 TO N
           END-PERFORM
           IF N = 4
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"perform_varying_after_exit": prog(
"""       01 I PIC 9(2) VALUE 0.
       01 J PIC 9(2) VALUE 0.
       01 N PIC 9(3) VALUE 0.
""",
"""           PERFORM VARYING I FROM 1 BY 1 UNTIL I > 3
             AFTER J FROM 1 BY 1 UNTIL J > 4
               IF I = 2 AND J = 2
                  EXIT PERFORM
               END-IF
               ADD 1 TO N
           END-PERFORM
           IF N = 5
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# `PERFORM n TIMES` fixes the count on entry: a body that assigns to the
# same field does not shorten its own loop.
"perform_times_fixed_at_entry": prog(
"""       01 N PIC 9 VALUE 3.
       01 C PIC 9 VALUE 0.
""",
"""           PERFORM N TIMES
              ADD 1 TO C
              MOVE 1 TO N
           END-PERFORM
           IF C = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"perform_varying_body_writes": prog(
"""       01 I PIC 9(2) VALUE 0.
       01 N PIC 9(2) VALUE 0.
""",
"""           PERFORM VARYING I FROM 1 BY 1 UNTIL I > 6
              ADD 1 TO N
              ADD 1 TO I
           END-PERFORM
           IF N = 3
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# Out of range, GO TO ... DEPENDING ON falls through to the next
# statement rather than taking a branch.
"go_to_depending_out_of_range": prog(
"""       01 K PIC 9 VALUE 5.
""",
"""           GO TO L1 L2 DEPENDING ON K
           PERFORM YES-P
           GO TO DONE-P.
       L1.
           PERFORM NO-P
           GO TO DONE-P.
       L2.
           PERFORM NO-P
           GO TO DONE-P.
"""),

"go_to_depending_zero": prog(
"""       01 K PIC 9 VALUE 0.
""",
"""           GO TO L1 L2 DEPENDING ON K
           PERFORM YES-P
           GO TO DONE-P.
       L1.
           PERFORM NO-P
           GO TO DONE-P.
       L2.
           PERFORM NO-P
           GO TO DONE-P.
"""),

# ALSO pairs subjects with values by position, and ANY matches whatever
# its subject holds.
"eval_also_any": prog(
"""       01 A PIC 9 VALUE 1.
       01 B PIC 9 VALUE 7.
""",
"""           EVALUATE A ALSO B
             WHEN 1 ALSO ANY
               PERFORM YES-P
             WHEN OTHER
               PERFORM NO-P
           END-EVALUATE
           GOBACK.
"""),

"eval_also_thru": prog(
"""       01 A PIC 9 VALUE 1.
       01 B PIC 9(2) VALUE 7.
""",
"""           EVALUATE A ALSO B
             WHEN 1 ALSO 5 THRU 9
               PERFORM YES-P
             WHEN OTHER
               PERFORM NO-P
           END-EVALUATE
           GOBACK.
"""),

"eval_also_mismatch": prog(
"""       01 A PIC 9 VALUE 1.
       01 B PIC 9 VALUE 2.
""",
"""           EVALUATE A ALSO B
             WHEN 1 ALSO 3
               PERFORM NO-P
             WHEN 2 ALSO 2
               PERFORM NO-P
             WHEN OTHER
               PERFORM YES-P
           END-EVALUATE
           GOBACK.
"""),

"eval_stacked_whens": prog(
"""       01 A PIC 9 VALUE 2.
""",
"""           EVALUATE A
             WHEN 1
             WHEN 2
               PERFORM YES-P
             WHEN OTHER
               PERFORM NO-P
           END-EVALUATE
           GOBACK.
"""),

"eval_no_match_no_other": prog(
"""       01 A PIC 9 VALUE 8.
""",
"""           EVALUATE A
             WHEN 1
               PERFORM NO-P
           END-EVALUATE
           PERFORM YES-P
           GOBACK.
"""),

"eval_true_also_false": prog(
"""       01 A PIC 9 VALUE 4.
       01 B PIC 9 VALUE 1.
""",
"""           EVALUATE TRUE ALSO FALSE
             WHEN A > 3 ALSO B > 5
               PERFORM YES-P
             WHEN OTHER
               PERFORM NO-P
           END-EVALUATE
           GOBACK.
"""),

"eval_when_negated": prog(
"""       01 A PIC 9(2) VALUE 15.
""",
"""           EVALUATE A
             WHEN NOT 15
               PERFORM NO-P
             WHEN OTHER
               PERFORM YES-P
           END-EVALUATE
           GOBACK.
"""),

"perform_thru_backwards": prog(
"""       01 A PIC 9 VALUE 0.
""",
"""           PERFORM P2 THRU P3
           IF A = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GO TO DONE-P.
       P1.
           ADD 5 TO A.
       P2.
           ADD 1 TO A.
       P3.
           ADD 1 TO A.
"""),

"perform_nested_same_para": prog(
"""       01 A PIC 9 VALUE 0.
       01 B PIC 9 VALUE 0.
""",
"""           PERFORM P-OUT
           IF A = 2 AND B = 1
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GO TO DONE-P.
       P-OUT.
           PERFORM P-IN
           ADD 1 TO B
           PERFORM P-IN
           GO TO P-OUT-X.
       P-IN.
           ADD 1 TO A.
       P-OUT-X.
           EXIT.
"""),

"alter_go_to": prog(
"""       01 A PIC 9 VALUE 0.
""",
"""           ALTER SW TO PROCEED TO L2
           GO TO SW.
       SW.
           GO TO L1.
       L1.
           PERFORM NO-P
           GO TO DONE-P.
       L2.
           PERFORM YES-P
           GO TO DONE-P.
"""),

"perform_until_varying_from_var": prog(
"""       01 I PIC 9(2) VALUE 0.
       01 S PIC 9(2) VALUE 3.
       01 N PIC 9(2) VALUE 0.
""",
"""           PERFORM VARYING I FROM S BY 2 UNTIL I > 9
              ADD 1 TO N
           END-PERFORM
           IF N = 4
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# ---- tables --------------------------------------------------------------
"occurs_variable_subscript_2d": prog(
"""       01 WS-T.
          05 WS-ROW OCCURS 2 TIMES.
             10 WS-CELL PIC 9(2) OCCURS 3 TIMES.
       01 I PIC 9 VALUE 2.
       01 J PIC 9 VALUE 3.
""",
"""           MOVE 23 TO WS-CELL(2 3)
           IF WS-CELL(I J) = 23
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"occurs_row_group_move": prog(
"""       01 WS-T.
          05 WS-ROW OCCURS 2 TIMES.
             10 WS-CELL PIC X(2) OCCURS 3 TIMES.
""",
"""           MOVE 'ABCDEF' TO WS-ROW(2)
           IF WS-CELL(2 1) = 'AB' AND WS-CELL(2 3) = 'EF'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"search_all_descending": prog(
"""       01 WS-T.
          05 WS-E OCCURS 3 TIMES DESCENDING KEY IS WS-K
             INDEXED BY IX.
             10 WS-K PIC 9(2).
             10 WS-V PIC X(3).
""",
"""           MOVE 09 TO WS-K(1)
           MOVE 05 TO WS-K(2)
           MOVE 01 TO WS-K(3)
           SEARCH ALL WS-E
              AT END PERFORM NO-P
              WHEN WS-K(IX) = 05
                 PERFORM YES-P
           END-SEARCH
           GOBACK.
"""),

"search_all_not_found": prog(
"""       01 WS-T.
          05 WS-E OCCURS 3 TIMES ASCENDING KEY IS WS-K
             INDEXED BY IX.
             10 WS-K PIC 9(2).
             10 WS-V PIC X(3).
""",
"""           MOVE 01 TO WS-K(1)
           MOVE 05 TO WS-K(2)
           MOVE 09 TO WS-K(3)
           SEARCH ALL WS-E
              AT END PERFORM YES-P
              WHEN WS-K(IX) = 07
                 PERFORM NO-P
           END-SEARCH
           GOBACK.
"""),

"set_index_down_by": prog(
"""       01 WS-T.
          05 WS-E PIC 9(2) OCCURS 5 TIMES INDEXED BY IX.
""",
"""           MOVE 22 TO WS-E(2)
           SET IX TO 5
           SET IX DOWN BY 3
           IF WS-E(IX) = 22
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"set_numeric_from_index": prog(
"""       01 WS-T.
          05 WS-E PIC 9(2) OCCURS 5 TIMES INDEXED BY IX.
       01 N PIC 9(2) VALUE 0.
""",
"""           SET IX TO 4
           SET N TO IX
           IF N = 4
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# ---- comparisons ---------------------------------------------------------
# A numeric display item compared against an alphanumeric literal is
# compared as characters, padding included.
"numeric_vs_alnum_literal": prog(
"""       01 WS-N PIC 9(3) VALUE 12.
""",
"""           IF WS-N = '012'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"numeric_different_widths": prog(
"""       01 WS-A PIC 9(3) VALUE 12.
       01 WS-B PIC 9(5) VALUE 12.
""",
"""           IF WS-A = WS-B
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"signed_vs_unsigned_compare": prog(
"""       01 WS-A PIC S9(3) VALUE -5.
       01 WS-B PIC 9(3) VALUE 5.
""",
"""           IF WS-A < WS-B
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"alnum_items_different_len": prog(
"""       01 WS-A PIC X(5) VALUE 'AB'.
       01 WS-B PIC X(2) VALUE 'AB'.
""",
"""           IF WS-A = WS-B
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"zero_against_alnum": prog(
"""       01 WS-A PIC X(3) VALUE '000'.
""",
"""           IF WS-A = ZERO
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"high_values_compare": prog(
"""       01 WS-A PIC X(3) VALUE HIGH-VALUES.
""",
"""           IF WS-A > 'ZZZ'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"class_alphabetic": prog(
"""       01 WS-A PIC X(3) VALUE 'AB1'.
""",
"""           IF WS-A IS ALPHABETIC
              PERFORM NO-P
           ELSE
              PERFORM YES-P
           END-IF
           GOBACK.
"""),

"class_numeric_signed_display": prog(
"""       01 WS-N PIC S9(3) VALUE -123.
       01 WS-X REDEFINES WS-N PIC X(3).
""",
"""           IF WS-X IS NUMERIC
              PERFORM NO-P
           ELSE
              PERFORM YES-P
           END-IF
           GOBACK.
"""),

"sign_condition_negative": prog(
"""       01 WS-A PIC S9(3) VALUE -5.
""",
"""           IF WS-A IS NEGATIVE
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"sign_condition_positive_zero": prog(
"""       01 WS-A PIC S9(3) VALUE 0.
""",
"""           IF WS-A IS POSITIVE
              PERFORM NO-P
           ELSE
              PERFORM YES-P
           END-IF
           GOBACK.
"""),

"numeric_field_vs_wider_lit": prog(
"""       01 WS-A PIC 9(2) VALUE 12.
""",
"""           IF WS-A = 00012
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"compare_group_to_literal": prog(
"""       01 WS-G.
          05 WS-N PIC 9(3) VALUE 007.
          05 WS-C PIC X(2) VALUE 'AB'.
""",
"""           IF WS-G = '007AB'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"lowercase_collates_above": prog(
"""       01 WS-A PIC X VALUE 'a'.
""",
"""           IF WS-A > 'Z'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),


# ---- I/O and status ------------------------------------------------------
# ---- I/O and status ------------------------------------------------------
#
# File status is a *planned input* in this tool - a knob the harness sets -
# rather than something derived from the file's state. These fixtures
# measure the gap that leaves: an operation whose status follows from what
# the program did earlier (closing a file it never opened, reading past
# end-of-file, writing a duplicate key) has one modelled outcome and one
# real one. Green here means the modelled status happened to be right.
"io_open_input_empty_ok": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN INPUT FA
           IF WS-ST = '00'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FA
           GOBACK.
"""),

"io_read_at_end_status_10": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN INPUT FA
           READ FA
              AT END CONTINUE
           END-READ
           IF WS-ST = '10'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FA
           GOBACK.
"""),

"io_close_unopened": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           CLOSE FA
           IF WS-ST = '42'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"io_open_twice": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN INPUT FA
           OPEN INPUT FA
           IF WS-ST = '41'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FA
           GOBACK.
"""),

"io_write_to_input_file": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN INPUT FA
           MOVE 'ABC' TO FA-REC
           WRITE FA-REC
           IF WS-ST = '48'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FA
           GOBACK.
"""),

"io_read_after_at_end": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN INPUT FA
           READ FA AT END CONTINUE END-READ
           READ FA AT END CONTINUE END-READ
           IF WS-ST = '46'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FA
           GOBACK.
"""),

"io_read_into": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
       01 WS-BUF PIC X(10) VALUE 'ZZZZZZZZZZ'.
""",
"""           OPEN OUTPUT FA
           MOVE 'HELLO     ' TO FA-REC
           WRITE FA-REC
           CLOSE FA
           OPEN INPUT FA
           READ FA INTO WS-BUF
              AT END CONTINUE
           END-READ
           IF WS-BUF = 'HELLO     '
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FA
           GOBACK.
"""),

"io_write_from": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
       01 WS-BUF PIC X(10) VALUE 'WORLD     '.
""",
"""           OPEN OUTPUT FA
           WRITE FA-REC FROM WS-BUF
           IF FA-REC = 'WORLD     '
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FA
           GOBACK.
"""),

"io_rewrite_without_read": io_prog(SEQ_SELECT, SEQ_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN OUTPUT FA
           MOVE 'ABC' TO FA-REC
           WRITE FA-REC
           CLOSE FA
           OPEN I-O FA
           MOVE 'XYZ' TO FA-REC
           REWRITE FA-REC
           IF WS-ST = '43'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FA
           GOBACK.
"""),

"io_indexed_open_missing": io_prog(IDX_SELECT, IDX_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN INPUT FB
           IF WS-ST = '35'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"io_indexed_duplicate_key": io_prog(IDX_SELECT, IDX_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN OUTPUT FB
           MOVE 'K001' TO FB-KEY
           MOVE 'AAAAAA' TO FB-DAT
           WRITE FB-REC
           MOVE 'K001' TO FB-KEY
           WRITE FB-REC
           IF WS-ST = '22'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FB
           GOBACK.
"""),

"io_start_key_relation": io_prog(IDX_SELECT, IDX_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN OUTPUT FB
           MOVE 'K001' TO FB-KEY
           WRITE FB-REC
           MOVE 'K005' TO FB-KEY
           WRITE FB-REC
           CLOSE FB
           OPEN INPUT FB
           MOVE 'K002' TO FB-KEY
           START FB KEY IS > FB-KEY
              INVALID KEY CONTINUE
           END-START
           READ FB NEXT AT END CONTINUE END-READ
           IF FB-KEY = 'K005'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           CLOSE FB
           GOBACK.
"""),

"io_start_no_record": io_prog(IDX_SELECT, IDX_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN OUTPUT FB
           MOVE 'K001' TO FB-KEY
           WRITE FB-REC
           CLOSE FB
           OPEN INPUT FB
           MOVE 'K900' TO FB-KEY
           START FB KEY IS > FB-KEY
              INVALID KEY PERFORM YES-P
              NOT INVALID KEY PERFORM NO-P
           END-START
           CLOSE FB
           GOBACK.
"""),

"io_delete_without_read": io_prog(IDX_SELECT, IDX_FD,
"""       01 WS-ST PIC X(2) VALUE '  '.
""",
"""           OPEN OUTPUT FB
           MOVE 'K001' TO FB-KEY
           WRITE FB-REC
           CLOSE FB
           OPEN I-O FB
           MOVE 'K999' TO FB-KEY
           DELETE FB
              INVALID KEY PERFORM YES-P
              NOT INVALID KEY PERFORM NO-P
           END-DELETE
           CLOSE FB
           GOBACK.
"""),

# ---- more language -------------------------------------------------------
# NEXT SENTENCE resumes after the next period, which is not the same place
# as END-IF: everything between the two is skipped.
"next_sentence": prog(
"""       01 A PIC 9 VALUE 1.
       01 B PIC 9 VALUE 0.
""",
"""           IF A = 1
              NEXT SENTENCE
           END-IF
           MOVE 5 TO B.
           IF B = 0
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"initialize_replacing": prog(
"""       01 WS-G.
          05 WS-N PIC 9(3) VALUE 123.
          05 WS-C PIC X(3) VALUE 'XYZ'.
""",
"""           INITIALIZE WS-G REPLACING NUMERIC BY 7
           IF WS-N = 7 AND WS-C = 'XYZ'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"initialize_keeps_filler": prog(
"""       01 WS-G.
          05 WS-A PIC X(2) VALUE 'AB'.
          05 FILLER PIC X(2) VALUE 'CD'.
          05 WS-B PIC X(2) VALUE 'EF'.
""",
"""           INITIALIZE WS-G
           IF WS-G = '  CD  '
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"move_alnum_to_numeric": prog(
"""       01 WS-A PIC X(3) VALUE '123'.
       01 WS-N PIC 9(5) VALUE 0.
""",
"""           MOVE WS-A TO WS-N
           IF WS-N = 123
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"abbrev_not_relation": prog(
"""       01 WS-A PIC 9(2) VALUE 3.
""",
"""           IF WS-A = 1 OR NOT = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"set_88_thru_range": prog(
"""       01 WS-C PIC 9(2) VALUE 50.
          88 IN-RANGE VALUE 10 THRU 19.
""",
"""           SET IN-RANGE TO TRUE
           IF WS-C = 10
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"level88_multi_ranges": prog(
"""       01 WS-C PIC 9(2) VALUE 25.
          88 OK-VAL VALUE 1 THRU 9, 20 THRU 29.
""",
"""           IF OK-VAL
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"compute_exponent": prog(
"""       01 WS-R PIC 9(5) VALUE 0.
""",
"""           COMPUTE WS-R = 2 ** 10
           IF WS-R = 1024
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_mod_negative": prog(
"""       01 WS-R PIC S9(3) VALUE 0.
""",
"""           COMPUTE WS-R = FUNCTION MOD(-7 3)
           IF WS-R = 2
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_rem_negative": prog(
"""       01 WS-R PIC S9(3) VALUE 0.
""",
"""           COMPUTE WS-R = FUNCTION REM(-7 3)
           IF WS-R = -1
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_max_min": prog(
"""       01 WS-R PIC 9(3) VALUE 0.
""",
"""           COMPUTE WS-R = FUNCTION MAX(3 9 5) + FUNCTION MIN(3 9 5)
           IF WS-R = 12
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_reverse": prog(
"""       01 WS-A PIC X(4) VALUE 'ABCD'.
""",
"""           IF FUNCTION REVERSE(WS-A) = 'DCBA'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"fn_numval_signed": prog(
"""       01 WS-A PIC X(6) VALUE '-12.50'.
       01 WS-R PIC S9(3)V99 VALUE 0.
""",
"""           COMPUTE WS-R = FUNCTION NUMVAL(WS-A)
           IF WS-R = -12.50
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"justified_truncates_left": prog(
"""       01 WS-A PIC X(3) JUSTIFIED RIGHT VALUE SPACES.
""",
"""           MOVE 'ABCDE' TO WS-A
           IF WS-A = 'CDE'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"goback_inside_performed": prog(
"""       01 A PIC 9 VALUE 0.
""",
"""           PERFORM SUBP
           PERFORM NO-P
           GO TO DONE-P.
       SUBP.
           PERFORM YES-P
           GOBACK.
"""),

"exit_program_not_main": prog(
"""       01 A PIC 9 VALUE 0.
""",
"""           PERFORM SUBP
           PERFORM YES-P
           GO TO DONE-P.
       SUBP.
           ADD 1 TO A
           EXIT PARAGRAPH.
"""),


# A leading space is data, not decoration: alphanumeric comparison pads the
# shorter operand on the *right* and then compares byte for byte.
# ---- comparison ----------------------------------------------------------
"leading_space_significant": prog(
"""       01 WS-A PIC X(5) VALUE '  ABC'.
""",
"""           IF WS-A = 'ABC'
              PERFORM NO-P
           ELSE
              PERFORM YES-P
           END-IF
           GOBACK.
"""),

"trailing_space_ignored": prog(
"""       01 WS-A PIC X(5) VALUE 'ABC'.
""",
"""           IF WS-A = 'ABC'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

"leading_space_orders": prog(
"""       01 WS-A PIC X(3) VALUE ' AB'.
       01 WS-B PIC X(3) VALUE 'AB '.
""",
"""           IF WS-A < WS-B
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# Two groups may each declare a field of the same name; `OF` says which one.
# A store keyed by the bare name has one cell for both, so writing either
# writes the other.
# ---- identity ------------------------------------------------------------
"qualified_same_name": prog(
"""       01 WS-G1.
          05 WS-F PIC X(2) VALUE 'AA'.
       01 WS-G2.
          05 WS-F PIC X(2) VALUE 'BB'.
""",
"""           MOVE 'ZZ' TO WS-F OF WS-G1
           IF WS-F OF WS-G2 = 'BB'
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# JUSTIFIED RIGHT aligns the sending item on the right of the receiver, so
# the padding lands in front of it. Tested with a slice rather than a whole
# -field comparison, because that is what tells the two alignments apart.
"justified_right_slice": prog(
"""       01 WS-A PIC X(5) JUSTIFIED RIGHT VALUE SPACES.
""",
"""           MOVE 'AB' TO WS-A
           IF WS-A(4:2) = 'AB' AND WS-A(1:3) = SPACES
              PERFORM YES-P
           ELSE
              PERFORM NO-P
           END-IF
           GOBACK.
"""),

# SEARCH VARYING an index *of the table being searched* uses that index for
# the scan; the table's first index is left where it was.
# VARYING an index *of the table being searched* makes that index the one
# the scan steps; the table's first index stays where it was.
"search_varying_own_index": prog(
"""       01 WS-T.
          05 WS-E PIC X(2) OCCURS 4 TIMES INDEXED BY IX IY.
""",
"""           SET IX TO 1
           SET IY TO 1
           SEARCH WS-E VARYING IY
              AT END PERFORM YES-P
              WHEN IX = 3
                 PERFORM NO-P
           END-SEARCH
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
            print("%-32s SKIP  %s" % (name, r["note"][:80]))
            continue
        if r["identical"]:
            print("%-32s ok" % name)
        else:
            d = r["first_divergence"]
            print("%-32s DIVERGES at %d: cobc=%s tool=%s" % (name, d["at"], d["real"], d["mine"]))
            print("%-32s   cobc: %s" % ("", r.get("_real", "")))
            bad.append(name)
    print("\n%d/%d fixtures diverge" % (len(bad), len(only)))
    print("diverging:", ", ".join(bad))


if __name__ == "__main__":
    main()
