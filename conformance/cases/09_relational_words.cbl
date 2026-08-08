       IDENTIFICATION DIVISION.
       PROGRAM-ID. C09.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-A PIC 9(3) VALUE 005.
       01  WS-B PIC 9(3) VALUE 010.
       PROCEDURE DIVISION.
       A-MAIN.
           IF WS-A NOT GREATER WS-B
              PERFORM B-LE
           END-IF
           IF WS-A EQUAL 005
              PERFORM C-EQ
           END-IF
           IF WS-B NOT EQUAL WS-A
              PERFORM D-NE
           END-IF
           GOBACK
           .
       B-LE.
           CONTINUE
           .
       C-EQ.
           CONTINUE
           .
       D-NE.
           CONTINUE
           .
