       IDENTIFICATION DIVISION.
       PROGRAM-ID. C07.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-F PIC X VALUE 'N'.
       PROCEDURE DIVISION.
       A-MAIN.
           PERFORM B-GATE THRU B-END
           GOBACK
           .
       B-GATE.
           IF WS-F = 'Y'
              GO TO B-END
           END-IF
           .
       B-MID.
           CONTINUE
           .
       B-END.
           CONTINUE
           .
