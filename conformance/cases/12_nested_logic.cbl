       IDENTIFICATION DIVISION.
       PROGRAM-ID. C12.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-A PIC X VALUE 'Y'.
       01  WS-B PIC X VALUE 'N'.
       PROCEDURE DIVISION.
       A-MAIN.
           IF WS-A = 'Y' AND WS-B = 'Y'
              PERFORM B-BOTH
           ELSE
              IF WS-A = 'Y' OR WS-B = 'Y'
                 PERFORM C-EITHER
              ELSE
                 PERFORM D-NEITHER
              END-IF
           END-IF
           GOBACK
           .
       B-BOTH.
           CONTINUE
           .
       C-EITHER.
           CONTINUE
           .
       D-NEITHER.
           CONTINUE
           .
