       IDENTIFICATION DIVISION.
       PROGRAM-ID. C01.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-F PIC X VALUE 'N'.
       PROCEDURE DIVISION.
       A-MAIN.
           IF WS-F = 'Y'
              PERFORM B-YES
           ELSE
              PERFORM C-NO
           END-IF
           GOBACK
           .
       B-YES.
           CONTINUE
           .
       C-NO.
           CONTINUE
           .
