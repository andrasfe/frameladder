       IDENTIFICATION DIVISION.
       PROGRAM-ID. C13.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-J PIC 9(2).
       PROCEDURE DIVISION.
       A-MAIN.
           PERFORM VARYING WS-J FROM 1 BY 1 UNTIL WS-J > 3
              PERFORM B-STEP
           END-PERFORM
           GOBACK
           .
       B-STEP.
           CONTINUE
           .
