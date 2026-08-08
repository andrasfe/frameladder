       IDENTIFICATION DIVISION.
       PROGRAM-ID. C11.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-I PIC 9(2) VALUE 0.
       PROCEDURE DIVISION.
       A-MAIN.
           PERFORM UNTIL WS-I > 2
              PERFORM B-BODY
              ADD 1 TO WS-I
           END-PERFORM
           GOBACK
           .
       B-BODY.
           CONTINUE
           .
