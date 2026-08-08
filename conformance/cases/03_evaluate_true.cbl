       IDENTIFICATION DIVISION.
       PROGRAM-ID. C03.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-N PIC 9(2) VALUE 07.
       PROCEDURE DIVISION.
       A-MAIN.
           EVALUATE TRUE
             WHEN WS-N GREATER 10
               PERFORM B-BIG
             WHEN WS-N GREATER 5
               PERFORM B-MID
             WHEN OTHER
               PERFORM B-SMALL
           END-EVALUATE
           GOBACK
           .
       B-BIG.
           CONTINUE
           .
       B-MID.
           CONTINUE
           .
       B-SMALL.
           CONTINUE
           .
