       IDENTIFICATION DIVISION.
       PROGRAM-ID. C08.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-RC PIC XX VALUE '04'.
       PROCEDURE DIVISION.
       A-MAIN.
           IF WS-RC = '00' OR '04'
              PERFORM B-OK
           ELSE
              PERFORM C-BAD
           END-IF
           GOBACK
           .
       B-OK.
           CONTINUE
           .
       C-BAD.
           CONTINUE
           .
