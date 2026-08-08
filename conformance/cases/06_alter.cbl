       IDENTIFICATION DIVISION.
       PROGRAM-ID. C06.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-F PIC X VALUE 'N'.
       PROCEDURE DIVISION.
       A-MAIN.
           ALTER B-JUMP TO PROCEED TO D-TWO
           PERFORM B-JUMP
           GOBACK
           .
       B-JUMP.
           GO TO C-ONE
           .
       C-ONE.
           GOBACK
           .
       D-TWO.
           GOBACK
           .
