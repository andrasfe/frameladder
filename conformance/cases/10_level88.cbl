       IDENTIFICATION DIVISION.
       PROGRAM-ID. C10.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-EOF PIC X VALUE 'N'.
           88  IS-EOF VALUE 'Y'.
           88  NOT-EOF VALUE 'N'.
       PROCEDURE DIVISION.
       A-MAIN.
           IF NOT-EOF
              PERFORM B-MORE
           END-IF
           SET IS-EOF TO TRUE
           IF IS-EOF
              PERFORM C-DONE
           END-IF
           GOBACK
           .
       B-MORE.
           CONTINUE
           .
       C-DONE.
           CONTINUE
           .
