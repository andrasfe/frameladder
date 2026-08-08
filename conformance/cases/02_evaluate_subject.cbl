       IDENTIFICATION DIVISION.
       PROGRAM-ID. C02.
       DATA DIVISION.
       WORKING-STORAGE SECTION.
       01  WS-S PIC X(4) VALUE 'BBBB'.
       PROCEDURE DIVISION.
       A-MAIN.
           EVALUATE WS-S
             WHEN 'AAAA'
               PERFORM B-A
             WHEN 'BBBB'
               PERFORM B-B
             WHEN OTHER
               PERFORM B-O
           END-EVALUATE
           GOBACK
           .
       B-A.
           CONTINUE
           .
       B-B.
           CONTINUE
           .
       B-O.
           CONTINUE
           .
