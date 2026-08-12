# Witness coverage: consolidated findings

The mission: raise witness coverage — directions with at least one stored,
replayable recipe demonstrably taking them from program entry — across two
corpora (CardDemo CICS set + a side batch/IMS set, 38 programs). This
document is the record of what moved the number, what did not, and what is
left, so the residual is a classified list rather than a mystery.

## Final scoreboard

| pool | witnessed / directions | coverage |
|---|---|---|
| CardDemo | 2,824 / 3,288 | 85.9% |
| side set (batch + IMS) | 951 / 1,126 | 84.5% |
| **combined** | **3,775 / 4,414** | **85.5%** |

24 of 38 programs at ≥90%. Floor: COACTUPC 72.6%, COTRTLIC 72.9%.
Trajectory over the run: 35.3% → 72.4% (honest crediting) → 80.6%
(stub axis + structural fixes) → 85.5% (re-entry).

Every number above reproduces from disk: reading the witness JSONL back and
rebuilding a fresh interpreter from nothing but each row re-takes the
recorded direction 100% of the time.

## What moved the number (in order of impact)

1. **The witness ledger** (`ledger.py`) — the single largest gain was not a
   new mechanism but honest crediting: every run is a witness for *every*
   direction its trace took, not one bit for the direction it targeted. The
   first (cheapest) recipe per direction is kept. 35.3% → 72.4% with zero
   new runs.
2. **Structural fixes to parser and interpreter** — a mis-parse of
   abbreviated conditions containing 88-level condition-names
   (`UNTIL X >= 11 OR SOME-88-FLAG`) made every read loop in that style run
   zero times; out-of-line `PERFORM VARYING/TIMES/TEST AFTER` discarded the
   clause; the bare verification world abended every batch program at its
   first OPEN (verified plans 804 → 1,161 after worlds/overlays/EXEC axis).
   When many programs plateau at a similar number it is one structural
   defect, not many hard directions.
3. **Stub-outcome search** (`stubsearch.py`) — backward from a missing
   direction to the STUB writer of its tested field, staging codes the
   program's own WHEN arms list. +127 directions pooled over ten programs;
   COBIL00C 58.3% → 97.6%.
4. **DL/I as a status channel** — DIBSTAT wired the same three places as
   SQLCODE (`provenance.stub_outputs`, `faults.py` family + `channel_of`,
   `conformance_defaults`). Side IMS set +38; CBPAUP0C 67.3% → 84.6%.
5. **CICS re-entry** (`reentry.py`) — cycle-completion entry states gated on
   the program's own `EXEC CICS RETURN TRANSID`, AID keys from source
   comparisons, and a task-boundary byte carry in the interpreter for
   childless commareas. +7.7% pooled on the mission set; COUSR00C → 91.4%,
   COTRN00C → 91.2%.
6. **Witness-carrying lift frontier** (`lift.py` `on_run`) — frontier search
   now emits full recipes, +80 directions on the worst six programs.

## Measured negatives (first-class results)

- **Free-slot mutation**: 0.27–1.60 new directions per 100 runs, versus
  9.61 for derivation-based planning. Not worth its budget.
- **Route-cost ordering** of plan attempts: exactly 0 new directions.
- **Raw budget**: every phase saturates; doubling run counts past the
  defaults adds nothing on any measured program.
- **Prefix witness reuse**: +1 direction total.
- **Symbolic paragraph summaries** did not directly add witnesses; they were
  merged instead as a conformance bar (`summary_check`, ~90% fidelity,
  tracked like microdiff).

## Residual: 639 directions, classified

Concentrated, not diffuse:

| program | missing | mechanism required |
|---|---|---|
| COACTUPC | 235 | an all-valid ~40-field screen for an 84-arm first-match attribute chain, plus multi-cycle staged reads |
| COTRTLIC | 84 | same shape (array-edit cascade; see `1240-EDIT-ALPHANUM-REQD`, `2200/2300` attr blocks) |
| COCRDUPC | 50 | same family |
| COTRN02C | 33 | same family |
| COPAUA0C | 21 | decision-reason EVALUATE: payload-driven 88s + one MQ code |

The mechanism that answers the top four — a greedy cascade **repair loop**
(run, read the first failed validation flag from guard events, repair that
field from the edit's own evidence, rerun; then one-field-spoiled variants)
— was specified and prototyped but stopped before verification. The
prototype lives unmerged on `agent/w90-repair` (`frameladder/repair.py` +
cli/ir/test edits); it has not passed the merge gates and its numbers are
unmeasured.

## Standing merge gates (all green at merge)

- full unit suite (305 tests) green
- genericity gate: token-level scan of executable code for corpus-specific
  names prints 0 (see `.claude/skills/witness-pattern-discovery/SKILL.md` §4)
- 100% from-disk witness reproduction
- no untargeted program regresses, except drops traceable to phantom
  coverage (mis-credits removed by a parser fix) — e.g. COTRTLIC
  77.1 → 72.9 after the abbreviated-condition fix, a win stated as such

## For the next agent

The discover-and-implement loop that produced all of the above is encoded
in `.claude/skills/witness-pattern-discovery/SKILL.md`. Start there; measure
before building.
