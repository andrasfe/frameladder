---
name: witness-pattern-discovery
description: Discover why branch directions in an arbitrary COBOL program have no witness, and implement a new generic mechanism that produces them. Use when witness coverage plateaus on a program or corpus and the existing battery phases do not move it.
---

# Witness pattern discovery

You are extending `frameladder`'s witness battery to cover a pattern it does
not yet speak. A **witness** is a stored, replayable recipe — entry state, I/O
world, stub outcome series, terminals — that demonstrably takes one branch
direction when run through the interpreter from program entry. The battery
(`python3 -m frameladder.cli <prog> --copybooks <dir> --json witnesses`)
already stacks several mechanisms; your job is the residual it leaves.

This skill encodes a loop that took two corpora from 35% to 85%+ witness
coverage in one night. Every rule in it was paid for. Follow the loop; do not
skip to building.

## The loop

### 1. Measure, never assume

```bash
python3 -m frameladder.cli PROG.cbl --copybooks CPY --json witnesses --out /tmp/w.jsonl
```

Read `witnessed / directions_total` and the `missing` list. Pool across every
program you have — **a three-program sample will lie to you** (one such sample
read 100% while the corpus read 87.9%). Keep the exact command and seed; every
later claim is a diff against this number.

### 2. Classify the residual by what would be needed

Bucket each missing direction by mechanism, not by syntax. The buckets that
recur, with the mechanism that answers each — check the battery does not
already own it before building anything:

| the direction needs | existing mechanism |
|---|---|
| a value at entry the plan derives | plans phase (`ladder.plan_for_branch`) |
| a value at entry nobody derives | overlays + samples from the literal pool |
| files present / absent / at-end | the three I/O worlds |
| record N of a series, or a fault at position k | `sequences.sequence_worlds` / `fault_worlds` |
| a stub to return a specific status code | `stubsearch` (backward from the direction) |
| mid-run state no entry value can produce | `lift` frontier phase |
| cycle-2+ state (CICS re-entry, carried commarea) | `reentry` |
| a status channel the tool has no vocabulary for | add the channel (see §5) |
| an all-valid multi-field screen, then one-field-spoiled | repair loop (may not exist yet — check) |

Whatever does not fit any row is your pattern.

### 3. Diagnose before building

For a handful of representative missing directions, find out **why** every
run misses. Run the best existing recipe under the interpreter and read the
trace — the guard events say exactly which condition went which way and what
the operands held. Three root causes look identical from outside and need
different fixes:

- **The run never reaches the paragraph.** Routing or world problem, not a
  value problem. Check what the run's `stopped` reason is: an abend means a
  world staged nothing; "ran to completion" means a guard upstream.
- **The paragraph runs but the decision never evaluates.** It sits under
  another condition — the diagnosis recurses onto that one.
- **The decision evaluates, always the same way.** Now it is a value problem:
  find the tested field's writers (`provenance.writes_to`), and whether
  anything can produce the wanted value. If *no writer exists at all*, the
  value must enter at entry or from a stub — and if the field is a status
  channel the tool lacks, that is the highest-value fix available.

Suspect the **parser and interpreter before the planner**. The largest single
gains of the record night were a mis-parse (`UNTIL X >= 11 OR SOME-88-FLAG`
read the flag as an operand, so every read loop in that style ran zero times)
and a verification-world defect (every run abended on a missing file before
reaching anything). When a whole class of programs plateaus at a similar
number, it is usually one structural defect, not many hard directions.

### 4. The evidence rule — what a mechanism may consume

Everything the mechanism stages must come from one of exactly two sources:

1. **The program itself**: literals it compares, fields its statements name,
   codes its own WHEN arms list, targets its PERFORMs call, layouts its data
   division declares. Reached through `provenance`, `layout`, `conditions`,
   never through regex over names.
2. **Platform vocabulary**: values fixed by the platform the way HTTP status
   codes are fixed — FILE STATUS, SQLCODE, DFHRESP, DFHAID, DIBSTAT. These
   live in `faults.py` families and may only be *offered* to a field the
   source itself put in that channel (a `FILE STATUS IS` clause, a `RESP()`
   operand, an implicit interface-block field).

Never decide behaviour from how a variable is *named*. The gate is mechanical
and must print 0 before you commit:

```bash
python3 -c "import io,re,tokenize,glob; PAT=re.compile(r'CARDDEMO|CDEMO-|COACTUPC|GAM0|CBACT01C|COTRN|COUSR|CSUTL',re.I); bad=[(p,t.start[0]) for p in sorted(glob.glob('frameladder/*.py')) for t in tokenize.generate_tokens(io.StringIO(open(p).read()).readline) if t.type not in (tokenize.COMMENT,tokenize.STRING) and PAT.search(t.string)]; print(len(bad))"
```

Extend the pattern with the names of whatever corpus you are working on. A
mechanism tuned to one program's vocabulary is worse than no mechanism: it
reports coverage an arbitrary program will not have.

### 5. Adding a status channel (the commonest new pattern)

If the residual tests a field written implicitly by an external operation
(the way every `EXEC SQL` sets SQLCODE and every `EXEC DLI` sets DIBSTAT),
three places must agree, and missing any one makes the channel silently
inert:

1. `provenance.stub_outputs` — the operation implicitly writes the field, or
   no writer is ever recorded and every arm on it looks unproducible.
2. `faults.py` — the value family (success value first, then the codes real
   programs handle) and `channel_of` mapping the exact platform name and/or
   op-key prefix to the family.
3. `conformance_defaults` — `_CHANNEL_OK` / `_CHANNEL_NIL` entries, or
   `io_defaults` raises `KeyError` on the new channel at run time.

The stub-search and world phases then pick the channel up with no further
wiring — that is the point of the evidence chain.

### 6. Implementing a new battery phase

Follow the shape of the existing phases in `cmd_witnesses`:

- **Credit only through the deduplicating `run()`**. Your phase proposes
  recipes; a fresh-interpreter replay decides. Nothing enters the ledger on
  your phase's say-so.
- **Budget-cap it** (`--yourphase N`) and prove the cap harmless: measure at
  2–5× the default and report the saturation point. Raw budget is a measured
  non-mechanism in this repository; if doubling the budget doubles nothing,
  say so in the commit.
- **Order it by cost**: cheapest recipes first, so a witness demands the
  least staging a harness must reproduce.
- **Feed survivors to `lift`** as seeds — a recipe that reaches new ground is
  a frontier other phases can extend.

### 7. Verify like the record night

- **Reproduction, from disk, 100%.** Read the written JSONL back; rebuild a
  fresh Interpreter from nothing but each row; confirm the recorded direction
  is taken. Anything under 100% means your recipe is not self-contained —
  find the leaked state, do not ship the number.
- **Before/after on programs the mechanism does NOT target.** No program may
  go down — with one exception: a drop you can trace to *phantom* coverage
  (a mis-parse or mis-credit previously counting directions that never truly
  ran) is a win. Say it out loud with the mechanism of the phantom.
- The standing bars: full unit suite green, `conformance.microdiff` count
  unchanged, `tests/parser_agreement.py` 100%, genericity gate 0.
- If you touch the parser or interpreter, run `conformance.differential`
  against GnuCOBOL on the batch programs — the interpreter is the authority
  for witnesses, and GnuCOBOL is the authority over the interpreter.

### 8. Report negatives as first-class results

The record night's ledger of *dead ends* is worth as much as its gains:
free-slot mutation (0.27–1.60 new directions per 100 runs vs derivation's
9.61), route-cost ordering (exactly 0), raw budget (saturates everywhere).
If your mechanism measures at zero, write the number, the reason, and where
the idea *would* pay, then stop. A measured zero closes a branch of the
search space for every agent after you; an unmeasured mechanism reopens it.

## Failure modes that have actually happened here

- **`PERFORM A THRU B` is not a call to "A THRU B"** — it enters at A and
  runs the range. This has bitten three separate mechanisms in one session.
  Resolve ranges to their member paragraphs everywhere a target is recorded.
- **A validator that convicts what it cannot evaluate.** A conformance check
  that stringifies conditions and re-parses them turned `X NOT NUMERIC` into
  a comparison against the literal `'NUMERIC'` and reported correct code as
  wrong. Treat "cannot judge" as no evidence, never as evidence against.
- **88-level condition-names in abbreviated conditions** are conditions, not
  elided operands. Only the data division can tell — thread the names table,
  never guess from shape.
- **The bare world is not neutral.** Under it a batch program abends at its
  first OPEN; every plan then fails identically at depth 1–2 regardless of
  target. Uniform shallow failure across many plans is one structural cause,
  not many hard directions.
- **Counting errors flatter you.** A probe that counts already-covered keys
  as new hits reported 82 arms cracked when the truth was 9. Recount from
  the ledger diff, not from the mechanism's own logs.

## Where things live

| | |
|---|---|
| `frameladder/ledger.py` | witness recipes, crediting, the missing list |
| `cmd_witnesses` in `cli.py` | the battery and its phase order |
| `frameladder/stubsearch.py` | backward-from-direction staging; the model phase to copy |
| `frameladder/reentry.py` | multi-cycle recipes; task-boundary byte carry |
| `frameladder/lift.py` | frontier search from seeds, witness-carrying |
| `frameladder/faults.py` | platform value families and `channel_of` |
| `frameladder/provenance.py` | who writes what, stub outputs, evidence chains |
| `AGENTS.md` | the development discipline this skill assumes |
