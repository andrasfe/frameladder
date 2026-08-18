# The bridge: fuzz a paragraph, feed the next one

What happens when witness coverage on a program is not limited by search
at all. Written from one 35,000-line batch program (`RCO100B`, supplied as
a pre-parsed AST with no data division), where every existing phase
returned almost nothing and the reason turned out to be four silent
structural gaps, not a hard residual.

---

## 1. The mechanism

`frameladder PROG bridge CURRENT-PARA NEXT-PARA` — a separate component,
no battery phase, no shared state.

1. **Fuzz** the current paragraph's closure in isolation, thousands of
   runs, seeded and deterministic. Each run is stored as a
   machine-verified fact `(inputs, directions fired, post-state)`. Values
   come from the closure's own compared literals plus platform
   figuratives; nothing from a field's name.
2. **Sweep** — hand every distinct post-state straight to the next
   paragraph and credit whatever its run takes. This is the whole yield
   (see §4). Post-states are deduplicated on what is *live at the next
   paragraph's entry*: two states agreeing there drive it identically, and
   deduplicating on the full post-state instead spent an entire 6,000-run
   budget on states differing only in fields the consumer never reads.
3. **Learn** an inverse model (MLP, post-state → inputs) over the
   *bridgeable surface* — fields the producer was observed to write that
   the consumer's guards read. It only ever selects among values seen in
   real runs, so it proposes, never invents; and nothing it proposes
   counts until a real run confirms it.
4. **Search** per goal for what the sweep missed, capped, with everything
   the cap drops named as a refusal rather than silently dropped.

Output is not witnesses — nothing here runs from entry. It is *facts* in
the shape `chain.run_chain` consumes, plus, under `--to-entry`, a chain
run that carries them to entry and credits through the one ledger path.

## 2. Four structural gaps, all silent

Found by running, not by reading. Each was worth more than any planner
change.

| gap | scale | effect |
|---|---|---|
| `PERFORM_THRU` as its own AST statement type | 1,138 calls | unrecognised, so every callee a no-op: **2 of 1,035 paragraphs reachable** |
| no ordinals in the AST | all statements | every decision of a kind in a paragraph collapsed onto one coverage key |
| empty attribute maps on `SET`/`WHEN`/`SEARCH` | 190 statements | `SET` set nothing; 41 `WHEN` arms compared against the empty string |
| unknown PIC width used as a *filter* | whole program | the evidence harvest dropped **every** variable; the fuzzer had nothing to vary |

All four are fixed at load time in `cobol._adopt_ast`, which re-derives
missing attributes through this module's own parser rather than growing a
second, approximate definition of what a statement means. The width filter
now applies only when the data division is actually present: judging
nothing must mean no evidence, never evidence against.

Measured on one empty-state run from entry: **2,452 → 7,004 guard events**;
guard evidence on the two largest paragraphs **0 → 46 and 68 variables**.

Two further honesty fixes fell out. The step cap reported truncation as a
clean `STOP RUN / GOBACK`, so a half-finished trace read as a finished one;
it now says so, and scales with statement count instead of being a flat
20,000 (a budget per program size, not per program). And the runaway
detector counted *cumulative* visits per paragraph over a whole run, so in
a batch program any per-record paragraph tripped it as a matter of course;
it now trips only on repetition without progress — no new direction taken
since that paragraph's last visit.

## 3. Why this program is stuck, and it is not search

`RCO100B` performs **28 paragraphs it does not define**, across 162 call
sites. They are genuinely external (the vendor's own transpiler emits
"Stub for missing paragraph" for the same names), not a parse failure.

The largest, `A9999-CALL-GOADCY00` (31 sites), is the date converter.
Absent, `WS-Y2K-CHKDATE-ERROR` keeps its initial value and the very next
guard — `IF WS-Y2K-CHKDATE-ERROR = WC-Y2K-ERROR` — takes the error branch.
Every date conversion in the program fails, forever, inside
`1000-INITIALIZATION`. **`2000-VALIDATE-SCHEDULE-FILE` is never entered,
nor is anything after it**: from-entry execution reaches 123 of 1,035
paragraphs and 5% of directions, for a reason no amount of search can
address. The interpreter now records `performed but not defined: X` as an
approximation, so a run bounded by missing source says so.

This is the named lever: supplying those 28 paragraphs is worth more than
any mechanism in this repository. Pinning the date flag at entry clears
that one loop (8,517 → 82,776 steps) and still gains **zero** directions,
because the run lands in the next loop with the same root cause.

## 4. Measured, on RCO100B

Baseline A is a from-entry sampler (entry states from the program's own
literal pool, every I/O world, standard ledger): **171 directions in 36
seconds**. The full battery, for comparison, credited **141 after 50
minutes** and was still in its first phase - per-direction planning does
not earn its cost on a program of this size.

The bridge over **296 pairs**, one per paragraph holding uncovered
directions, each paired with the prior paragraph writing the most of what
its guards read:

| | directions | of 3,386 |
|---|---|---|
| from-entry sampler (A) | 171 | 5.05% |
| bridge (B) | 1,693 | 50.00% |
| A ∪ B | **1,864** | **55.05%** |
| ∪ stitched walk (below) | **1,944** | **57.41%** |

Paragraphs holding at least one covered direction: **399 of 441 (90.5%)**,
against the 53 a from-entry run even enters.

**Every one of the 4,326 bridged claims reproduced independently** - each
rebuilt from its stored row by a fresh interpreter consulting none of the
generator's bookkeeping. (4,326 counts every claim; 1,693 is the
deduplicated union, since a direction recurs across overlapping closures.)

All 4,326 were credited by the **sweep**. Across the whole run the inverse
model and the per-goal search contributed nothing at all; see §5.

### What this coverage is, and is not

Two different claims are being added together, and conflating them would
overstate the result:

- **171 directions have from-entry witnesses** - a complete recipe that
  drives the direction when the whole program runs from its entry point.
- **1,693 are bridged**: an input state for paragraph P such that running
  P and handing its post-state to paragraph N drives the direction. Both
  executions are real and reproducible, but execution *starts mid-program*
  at P. Nothing shows that state is reachable from entry.

The second is a per-paragraph test input, not a program-level one. It is
the honest ceiling for this program: **92.7% of directions live in
paragraphs a from-entry run never enters**, because of §3.

### Stitching: paragraphs in order, carrying state

A single from-entry run dies where one paragraph traps, and takes the
whole program with it. Running paragraph by paragraph in source order and
carrying the state forward changes what a trap costs - it ends that
paragraph's segment, and the walk continues.

**1,090 directions (32.19%) in 52 seconds**, entering 1,033 of 1,035
paragraphs. It converges immediately: pass 1 adds 1,074, pass 2 adds 14,
pass 3 adds 2.

Per unit of compute that is roughly a hundred times the bridge's yield,
and the two are complementary rather than redundant: the walk finds 111
directions the 296-pair fleet never did, the fleet holds 780 the walk
misses. The walk gives every paragraph one *realistic* accumulated state;
the bridge gives one paragraph thousands of deliberately varied ones.

Same caveat as the bridge: each hop starts a fresh interpreter with
carried state, so this is a plausible execution history, not a proven
reachable one.

### Seeding the producer from the consumer

`--seed-from-consumer` adds the *next* paragraph's compared literals to the
*current* paragraph's fuzz pools. A producer that moves an input straight
through can only ever emit a value the fuzzer tried at its input, so a
literal only the consumer compares against was unreachable by
construction - the producer's own text never mentions it. Still inside the
evidence rule: the program's own words, just a different paragraph's share
of them.

Measured on one pair, same seed and same run budget:

| arm | bridged directions |
|---|---|
| producer evidence only | 52 |
| + consumer literals | **74** (+42%) |

### Budgeting the fuzz

`--runs` is a poor unit of cost. Per-run execution time varied **30x**
across the pairs measured - 0.007s for an 82-paragraph closure against
0.226s for a 216-paragraph one - so the same 6,000-run budget is one
minute of wall clock on one pair and half an hour on another. Two of the
fourteen pairs were still fuzzing when the rest had finished and been
aggregated. The novelty stall (`STALL`) already ends a fuzz that stops
learning, but it cannot fire while a slow closure is still producing new
signatures; size the budget per closure, or bound it by time.

### Two ways this exhausts a machine, and the fixes

Both found by running it at scale, not by reading it.

**A row per run, holding the whole entry state.** `Table.record` stored the
merge of the base state and the fuzz delta, so every row carried a copy of
all 2,823 declared fields. At a 60,000-run budget that is over a hundred
million dictionary entries in one process, and twelve concurrent jobs took
a 28GB machine down. Rows now store the delta only - the base is constant
and re-applied wherever a row is replayed, so nothing is lost - and
retention is capped, past which only rows showing a *new signature* are
kept, so memory tracks distinct behaviour rather than run count. Measured
after: **323MB peak RSS** for a 6,000-run job on the largest pair.

**BLAS threads times process count.** The inverse model's backend defaults
to one thread per core, so twelve concurrent jobs asked for far more
threads than the machine has. Pin `OMP_NUM_THREADS`,
`OPENBLAS_NUM_THREADS` and `MKL_NUM_THREADS` to 1 and let the fleet's own
parallelism be the only source of concurrency.

## 5. Measured negatives (do not re-propose without new evidence)

- **The inverse MLP: 0 directions**, on every pair measured. The sweep
  already extracts what the producer can offer; what remains is refused as
  `next-local-unsolvable` or `independent-of-current`, i.e. blocked by
  something other than the producer's outputs. The model is built,
  attributable (`--no-model`), and currently unpaid-for.
- **Per-goal search after the sweep: 0 directions**, and it is the
  expensive half — one solve builds a whole closure's attempt set, costing
  more than the sweep did for every goal together. Default capped at 40.
- **Pinning guard fields with no writer at entry**: gains 5 directions,
  loses 16 (169 → 158). The blocker is a loop, not a guard.
- **Direction bits as model features**: actively harmful. A query knows
  the post-state it wants but not which directions the producing run fired,
  so those columns were ones in training and zeros in every query.

## 6. Gates, at the state described here

- full unit suite green (351 tests), and green on six consecutive runs -
  an id()-keyed cache made one test in three fail until it was found
- `conformance.differential` against GnuCOBOL: **13/13 programs traced
  identically**, so the interpreter changes here keep compiler agreement
- genericity scan over executable code prints **0**, with this corpus's own
  vocabulary added to the pattern
- every bridged direction independently reproduced from its stored row by
  a fresh interpreter that consults none of the generator's bookkeeping

## 7. Reproducing

```bash
frameladder choices.ast bridge CURRENT NEXT \
    --defaults ws-defaults.json --baseline base.jsonl \
    --runs 6000 --budget 6000 --seed 7 --search-goals 0 --progress 60 \
    --out bridge.jsonl [--to-entry]
```

`--defaults` supplies declared WORKING-STORAGE values for an AST that
carries no data division. `--to-entry` walks the bridged directions to
program entry and writes real witnesses; those reproduce from disk at
100%. The learned half needs `pip install frameladder[learn]` and says so
when absent.
