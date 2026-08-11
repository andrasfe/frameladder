# frameladder

Work out what inputs reach a deep target in a COBOL program, by starting at
the target and walking **outwards**.

```bash
frameladder COACTUPC.cbl verify EDIT-US-PHONE-LINENUM
```
```
REACHED   0000-MAIN -> EDIT-US-PHONE-LINENUM
chain     0000-MAIN -> 1000-PROCESS-INPUTS -> 1200-EDIT-MAP-INPUTS
          -> 1260-EDIT-US-PHONE-NUM -> EDIT-AREA-CODE -> EDIT-US-PHONE-PREFIX
          -> EDIT-US-PHONE-LINENUM
```

Nothing to install, no dependencies, no network, no model.

Working on the repo rather than with it? See [`AGENTS.md`](AGENTS.md).

---

## Why outwards

Forward search asks *"what inputs, when run, happen to land here?"* and answers
by sampling. That works until the target needs two values produced in two
different frames to agree — a card number read from one file matching a table
entry loaded from another. Sampling then has to guess the same needle twice,
and no budget buys that.

The ladder asks the mirror question. Starting at the deepest frame, where the
obligation is smallest and most concrete, it rewrites each obligation into one
on the caller's own arguments:

```
goal on (g,h,k)  --lift through f2's body-->
goal on (d,e,f)  --lift through f1's body-->
goal on (a,b,c)  -> emit
```

COBOL paragraphs have no parameters, so "arguments" means the live-in set and
the call chain is the PERFORM/GO TO chain. Nothing else changes.

## Constraints that fix a relationship, not a value

The recurring win is a constraint shape where the condition says everything
about how two values relate and *nothing* about what they are. There is then
nothing to search for — construct a witnessing pair and write it down.

**Rendezvous** (`A = B`, both produced). A key read from one file matching a
key loaded from another. Sampling has to draw the same needle twice; the ladder
picks any value and plants it at both producers. O(1) against |domain|².

**Separation** (`A != B`) and **ordering** (`A < B`, `A > B`). The same shape.
Two values that merely differ, or are merely in order, are constructed rather
than found.

**Guard avoidance.** An obligation contradicting a literal assignment is not
dead if that assignment sits under a condition. `MOVE 'Y' TO END-OF-FILE` under
`WHEN '10'` means `END-OF-FILE != 'Y'` is reachable by making the return code
anything else. The obligation moves onto the guard and the ladder recurses.

**Outcome sequences.** A read returns `'00'` for a record and `'10'` at
end-of-file. Two obligations on one status field are not a contradiction —
they are consecutive outcomes of one operation, and the plan emits them in
order. Recognising this needs the `FILE STATUS IS` clause and the `FD` record
to be attributed to the I/O that writes them, so both are parsed.

**A specific reason, scoped to the chain.** When a variable the program
*never writes* is required to hold two different values, that is not a gap in
the search — the chain cannot be taken, and the tool says so in O(1) rather
than reporting a vague failure. On COACTVWC: `WS-INPUT-FLAG must be '0' and
also '1', and nothing on the chain writes it`.

**Read the scope, because an earlier version of this section did not have
one.** It called these *infeasibility proofs* and claimed 40 of 41 unresolved
obligations were proofs of dead code. That was wrong, and measurably so: on
GAM0VII, 7 of the 24 directions declared infeasible were afterwards observed
executing. The obligations come from **one route**. A contradiction between
them rules out that route and says nothing about the program — another way in
may carry no opinion about the field at all. For a tool whose output decides
what gets tested, "this code is dead" is the most expensive sentence to get
wrong, so it is no longer said.

## Free values are not free

`frameladder` knows something unusual: for every binding it makes, whether the
constraint pinned the **value** or only a **relationship**. Across the corpus,
**56% of bindings are free** — the plan reaches its target under *any*
assignment to them.

Those slots used to be filled with `'AAAA'`, `'BBBB'` and `4111111111111111`.
For migration parity that is the one choice guaranteed to reveal nothing.

So spend them. Each free slot becomes a set of candidate values, each chosen
because some real migration gets it wrong, and each still satisfying the
constraint that made the slot free:

- **PIC boundaries** — width-exact, one byte over (COBOL truncates the tail
  silently), all-nines, one past the field, negative zero, a digit finer than
  the scale
- **Figurative constants** — `SPACES`, `LOW-VALUES`, `HIGH-VALUES` are three
  distinct states that ports habitually collapse into one
- **Program literals** — the values this variable is actually compared against
- **Level-88 values** — an equivalence partition the programmer wrote down
- **Collation crossovers** — see below

```bash
frameladder COACTUPC.cbl family EDIT-US-PHONE-LINENUM
```
```
14 tests, all reaching EDIT-US-PHONE-LINENUM
varied                 category           why
(baseline)             baseline           the plan as derived
ACUP-CHANGE-ACTION     spaces             all spaces
WS-DATACHANGED-FLAG    low-values         LOW-VALUES; ports often collapse this into empty/null
LIT-THISPGM            over-width         one byte too long; COBOL truncates the tail silently
```

One derivation, many tests: the chain is identical for every member, so the
marginal cost of another test is near zero. Corpus-wide that turns 563
derivations into **3,784 validated tests** — every one re-verified as still
reaching its target, and every one differing in a single value, so a
divergence is attributable to that value.

### Collation is the sharpest instance

z/OS is EBCDIC; essentially every migration target is ASCII. They disagree on
ordering for exactly three class pairs, verified against GnuCOBOL under both
collating sequences rather than taken from lore:

| pair | ASCII | EBCDIC |
|---|---|---|
| digit vs upper | `'5' < 'M'` ✓ | ✗ |
| digit vs lower | `'5' < 'm'` ✓ | ✗ |
| upper vs lower | `'M' < 'm'` ✓ | ✗ |

Same class, or anything against space, is stable. So an ordering constraint
witnessed by `'AAAA'` and `'BBBB'` holds identically on both platforms and
proves nothing, while one witnessed across a class boundary **flips the
branch**. That is a control-flow divergence, the worst kind — the migrated
program does not merely compute a different number, it takes a different path.
The tool applies this only to alphanumeric comparisons, because numeric ones
compare values rather than bytes and are stable.

## Witnesses are reusable

A state that opens a paragraph is evidence about a *frame*, not about the one
path that found it. Chains overlap heavily — **63% of targets have a chain
that extends another target's** — so it is worth keeping what was learned.

Measuring where that actually pays gave a surprise. Two mechanisms were
plausible:

- **Prefix inheritance** — offer a shorter chain's values as preferences for a
  longer one. Measured gain: **0%**. The value chooser is deterministic, so
  targets sharing a prefix already agreed; there was no inconsistency to
  remove. Kept anyway (`preferred=`, which moves only *free* slots and never
  overrides a constraint) because it stops being a no-op the moment values
  vary — which is exactly what families do.
- **State identity** — 563 targets ask for only **189 distinct states**, and
  2,631 family members for **856**. Roughly two-thirds of the work is asking a
  question someone already asked.

The second is where the money is, because one compile of a state produces a
whole *trace*, and a trace answers reachability for every paragraph at once.
So the unit of work is the distinct state, not the target:

| | per target | per distinct state |
|---|---|---|
| compiles | 90 | **19** (79% avoided) |
| wall clock | 25.0s | **5.5s** |
| confirmation matrix | 21/4/0/65 | identical |

`--witnesses FILE` persists compiler-confirmed witnesses across runs.

Making this sound required computing **live-in** sets — the variables a
paragraph reads before writing. The README had described a paragraph's
"arguments" that way from the start, but nothing computed it; the ladder
worked from call-site guards, which is enough to *reach* a frame and not
enough to say what a witness is really about.

## Heuristics: shape, then plausibility

Two different jobs need two different kinds of value, and both live in the
free slots.

**Shape** comes from class conditions. `IF WS-X IS NUMERIC` compares nothing —
it asks whether the bytes are digits — so the PIC clause decides what
satisfies it. This was previously parsed as a *relation*: `ACCT-ID IS NOT
NUMERIC` became `ACCT-ID != NUMERIC`, comparing the field against the word
`NUMERIC`. Plausible-looking and meaningless, 27 times in the corpus.

**Plausibility** is sought in a strict order, and the order matters more than
the sources.

*Evidence from the program first.* If a field is compared against literals
anywhere in the source, those are what its own logic distinguishes — facts
about this program rather than assumptions about programs in general, and
they work whatever language the names are in. **56% of free bindings get a
value this way.**

*Convention only as a fallback,* consulted when the source says nothing. The
built-in name table is English and US-shaped, and it earns **1%** — so an
estate whose fields are called `GEB-DAT` or `VERS-NR` loses almost nothing,
and `--conventions FILE` supplies its own pack rather than being served
nothing. The name and the shape are read together:

| field | PIC | value |
|---|---|---|
| `ACCT-OPEN-DATE` | `X(8)` | `20250115` |
| `ACCT-OPEN-DATE` | `X(10)` | `2025-01-15` |
| `CUST-ADDR-STATE-CD` | `X(2)` | `NY` |
| `DALYTRAN-ORIG-TS` | `X(26)` | `2025-01-15-12.30.45.000000` |

Both apply only to free slots, so a heuristic can never contradict something
the program requires. Where they compete, shape wins: a realistic date that
fails `IS NUMERIC` is worse than dull digits that pass.

**Where free-slot values come from**

| source | share |
|---|---|
| the program itself — a literal it compares the field against *that satisfies the constraint* | **320 (21%)** |
| genuinely undecided | 1,212 (79%) |

An earlier version of this table claimed 56%. It was wrong: it counted any
literal the field appeared beside, including — for a disequality — the very
value being ruled out. Applying the constraint to the evidence dropped it to
21%, which is the honest figure.

**No token table is consulted by default.** A fixed list of name fragments is
a guess about how other people name things, and programs are not consistent
enough for that to hold. Measured against the corpus it settled 1% of values
and **zero targets of reachability**, so it now ships as `packs/en-US.json`
and is opt-in via `--conventions`.

What replaces it is a sweep of the program's *own* vocabulary. A single
program was written by one team with one convention, so the convention is
discoverable from the source rather than assumed:

```bash
frameladder CBACT04C.cbl names
```
```
CBACT04C: 1 value the program never pins down, sharing 3 tokens.
copybooks read: CVTRA01Y, CVACT03Y, CVTRA02Y, CVACT01Y, CVTRA05Y

token     fields  type          declared in     examples
DIS            1  S9(04)V99     CVTRA02Y.cpy    DIS-INT-RATE
RATE           1  S9(04)V99     CVTRA02Y.cpy    DIS-INT-RATE
```

The entry carries the **type**, not just the shape. `PIC` alone does not
determine representation: `S9(4) COMP` is two binary bytes truncated to four
decimal digits, `S9(4) COMP-3` is three packed bytes with a sign nibble, and
`S9(4) DISPLAY` is four characters with an overpunched sign. They compare
equal and serialise completely differently — which is exactly where a
migration diverges — so `USAGE`, `REDEFINES`, `SIGN` and `OCCURS` are read
alongside `PIC`, and every field records which file declared it.

It covers **every** variable, not just copybook ones. For CBACT04C that is 86
declared in the program and 43 across its five copybooks — and only its five:
loading the whole directory gave 2,640 fields, 95% of them belonging to other
programs, which inflates the declared set that live-in filtering and record
association both key off. `COPY` statements say which members are wanted.

`questions` lists the same set field by field; `bind --why` records a
decision; the journal makes it permanent, so it is asked once and is data
thereafter. Where nothing decides a value, the tool says so instead of
inventing one.

### What the vocabulary turned out *not* to be good for

The obvious next step was to let an undecided field borrow a value from a
related one. Measured on 1,212 undecided slots:

| | share |
|---|---|
| a token sibling could supply a value | 293 (24%) |
| a *same-shape* sibling under a *discriminating* token could | **0 (0%)** |

Every one of the 24% fails once the transfer has to be defensible, and the
reason is the useful part: the fields that need help are overwhelmingly the
ones with **no `PIC` at all**, because their copybook was never loaded. There
is no shape to match on, so there is no safe basis to transfer anything.

So the honest ranking is the unglamorous one:

| | undecided values |
|---|---|
| baseline | 911 |
| **copybooks loaded** | **518 (−43%)** |
| guarded name-based transfer | no change |

Copybook directories are now found automatically beside or just above the
source (`cpy`, `copy`, `copybook`, `cpylib`, …), which picked up 29 of the
corpus programs without being asked. `--copybooks` still overrides.

This also corrected the evaluation: every corpus figure quoted before this
was measured *without* copybooks, and so understated what the tool knows.

The one piece of built-in knowledge that is *not* a naming guess is the
platform's status vocabulary — file status, SQLCODE, CICS RESP. Those are
fixed the way HTTP status codes are fixed, and a field is only offered them
when the source demonstrably puts it in that channel.

**Honest limits.** The corpus figure did not move — and cannot. The
interpreter evaluates only the guards the ladder already lifted, so a
plausible value and `'AAAA'` behave identically to it; validation cascades
that call subprograms are no-ops. The compilable programs abend on file-open
before reaching any validation. So the payoff is real in a real runtime and
**unmeasured here**.

Chasing why class conditions never fired surfaced something sharper: the
ladder takes the *shortest* chain, which is systematically the route that
**skips validation**, because validated paths carry more obligations. Optimal
for reaching code; backwards for parity testing, where the validated path is
where the interesting semantics are. `--via` forces the hard route today; a
"prefer the guarded path" chain selector would do it by default.

## Choosing what an operation returns

Outcomes are picked **by obligation, not by enumeration**. The ladder asks
what a guard on the chain requires, walks back through the MOVE chains to the
operation that produces that variable, and makes it return the required value.

That is the right default: it only ever generates outcomes the program
actually distinguishes. There is no point returning file status 47 to a
program that never tests it, and a harness that enumerates the whole status
table spends most of its budget on branches that do not exist.

It breaks in exactly one place — a **negation**. `IF ACCTFILE-STATUS NOT =
'00'` names the value to avoid and none to use instead, so with nothing else
in evidence the witness invents a string. Measured across the corpus that was
happening 123 times, and an invented string is not a file status: the code
goes on to test it against `'10'` and `'23'` and takes neither branch.

So negations draw on the platform's fixed vocabulary — file status, SQLCODE,
CICS RESP — ordered by how much behaviour each unlocks, with the program's own
literals always ranked first. A field is only offered a vocabulary when it
demonstrably belongs to one: `FILE STATUS IS` names the status field in the
SELECT, `SQLCODE` is `SQLCODE`, a `RESP` operand names itself. No naming
guesswork, because putting status codes into a field that is not a status
field is worse than picking badly.

| | before | after |
|---|---|---|
| invented `'X'` placeholders | 123 | **6** |
| `'10'` end-of-file | 58 | **175** |
| verified reached | 78% | **81%** |

Writing the test for this found a parser bug worth its own mention: `NOT =`
is a word operator that ends in a symbol, and wrapping it in word boundaries
put one after the `=`, which cannot match before a quote. `IF WS-ST NOT =
'00'` therefore fell through to the bare `=` and produced a variable called
`WS-ST NOT`. 63 occurrences in the corpus.

## From field values to a record

A plan says what value a field should hold. A harness needs the *bytes* — the
record a file contains or a subprogram is handed — and the distance between
those two is most of the work of building mainframe test data.

That distance is exactly what `USAGE` closes. `PIC S9(4)` is **four** bytes as
DISPLAY, **three** as COMP-3 and **two** as COMP, so a layout computed from
`PIC` alone puts every field after the first packed one at the wrong offset —
and a record wrong from byte nine onwards is worse than no record, because it
looks plausible. `REDEFINES` does not advance the cursor; `OCCURS` multiplies
a whole subtree; `FILLER` cannot be referenced but still takes space.

`layout.py` computes offsets and lengths, checked against the compiler the
same way everything else is:

```
records checked against GnuCOBOL: 19
  lengths agree : 19 (100%)
```

Worth being clear about what this does *not* yet do: it places DISPLAY values,
and packed and binary fields need real encoding rather than text. It is the
groundwork for comparing outputs, not a finished record writer.

## The external world

A program's interesting behaviour is mostly decided by things it does not
compute: what a file read returned, whether an open succeeded, what a
subprogram put in the commarea, what DB2 said. A test has to *supply* those,
so the plan names them as **outcomes** rather than pretending they are inputs.

An outcome is identified by the operation and by whatever selects it:

| kind | identity | how the outcome arrives |
|---|---|---|
| file I/O | `OPEN-INPUT:ACCTFILE-FILE`, `READ:XREF-FILE` | the `FILE STATUS IS` variable, and the `FD` record |
| subprogram | `CALL:CBSTM03B` | the `USING` area |
| CICS | `EXEC:CICS:READ` + `DATASET(...)` | `RESP`, `RESP2`, `INTO`, `COMMAREA` |
| DB2 | `EXEC:SQL:SELECT` | `SQLCODE` always, plus `INTO :host-vars` |

Three things make this work:

**Discrimination.** One subprogram called twice is two operations if something
distinguishes them. The literals set before a call are compared *across* call
sites and only the fields that actually vary are kept — a DD name selects,
blanking the output area does not. CICS resource clauses (`DATASET`, `MAP`,
`PROGRAM`) do the same job and are treated the same way.

**Sequences.** An operation returns a *series*: a record, another record, then
end-of-file. Two obligations on one status field are consecutive outcomes, not
a contradiction, and the plan emits them ordered. The end-of-file value is
derived rather than guessed — it is the literal that guard avoidance steered
away from. `--stub-repeat`, `--terminal` and `--default` control delivery
(`--default` is what an operation returns when no planned outcome matches it,
which is different from what it returns once they run out).

**Mode.** `OPEN INPUT` and `OPEN OUTPUT` are different operations, because
opening a missing file for input fails where opening it for output creates it.

### What is weak here

- **`--terminal` is per operation, not per invocation.** A program routing its
  opens and its reads through one subprogram cannot have both a succeeding
  open and an ending read. This is what still caps CBSTM03A.
- **CICS and SQL are shallow.** Operands and status channels are modelled;
  cursors, result sets, `SYNCPOINT`/rollback, pseudo-conversational state
  across `RETURN TRANSID` and commarea round-trips are not.
- **No state setup.** The plan says what an operation should return; it does
  not build the VSAM file, the DB2 rows or the queue that would make a real
  system return it. On a migration that gap is most of the work.
- **Stubbing hides the seam.** A transpiled program is usually faithful
  *inside* and lossy at its edges — DB2 to Postgres, VSAM emulation, date
  handling. Stubbing those interfaces tests the part that was already
  semantics-preserving and skips the part where divergence actually lives.
  This is the strongest argument against using the tool as a primary parity
  oracle, and it stands.

## The harness is a constraint, not a filter

A plan is derived against this repository's own interpreter, where every
variable is settable and every operation is replayable. Whatever will actually
run it is narrower — and the expensive part is that the narrowing is silent.
A harness that cannot inject a field drops it in projection; the plan still
runs, still reports a status, and no longer means anything. On the one
integration measured, of 45 internally valid plans **35 could not be
represented, 4 reached COBOL, 3 succeeded, and all 3 landed on branches that
were already covered.**

`capability.py` is the contract that makes that sayable up front: which
variables the harness can inject, which operations it can replay and which
fields each of those can set, how long an outcome series it can hold, and
which directions it still has not covered. Two commands use it.

```bash
frameladder PROG.cbl --copybooks ./cpy --json replay 3000-VALIDATE --proxy
frameladder PROG.cbl --copybooks ./cpy represent --proxy --profile-aware
```

`replay` emits the whole ordered series a harness runs without interpreting
anything: per operation, outcome 1..n in delivery order **and the terminal**,
truncated to `max_outcomes` where the profile states one. What it will not do
is drop something quietly. Every field the profile refuses, every input it
cannot inject and every outcome past the limit comes back in `reasons`, in the
harness's own words (*cannot inject X*, *cannot replay READ:F*), and an
outcome whose fields were all refused stays in place holding nothing — because
removing it would shift every later outcome onto an earlier call.

`represent` classifies every plan the tool would emit as representable or not,
with those same reasons.

### What it measures, with a profile nobody has stated yet

No harness states a profile today, so `--proxy` derives one from the source
using the rule a real one uses: **a variable is injectable when the program
compares it against a literal or it carries an 88-level `VALUE`**, and **an
operation is replayable when the source puts one of its outputs in a status
channel — and can set exactly those status fields**, because a mock record
carries a status and not a record image. Which fields are status fields comes
from `FILE STATUS IS`, a `RESP` operand and `SQLCODE`; never from a name.

**This is a proxy and it proves nothing about any harness.** It is an upper
bound in three known ways, all of them in the same direction: injectability is
treated as a property of the variable rather than of the entry state; a
program in which no operation has a status channel gets no operation
constraint at all (8 of 46 programs, 15 solved plans that bind an outcome);
and the real rule has name-based clauses this deliberately omits.

Solved plans — one per reachable paragraph — that the profile could not
replay:

| | programs | plans | unrepresentable | median | range |
|---|---|---|---|---|---|
| the corpus this was built against | 29 | 494 | **53.2%** | 0.0% | 0–96.6% |
| everything else | 17 | 229 | **55.0%** | 10.3% | 0–100% |

The median is 0 and the pooled figure is 53%, which is the whole shape of the
result: **16 of those 29 programs lose nothing and 7 lose more than half**.
The batch programs are almost entirely representable; the loss is concentrated
in the CICS screen programs, where the plan depends on an operation whose
outcome is not in any status channel — a `SEND MAP`, an `XCTL` — so nothing
about it can be handed back. Quote the median and the range.

Loosening the operation rule to "it can set anything the source records it as
writing" brackets the answer at 33.8% / 52.8%. The half that does not move is
`cannot inject`, which is the half that does not depend on that choice.

### Making the planner profile-aware moves 51 plans, and the share by 5-10 points

Two mechanisms: reject a route before solving it, and prefer a route whose
bindings the profile permits. Neither relaxes an obligation — an `OR` offers
two ways to satisfy one condition and a target usually has more than one way
in, so both are choices the program had already left open.

| | solved plans | unrepresentable | runnable |
|---|---|---|---|
| the corpus this was built against, plain | 494 | 263 = 53.2% | 231 |
| the same, profile-aware | 500 | 244 = **48.8%** | **256** |
| everything else, plain | 229 | 126 = 55.0% | 103 |
| the same, profile-aware | 236 | 107 = **45.3%** | **129** |

*Runnable* — solved **and** representable — is the figure to watch, because
the denominator moves slightly: the profile-aware pass also settles six or
seven plans the plain one leaves open, by taking the other branch of an `OR`.
It changed 4 of those 29 programs and 8 of the 17 elsewhere, and made none
worse.

Where it does nothing it does nothing for a reason worth knowing: on the deep
CICS programs the operation that cannot be replayed sits in the mainline, so
*every* route needs it and there is no other way in to prefer. Route
preference cannot rescue a program whose entry point is the problem. The gain
is larger off-corpus than on it, which is the check to repeat after any
change here.

**The cheap prefilter agreed with the full solve on every route the proxy
refused** — 403 refusals, none of them wrong. It is not exact in general: a
hand-written profile listing two variables and one operation produced 2 false
refusals out of 26 targets, both because the solve met the obligation by
reaching a write that establishes the value rather than by binding the
producer `precheck` objected to. So the filter skips and orders, and when
*every* route is refused the base route is derived anyway and the finished
plan gives the answer. A filter that decides what gets tested has to be wrong
in the harmless direction.

**A gap in the contract, found by measuring rather than by reading it.**
188 of the 819 plans carry an outcome selected by a *discriminator* — "this
`READ` returns not-found only while the create flag is off" — and `Capability`
has no way to say whether the harness can match on program state. A harness
whose mock is a plain ordered list will deliver those in order and ignore the
condition. They are counted in `notes` rather than refused, since refusing
them would assume an answer the profile does not give.

## Coverage

`frameladder <program> coverage --branches` measures what a whole plan set
exercises. Branches are counted **by direction**, since taking an `IF` only
one way is half a branch:

| program | paragraphs | directions |
|---|---|---|
| COACTUPC (4,236 lines) | 97% | **48.8%** |
| COCRDLIC | 100% | 86.7% |
| COCRDUPC | 100% | 75.6% |
| COUSR00C | 100% | 71.6% |
| COTRN02C | 100% | 66.2% |

Paragraph coverage saturates almost immediately and is close to useless as a
target. Directions do not, and iterating on the gap has been the most
productive way to find defects in the tool — every gain below came from
fixing a semantic error, not from adding search:

| | branches | directions |
|---|---|---|
| one plan per paragraph | 291 | 49.7% |
| plans aimed at each decision *direction* | 291 | 62.4% |
| condition-name values parsed with quoted literals | 291 | 63.2% |
| `WHEN` arms given their subject; entry paragraph planable | 291 | 65.5% |
| `EVALUATE` first-match semantics | 291 | 66.8% |
| **`COPY … REPLACING` expanded** | **401** | 56.1% |
| **figurative `VALUE`s read as values** | 401 | **48.8%** |

The last two *lower* the number and are the two I trust most. Expanding
`COPY` revealed 110 branches that were never being counted — the numerator
rose (389 → 450) while the denominator rose further, so 66.8% had been
measured against a program two-thirds the size of the real one. Reading
`VALUE LOW-VALUES` as `\x00` rather than as the ten-letter string stopped
conditions matching that never should have.

This is the recurring shape of the whole exercise: **almost every correctness
fix moved coverage down, and every one of them was right.** A coverage number
is only as honest as the semantics underneath it, which is why
`conformance/` runs against a real compiler after each change — still
20/20 identical.

That last one is the shape of most of them. `EVALUATE` takes the *first*
matching arm, so reaching arm N means arms 1..N−1 all failed. Without that
obligation a long `EVALUATE` looks satisfiable arm-by-arm and only its first
arm is ever taken — 76 branches in one paragraph of COACTUPC. Adding it
naively made things *worse* (54%), because the negations bound before the
arm's own condition and consumed the slots it needed; settling the arm's own
condition first is what made it pay.

Two mechanisms measured at ~zero and are recorded as such: divergence
families add 252 runs for **+1 direction** (they vary values while preserving
reachability, so they take the same paths — they are for parity probing, not
coverage), and a warm learned dictionary adds **+1** (it confirms values the
deterministic chooser already picks).

**What the number does not include.** `COPY ... REPLACING` is not expanded, so
a paragraph built from 39 replaced copies contributes only the branches
written inline. The denominator is therefore understated wherever that idiom
is used, and real coverage of those programs is lower than reported.

## Runbook: synthetic data for a migration you have already built

The common situation. The COBOL compiles, its externals are mocked, a Java
program has been generated — and there is nothing to *run* either side on.
That is what this section is for. It assumes you have the COBOL source and
its copybooks and nothing else from this repository.

### What you get, and in what shape

One command per target produces a test case as JSON:

```bash
frameladder PROG.cbl --copybooks ./cpy --json plan 3000-VALIDATE > tc.json
```

Four fields matter, and they map onto the three things a test needs.

| field | what it is | drive it into |
|---|---|---|
| `input_state` | program inputs: `{"FIELD": value}`, keys upper-case | the entry state on both sides |
| `stub_plan` | `{op_key: [{when, set, seq}, …]}` — what each external operation returns, **in order** | your mocks |
| `terminals` | `{op_key: {field: value}}` — what it returns once the planned outcomes run out | your mocks' fallback |
| `open` | obligations it could **not** solve | read this before trusting the case |

`op_key` is the operation identity, and it is stable across both sides:
`READ:ACCTFILE-FILE`, `OPEN-INPUT:ACCTFILE-FILE`, `CALL:CBLTDLI`,
`EXEC:SQL:SELECT`, `EXEC:CICS:READ`. Mode is part of it — opening a missing
file for input fails where opening it for output creates it — so key your
mocks on the same string and the two sides stay aligned.

The sequence is not decoration. A file read returns a record, then another,
then end-of-file; `seq` carries that order and `terminals` says how it ends.
A mock that returns one fixed status describes a file that never ends, and
the run will loop instead of finishing.

`flat_state` is a convenience view — every binding as one map, first outcome
only. Use it for a quick smoke test; use `stub_plan` for anything real,
because a flat map cannot express a sequence.

**Always check `open` and `solved`.** A plan with unmet obligations is still
useful — it says exactly what it could not arrange — but it is not a test
case yet. `sweep` does all targets at once and reports which ones verified.

### The part that is specific to parity

A binding is **forced** when the program's logic fixes the value, and **free**
when it only fixed a relationship (`A = B`, `A NOT = B`, `A > B`). Only free
slots may be varied — vary a forced one and you change which path runs, so
the test stops reaching its target and proves nothing.

That distinction is what makes divergence probing sound, and `family` spends
it:

```bash
frameladder PROG.cbl --copybooks ./cpy --json family 3000-VALIDATE
```

Each member varies **one** free slot, so a failure is attributable to one
value, and the set is capped (12 by default) so it stays linear in the
number of slots rather than exponential.

Which categories you actually get depends on the slot: its PIC decides
whether the numeric or the alphanumeric list applies, and the *operator*
decides whether ordering-sensitive ones apply at all. A plan with ten free
text slots and no ordering constraint yields ten `spaces` variants and
nothing more exotic — that is the common case, and it is worth knowing
before you go looking for the interesting ones. The categories are chosen
because real ports get them wrong:

- **truncation** — COBOL truncates on both kinds of `MOVE` and in opposite
  directions. Alphanumeric is left-aligned, so the tail is lost; numeric
  aligns on the decimal point, so `MOVE 12345 TO PIC 9(2)` leaves **45**. A
  Java port that models a field as `String` or as `int` loses exactly one of
  those, silently.
- **collation** — z/OS is EBCDIC and your target is ASCII, and they disagree
  on ordering for exactly three class pairs: digit/upper, digit/lower,
  upper/lower. An ordering constraint witnessed by two values from the same
  class holds on both platforms and proves nothing; one witnessed *across* a
  class boundary flips. Verified against GnuCOBOL under both sequences, not
  assumed. **Only emitted for `<`/`>`/`<=`/`>=` on a text field** — if your
  program compares such fields for ordering, this is the highest-value
  family in the list; if it does not, you will never see one.
- **figurative constants** — `SPACES`, `LOW-VALUES` and `HIGH-VALUES` are
  three distinct states that a port usually collapses into one.
- **width and sign** — a value one byte too long, a signed field at its
  negative maximum, minus zero (equal arithmetically, different bytes).

If you only take one thing from this section: truncation and collation are
where a generated Java program actually diverges, and both cost nothing to
generate once a plan exists. Truncation you can also probe directly without
`family` — take any forced binding, widen the value past the receiving
field's PIC, and check both sides agree on what survives.

### What to expect

Measured on 55 programs, and the split is sharp:

| | branch directions covered |
|---|---|
| batch / file-driven | 88–100% |
| CICS / screen / commarea-driven | 6–70% |

Batch programs are the tool's strong case: the entry state plus the stub
sequence really do determine the path. Long CICS transactions are the weak
one, because a plan must survive the program's own writes all the way to the
target and over a deep chain it often does not. Expect to hand the stubborn
targets to an agent (see [`AGENT.md`](AGENT.md)) rather than to get them for
free.

### Things that will bite, in the order they will bite you

1. **Pass `--copybooks` explicitly.** Automatic discovery only looks beside
   the source and one directory up. On a deeper tree it silently finds
   nothing, and a field with no copybook has no PIC — so no width, no sign,
   no 88-levels, and no candidate values. It does not error; coverage is
   just quietly worse. This is the most common silent failure.
2. **Runtime scales with decisions times program size.** Roughly one branch
   per ten lines, `coverage --branches` derives a plan per *direction*, and
   each plan is run in three I/O worlds — so the work is quadratic in the
   source, not linear. Measured on a 32,325-line monolith assembled out of
   this corpus (1,288 paragraphs, 3,401 branches, 73 copybooks): the branch
   sweep gets through **0.42 s per direction**, so its 6,802 directions are
   about 48 minutes before the sampling and paragraph stages start at all.

   `--sample 0 --overlays 0` is **not** the lever, and this file used to say
   it was. On the two corpora it costs 4.0 and 2.1 pooled points
   respectively to save 23% of the runtime; on the 32,325-line program it changes nothing
   at all, because the budget is exhausted inside the branch loop and the
   sampling stage is never reached. What to run instead, in this order:

   | on 32,325 lines | wall | directions |
   |---|---|---|
   | `coverage --lift-only --lift 600` | **22 s** | 397/6802 = 5.8% |
   | `coverage --sample 150 --lift 600` (no `--branches`) | 346 s | 410/6802 = 6.0% |
   | `coverage --branches --lift 600 --time-budget 420` | 428 s | 82/6802 = 1.2% |

   The frontier search is the whole first look and it costs seconds. Reach
   for `--branches` when it has saturated, and give it `--time-budget
   SECONDS --work-list FILE` so it stops rather than disappears; the next
   run reads that file back through `--capability` and continues, skipping
   both what was covered and what was already attempted. Peak memory was
   103 MB in every case — size is not the problem, time is.

3. **Read `step_capped_runs` before reading the percentage.** A run is
   capped at `MAX_STEPS = 20,000` statements *for the whole program*, and
   that constant does not scale with the source. On the 32,325-line program
   30% of runs ended on the cap and only **157 of 1,288 paragraphs were
   entered by any run at all** — so the ceiling on coverage there is a
   constant in `interpreter.py`, not the planner, and no amount of
   `--routes`, `--sample` or patience moves it. On a 4,236-line program the
   same figure is zero, which is why it has not mattered until now.
4. **Constructs that are not modelled**, so anything gated behind them will
   not be planned: `SEARCH`/`SEARCH ALL`, `REDEFINES` aliasing, `OCCURS`
   indexing (subscripts are flattened — `T(1)` and `T(2)` are one cell),
   `INSPECT`, `SORT`/`MERGE` with `INPUT`/`OUTPUT PROCEDURE` (no call edges,
   so the procedures look unreachable), and nested programs (`LINKAGE
   SECTION` is parsed as a paragraph). `python3 -m conformance.microdiff`
   prints the current list, measured against GnuCOBOL.
5. **Record layout is a module, not a command.** `layout.py` gives byte
   offsets and exact lengths (19/19 against GnuCOBOL) if you need to write
   real fixed-width data files rather than field maps. Import it.

### First twenty minutes

```bash
frameladder PROG.cbl --copybooks ./cpy frames          # does it parse; how deep
frameladder PROG.cbl --copybooks ./cpy --json sweep    # every target, planned and verified
frameladder PROG.cbl --copybooks ./cpy crossroads TARGET  # what that route needs from outside
python3 -m conformance.microdiff                       # which constructs are still wrong
```

`frames` tells you it read the program. `sweep` tells you how much of it is
plannable, and is the one to run first on anything unfamiliar. `crossroads`
takes a target and tells you which external operations you must control to
reach it — exactly the list your mocks have to satisfy.

## Agent-assisted

The derivation is deterministic and needs no model. Where it runs out — the
shortest chain skips the set-up, a value has to *mean* something, a run loops —
a coding agent takes over. [`AGENT.md`](AGENT.md) is the protocol: the only
static input, with source and call trace passed dynamically.

The tool's job is to make the handover cheap. A failed `verify` does not say
"false"; it says which frame was not entered, which guards went the wrong way,
and what the values actually were:

```
NOT REACHED   0000-MAIN -> 9700-CHECK-CHANGE-IN-REC-EXIT
of which      0000-MAIN -> 2000-DECIDE-ACTION -> 9600-WRITE-PROCESSING
first frame not entered: 9700-CHECK-CHANGE-IN-REC-EXIT
```

That diagnosis — the chain went straight to the EXIT and never entered the
frame that gates it — turns into one `--via` and a reached target.

## Commands

```bash
frameladder PROGRAM [--copybooks DIR] [--entry PARA] [--work-dir DIR] [--json] CMD
```

| | |
|---|---|
| `frames` | reachable paragraphs, ranked by depth and guard weight |
| `trace TARGET [--via A,B]` | the call chain and every obligation on it |
| `plan TARGET` | bindings, rendezvous couplings, open obligations |
| `verify TARGET` | run it; on failure, say exactly where and why |
| `explain FRAME --variables A,B --source` | one frame, with provenance |
| `family TARGET` | many tests reaching one target, differing only where free |
| `sweep` | plan and verify every target |
| `replay TARGET` | the complete ordered outcome series, terminal included, and every value the harness would have had to drop |
| `represent` | which plans a stated harness could run, and why the rest could not |
| `bind` / `note` / `resume` | the journal, so a loop survives a restart |

`--capability FILE` states what will run the plans; without one nothing is
assumed and no plan is refused. `--proxy` derives a stand-in from the source
and labels every figure it produces as one.

## What it models

Real COBOL, not a subset that avoids the hard parts:

- **`ALTER … TO PROCEED TO`** — rewrites another paragraph's `GO TO` at run
  time. Without it a dispatcher-style program looks almost entirely
  unreachable.
- **`PERFORM A THRU B`** — runs the whole range, fall-through included.
- **Fall-through**, guarded by the negation of every earlier escape: reaching
  anything at line N means no earlier `GO TO` fired.
- **`EVALUATE TRUE`** — each `WHEN` arm is a condition, not a value.
- **Relational words** in all their spellings: `EQUAL`, `NOT GREATER THAN`,
  `IS NOT EQUAL TO`.
- **Abbreviated relations** — `IF WS-RC = '00' OR '04'` means the subject
  twice, and reading the second as a condition-name is silently wrong.
- **`ELSE` as negation**, not inheritance.
- **Level-88 condition names**, group `MOVE`s, `OCCURS`, `REDEFINES`-adjacent
  layout, and record fields whose copybook was never shipped (associated by
  name, and flagged `inferred` rather than trusted).
- **Stub outcomes as sequences** — a read returns records and *then*
  end-of-file. Discriminated by the literals set before the call, so two
  invocations of one subprogram are told apart.

## The parser

The repository runs on source handed to it directly, so the COBOL parser lives
here rather than being a dependency. It is checked against pre-parsed
`cobalt` ASTs for every program where both exist:

```
16 programs   paragraph recall 100%   call-edge recall 100%
```

On the largest (COACTUPC, 4,236 lines) it finds 106 call edges where the
reference AST has 24 — the source contains 115 call statements, so the
reference is the incomplete one.

## Results

Every reachable paragraph, planned and then verified by running it. Across
**44 programs / 34,005 lines / 922 targets**:

| | |
|---|---|
| plans complete | 869 (94%) |
| verified reached | 718 (78%) |
| per-program reached | median **100%**, min 12%, max 100%, σ 33 |

**Read the spread, not the mean.** A single aggregate hides that this works
completely on most programs and barely at all on a few. The same is true of
every ratio here: "56% of bindings are free" is really *median 70%, range
0–100%, σ 32*. These are not properties of COBOL; they are properties of this
corpus.

The reached figure was 96% before the interpreter was checked against a real
compiler, and 96% was wrong — see below.

| program | lines | targets | reached |
|---|---|---|---|
| COACTUPC | 4,236 | 84 | 84 |
| COCRDLIC | 1,459 | 38 | 38 |
| COCRDUPC | 1,560 | 44 | 44 |
| CBSTM03A | 924 | 24 | 17 |
| CBACT01C | 430 | 16 | 3 |

CBSTM03A is an `ALTER`-driven dispatcher that re-enters one paragraph with a
different selector each pass. CBACT01C is the honest low score: every path runs
through a file-open whose failure abends the program, and the ladder does not
yet lift "survive the paragraph performed before this one" as an obligation.
See *Limits*.

## Checked against a real compiler

Everything above rests on the built-in interpreter, which shares its condition
parser and control-flow rules with the planner. If those rules are wrong, plan
and verification are wrong *the same way* and agree with each other — so
agreement proves nothing.

`conformance/differential.py` breaks the circle. It instruments every
paragraph with a marker, compiles with GnuCOBOL, runs, and compares the real
execution against the interpreter's prediction.

```
20/20 runnable programs traced identically
```

`conformance/plan_check.py` goes further and tests the claim that actually
matters — that a *generated plan* reaches its target in GnuCOBOL, not just
that default runs agree. It injects the plan's entry state as MOVE statements,
compiles, and looks for the target:

| | |
|---|---|
| interpreter says REACHED, GnuCOBOL agrees | **21** |
| interpreter says REACHED, GnuCOBOL does not | 4 |
| interpreter says not reached, GnuCOBOL reaches it | 0 |

All four disagreements are plans that also require outcomes from external
operations, which entry-state injection cannot supply. Among plans whose
requirements *can* be injected, agreement is 21/21.

13 synthetic cases covering the constructs the ladder depends on (`ELSE`,
`EVALUATE TRUE`, `PERFORM THRU`, `ALTER`, fall-through, abbreviated relations,
level-88s, relational words) and 7 real CardDemo batch programs.

It found four real bugs, none of which the self-consistent tests could have:

1. **Statements directly under `PROCEDURE DIVISION`, before any label, were
   silently dropped.** That is where the program *starts*, so the entry point
   was wrong for every program in the CBACT/CBTRN family and the first named
   paragraph was mistaken for the mainline.
2. **`CALL 'CEE3ABD'` was treated as returning.** It is the Language
   Environment abend service and does not return. Because the interpreter ran
   on past it, programs that should have stopped after four paragraphs appeared
   to reach everything — which is precisely why the reached figure fell from
   96% to 76% once this was fixed. The 96% was an artifact.
3. **`OPEN INPUT ACCTFILE` keyed as `OPEN:INPUT`**, collapsing every open in a
   program to one operation. The mode belongs in the operation's identity:
   opening a missing file for input fails where opening it for output creates
   it.
4. **`ALTER` targets must contain nothing but their `GO TO`** — a constraint
   the compiler enforces and the instrumenter has to respect.

`plan` reporting open obligations while `verify` reports REACHED is normal —
`solved` is deliberately conservative, and some obligations gate nothing.
Trust `verify`.

## What this corpus is, and is not

Most of it is **AWS CardDemo — a teaching sample**. It is small, recent,
written in one house style, and free of the things that make real estates
hard: forty years of accretion, 20k-line programs, deep copybook hierarchies,
`GO TO DEPENDING ON`, `SORT`/`MERGE`, nested programs, dynamic `CALL` on a
variable. The widened corpus adds DB2 programs and one scrambled
production-derived program (3,215 lines, 117 paragraphs), but 44 programs and
34k lines is still three or four orders of magnitude smaller than the estates
this is meant for.

So treat every number here as a measurement of this corpus, not an estimate
for yours. Two things are worth knowing about the bias:

- **The variance is larger than the differences being claimed.** Free-binding
  share runs 0–100% (σ 32); per-program reachability runs 12–100% (σ 33). Any
  headline mean is averaging over programs that behave nothing like each other.
- **The size bias has a known direction.** The six largest programs average
  79% free bindings against 55% for the rest, so if real programs are bigger,
  the free-slot share — the thing the divergence work spends — is more likely
  understated here than overstated. That is an argument for the approach, not
  evidence for the number.

## Limits

Stated rather than hidden; each is reported in the output when it bites.

- **A variable that must hold different values at different moments.** Handled
  when the program writes it (the entry state supplies the first value and the
  program produces the rest) and proved impossible when it does not. Still only
  partial for a dispatcher selector walking TRNXFILE → READTRNX → XREFFILE,
  where a chain re-enters the dispatcher several times.
- **Surviving an earlier sibling call is not yet an obligation.** Reaching a
  frame requires that the paragraphs performed before it did not abend. The
  obligation is derivable — a prototype lifted exactly the right condition on
  CBACT01C — but the binding layer attributes the status to the wrong operation
  and over-produces outcome sequences, so it is not in the shipped version.
  This is the single biggest remaining gap and the whole of CBACT01C's 3/16.
- **Ordering constraints are solved pairwise, not as a system.** Several
  coupled orderings over the same values would need a topological assignment;
  each is currently witnessed on its own.
- **`--terminal` is per operation, not per discriminator**, so a program
  routing opens and reads through one subprogram cannot have both a succeeding
  open and an ending read.
- **Subscripts are flattened**: `WS-TAB(I)` and `WS-TAB` are one cell, so
  table-indexed plans are verified loosely.
- **`COMPUTE` is not evaluated.**
- Verification is by the built-in interpreter, not a compiled binary.

## Tests

```bash
python3 -m pytest tests/test_frameladder.py -q     # 94 unit tests, self-contained
python3 tests/parser_agreement.py                  # parser vs reference ASTs
```
