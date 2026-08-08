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

**Infeasibility proofs.** When a variable the program *never writes* is
required to hold two different values, that is not a gap in the search — it is
a proof that the chain is dead, delivered in O(1). On COACTVWC the tool reports
`WS-INPUT-FLAG must be '0' and also '1', and nothing in the program writes it`;
the field is declared on line 50 and never mentioned again.

Together these took the corpus from 197 unresolved obligations to 41 — of which
40 *are* infeasibility proofs.

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
| `bind` / `note` / `resume` | the journal, so a loop survives a restart |

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
python3 -m pytest tests/test_frameladder.py -q     # 82 unit tests, self-contained
python3 tests/parser_agreement.py                  # parser vs reference ASTs
```
