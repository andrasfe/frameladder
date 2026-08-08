# AGENTS.md

Guidance for an agent working **on** this repository.

Not to be confused with [`AGENT.md`](AGENT.md), which is the protocol for an
agent **using** the tool against a COBOL program. That one is a product
surface and is read at runtime; this one is about developing the thing.

## What this is

`frameladder` derives program inputs that reach a deep target in a COBOL
program, by starting at the target and lifting obligations **outwards** along
the call chain. It is used for coverage and, increasingly, for generating
synthetic test data to validate parity in mainframe migrations.

Python 3.9+, standard library only. No network, no model, no services. That
is a deliberate property, not an accident of youth — see *Invariants*.

## Commands

```bash
python3 -m pytest tests/test_frameladder.py -q      # 76 unit tests, seconds
python3 tests/parser_agreement.py                    # parser vs reference ASTs
python3 -m conformance.differential  <programs>      # interpreter vs GnuCOBOL
python3 -m conformance.plan_check    <programs>      # do plans reach, in GnuCOBOL?
python3 -m frameladder.cli <program.cbl> sweep       # plan+verify every target
```

`cobc` (GnuCOBOL) must be on PATH for the conformance harnesses. Everything
else runs anywhere.

## Architecture

Reading order, which is also the dependency order:

| module | responsibility |
|---|---|
| `cobol.py` | parse source into paragraphs, statements and a data model. Ships its own parser rather than depending on one |
| `ir.py` | `Term`, `Atom`, `Producer`, `Binding`, `Plan` — the algebra everything else speaks |
| `conditions.py` | COBOL conditions to disjunctive normal form |
| `graph.py` | call graph, guarded call sites, chains, execution order |
| `provenance.py` | who writes what, under which guards, and which knob really sets it |
| `liveness.py` | live-in sets: what a paragraph reads before writing |
| `ladder.py` | the solver. Lifts obligations outwards and binds knobs |
| `interpreter.py` | executes the subset, to verify a plan and say where it failed |
| `divergence.py` | spends free values on exposing migration differences |
| `heuristics.py` | evidence first, naming convention a distant second |
| `faults.py` | platform status vocabularies (file status, SQLCODE, CICS RESP) |
| `layout.py` | physical record layout — offsets and byte lengths |
| `dependencies.py` | what each frame commits you to in the outside world |
| `witness.py` | verified states, kept and reused |
| `cli.py` | the toolbox an agent drives |

## Invariants

Break these and the tool stops being trustworthy rather than merely wrong.

**Determinism.** The same program and target produce the same plan, every
run. This is why there is no model call in the derivation path: judgment
enters through `bind`, is written to the journal, and is data thereafter.

**Free vs forced.** A binding is *free* when the constraint fixed only a
relationship, and *forced* when it fixed the value. Only free slots may be
touched by a heuristic, a preference, or a divergence category — so no
convenience can ever contradict something the program requires.

**Evidence outranks convention.** A literal the program compares a field
against is a fact about this source. A name table is a guess about how other
people name things; it is opt-in (`--conventions`), ships as
`packs/en-US.json`, and measured at 1% of values and zero targets.

**Platform vocabulary is not a naming guess.** File status codes, SQLCODE,
CICS `DFHRESP` are fixed the way HTTP status codes are fixed. They are
allowed. A field is only offered one when the *source* puts it in that
channel — `FILE STATUS IS` in the SELECT, a `RESP` operand — never because
its name looks status-ish.

**Computed, not stored.** The whole index for a 4,236-line program builds in
81 ms. A persisted graph would buy nothing and cost a second source of truth.

## How to work here

This has been the productive discipline, and it is worth keeping:

**A settled obligation must be bound or reported, never neither.** The
worst defect found so far was silent: when the entry state could not carry a
value, `build_plan` wrote a note and marked the obligation settled, so plans
reported `solved` while binding nothing. Coverage looked fine because other
paths found those directions anyway - only an audit of `solved` plans that
bound no state exposed it. If a branch settles an obligation, it either
produced a binding or it appended to `open_obligations`. There is no third
option, and a plan that claims to be solved is a claim someone will rely on.

**Measure before building.** Several plausible features measured at zero and
were not built: name-based sibling transfer (0% once guarded), prefix
inheritance of witnesses (0%, because the chooser was already deterministic).
Both are recorded in the README, because *"we tried the clever thing and the
boring thing won"* is the useful part.

**Measure spread, not means.** Free-binding share is *median 70%, range
0–100%, σ 32*. Per-program reachability is *median 100%, min 12%, σ 33*. Any
single mean averages over programs that behave nothing like each other. Quote
median and range.

**Validate against the compiler, not against yourself.** The interpreter
shares its condition parser with the planner, so agreement between them
proves nothing. `conformance/` exists to break that circle, and it has found
real defects every time it was pointed somewhere new — a dropped mainline,
`CALL 'CEE3ABD'` treated as returning, `OPEN:INPUT` collapsing every open.

**Expect the bug to be yours.** Almost every "the program never says X" turned
out to be "the parser was not listening": `VALUE` clauses unread, `DFHRESP()`
parsed as an array, `NOT=` yielding a variable called `X NOT`, `USAGE`
ignored entirely. Check the source before adding inference.

**Report the number that moved, and the one that did not.** If a change
leaves the corpus figure flat, say so and say why it cannot show up there.

## Known traps

- **COBOL falls through.** A paragraph that does not end in `GO TO`/`GOBACK`
  runs into the next one. Test fixtures that ignore this produce confusing
  failures; end fixture paragraphs with an explicit `GO TO`.
- **`bool` is an `int` in Python.** `witness('!=', True)` returned `2` until
  guarded. Anything arithmetic on a value needs `not isinstance(v, bool)`.
- **`FILLER` occupies bytes but cannot be referenced.** It is excluded from
  `declared` and included in the layout, under a synthetic unique name.
- **`ALTER` targets must contain only their `GO TO`.** The compiler rejects
  anything else, so instrumentation has to skip them.
- **Order is meaning.** Passing a `set` where a ranked list is expected
  silently re-sorts by `repr` — that is how `'02'` beat end-of-file 174 times.
- **Copybooks: read what is `COPY`ed.** Loading the directory gave CBACT04C
  2,640 fields instead of 129, inflating the `declared` set that live-in
  filtering and record association depend on.

## The corpus, and what it is worth

44 programs, 34,005 lines, mostly **AWS CardDemo — a teaching sample**. It is
small, recent, one house style, and free of what makes real estates hard:
20k-line programs, `GO TO DEPENDING ON`, `SORT`/`MERGE`, nested programs,
dynamic `CALL`. There is one scrambled production-derived program and a few
DB2 ones.

Treat every figure as a measurement of this corpus, not an estimate for
anyone's estate. Where a bias direction is knowable, state it: the six
largest programs average 79% free bindings against 55% for the rest, so the
free-slot share is more likely understated here than overstated.

## Derivation is not the whole answer

The ladder derives; it does not sample. Those reach different things, and the
gap is not small: on COACTUPC derived plans alone reach 61.2% of directions
and literal sampling alone reaches 57.0%, but their **union is 69.8%** — each
finds roughly a hundred directions the other never does.

So `coverage --sample N` is a first-class part of the answer rather than a
fallback. Derivation gets past guards that sampling would have to be lucky to
hit; sampling reaches statements whose obligations the ladder cannot lift at
all (unmodelled `COMPUTE`, `SEARCH` arms, reference modification). The
directed-symbolic-execution literature reports the same shape, which is some
comfort that this is a property of the problem and not of this code.

Sampling saturates early — 100 draws gets within a point of 1,500 — so the
default is small on purpose. Ranking it above `--routes` retries would be the
wrong lesson: what makes the union work is that the two are uncorrelated.

## Reporting honestly

Paragraph coverage is close to free on this corpus: an empty state already
enters 93 of COACTUPC's 99 paragraphs, because most are reached by
fall-through rather than by a guard. **96/99 is not a result.** Direction
coverage is the number that measures anything, and it is the one to quote.

## Where coverage stands

Branch directions, whole CardDemo corpus, `coverage --branches --sample 150`:
**29 programs, median 79.5%, range 7.1-97.6%.** Quote the median and the
range; the mean hides CBEXPORT.

Two outliers are diagnosed and worth taking first, because both are single
defects rather than search failures:

- **CBEXPORT 7.1%** - `NOT` in `conditions.py` distributes over the whole
  expression instead of binding to its operand, so `NOT (A OR (B AND C))`
  is mis-normalised. It sits in this program's main read loop, which is why
  one bug costs the entire file. CBIMPORT has the same shape.
- **CBACT01C 50%, CBTRN03C 57.8%** - the survival gap in item 1 below.

## Open work, in the order I would take it

0. **`NOT` precedence in `conditions.py`.** One defect, one program at 7%.
   Cheapest real point on the board.
1. **Surviving an earlier sibling call is not yet an obligation.** Reaching a
   frame requires that paragraphs performed before it did not abend. A
   prototype lifted exactly the right condition on CBACT01C, but the binding
   layer misattributed the status and over-produced outcome sequences, so it
   was reverted rather than shipped. Biggest single gap.
2. **`--terminal` is per operation, not per invocation** — a program routing
   opens and reads through one subprogram cannot have both a succeeding open
   and an ending read.
3. **No forward reasoning to an output.** A test that reaches a divergent
   statement but whose effect never reaches a sink detects nothing.
   `layout.py` is the groundwork; the reader index does not exist yet.
4. **No data representation model in the interpreter** — it can generate a
   truncation probe but cannot predict the truncation. `ir.holds()` compares
   with Python semantics, which means it agrees with a naive Java port and
   disagrees with z/OS on exactly the classes a parity generator cares about.
