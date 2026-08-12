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
python3 -m pytest tests/test_frameladder.py -q      # 260 unit tests, seconds
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
| `capability.py` | what the harness that will run these plans can inject and replay |
| `replay.py` | the complete ordered outcome series, with every refusal named |
| `represent.py` | which plans a profile could run, and a proxy profile to measure with |
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

**Outcome sequences pay on the fault axis, not the payload axis.** Rotating
record *contents* across a read sequence measured at exactly zero on both
corpora, for two measured reasons: `MAX_LOOP` already breaks an endless read
loop, and only 0-2 fields per program under a record area are ever compared
against a literal, so there is almost no evidence about what a record should
contain. What pays is one operation returning a non-zero status at *one
point* in the series and succeeding either side - a fixed world can only
fail the lookup on every record, and then the record that would have been
rejected was never read successfully.

Stated plainly: the mechanism needs `FILE STATUS IS`, which is 10 of 29
CardDemo programs and **1 of 17** elsewhere, and that one was already at
100%. **It is unproven off-corpus rather than shown to generalise.**

**A budget spent depth-first is a budget spent on one field.** `divergence.
family` took every candidate of the first free slot before looking at the
second, so a twelve-member family covered two slots out of thirteen - the
opposite of the "one factor at a time, linear in the number of slots" its
own docstring promised. Worse, it decided which *categories* existed: each
slot lists boundary values first and its collation pair last, so the one
category that changes control flow rather than data was generated and then
truncated away every single time, on every program, in both corpora.
Breadth-first plus a detection-value ranking fixed both. Check what a
budget actually reaches, not what the code offers.

**Audit this, do not assume it.** Every corpus name in the package is in a
comment or a docstring, citing the program a defect was found in - none is
in executable code, and that is checkable:

```bash
grep -rniE "CARDDEMO|CDEMO-|COACTUPC|GAM0|CBACT01C" frameladder/*.py
```

The subtler failure is code that decides behaviour from a variable's
*name*. There was exactly one, and its own docstring disowned it:
`faults.channel_of` matched a `-RESP` suffix under a comment reading
"deliberately not a naming heuristic", and the unit test asserting it was
named `test_channel_comes_from_the_select_not_the_name`. A field is a CICS
response field because the source wrote `RESP(WS-RC)`, which is evidence.
Removing the heuristic also *found* a field it had missed - `WS-REAS-CD`
does not end in `-RESP`.

**Platform vocabulary is not a naming guess.** File status codes, SQLCODE,
CICS `DFHRESP` and the `DFHAID` attention keys are fixed the way HTTP status
codes are fixed. They are
allowed. A field is only offered one when the *source* puts it in that
channel — `FILE STATUS IS` in the SELECT, a `RESP` operand — never because
its name looks status-ish.

**Computed, not stored.** The whole index for a 4,236-line program builds in
81 ms. A persisted graph would buy nothing and cost a second source of truth.

**A harness limitation may pick between witnesses; it may never decide what is
required.** A capability profile reaches the derivation in exactly two places:
it orders the alternatives of an `OR` so the deliverable one is tried first,
and it chooses between routes. Both are choices the program left open. Nothing
about a profile can relax an obligation, and nothing about it may declare a
target unreachable — `precheck` refuses a *route*, and when every route has
been refused the base one is derived anyway so the finished plan gives the
answer. It agreed with the full solve on all 403 routes it refused under a
profile derived from the source, and produced 2 false refusals out of 26
targets under a hand-written narrow one, which is exactly why it skips and
orders rather than decides. A filter that decides what gets tested has to be
wrong in the harmless direction.

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

**Nothing is pinned, and nothing may be.** `interpreter.assign` used to
return early for any variable present in the entry state, so the program's
own assignments to it were discarded for the whole run. No COBOL construct
models that. It let a failed OPEN run `MOVE 12 TO APPL-RESULT` and the next
line still find `88 APPL-AOK VALUE 0` true - both arms scored in one run no
compiler can produce. Removing it cost roughly a third of the reported
coverage and is not negotiable: an entry state supplies a variable's
*initial* value and the program owns it from then on. A plan whose value is
overwritten before the target needs an obligation about that write, which is
what `blocking_writes` and `establishing_writes` are for - not a plan that
needs the write suppressed.

**Some of the coverage was phantom.** `X(2:8)`, `FUNCTION TRIM(X)` and
`X NOT NUMERIC` all parsed as *variable names*, so the sampler set them
directly and scored the directions they gated - 24 such pseudo-variables
across the corpus. Correcting the parser removed that coverage; correcting
value generation earned most of it back honestly. When a construct is
unparsed, check whether it became a settable name before believing any
number that depends on it.

**Trace feedback pays only if the harness gets *further* than the
interpreter, and here it does not.** The Specter request asked for
re-planning from the compiled program's first missing frame. Built and
measured: frame-rooted search reaches 11.7% of wanted directions against
9.1% entry-rooted on CardDemo, 22.4% against 13.9% elsewhere. But two
ablations gut the claim.

*The frames add no reach.* Seeding on **every paragraph**, with no report at
all, reaches 179/786 off-corpus against the frame-rooted 176. What a report
buys is *which of your own seeds are worth running* - an ordering, not new
ground.

*The premise had no headroom.* Over the seven GnuCOBOL-runnable programs the
interpreter reports **53** chain frames reached and the real compiled run
**13**: the actual program is *shallower*, because it abends on absent
files. A reported frame is only a new resume point if the harness reached
somewhere the interpreter cannot, and on this corpus it never does. On an
estate with real data behind the mocks that may invert - which is precisely
why it is written down as a condition rather than a verdict.

*And it conflicts with targeting only uncovered directions.* Telling the
planner to skip what the harness already covers collapses an entry-rooted
search (168 directions to 36) while a frame-rooted one is unaffected (215 to
212). The directions a shallow search climbs *through* are the ones already
owned; closing them removes its ladder. Requests 1 and 4 of that enhancement
pull against each other, and only a search that starts deep can have both.

**A spot check is not a measurement, and saying "measured at zero" when it
was three programs is worse than saying nothing.** A commit here claimed a
provenance change was "measured at zero on both corpora"; it was checked on
three programs, the largest one timed out and was skipped, and the change
was **-199 directions** - -145 on that program alone. If a claim of zero is
worth making it is worth a sweep, and if the sweep is too slow to run then
the honest report is "not measured".

**Measure before building.** Several plausible features measured at zero and
were not built: name-based sibling transfer (0% once guarded), prefix
inheritance of witnesses (0%, because the chooser was already deterministic).
Both are recorded in the README, because *"we tried the clever thing and the
boring thing won"* is the useful part.

**Measure spread, not means.** Free-binding share is *median 70%, range
0–100%, σ 32*. Per-program reachability is *median 100%, min 12%, σ 33*. Any
single mean averages over programs that behave nothing like each other. Quote
median and range.

**Constructs this corpus does not use are still worth fixing.** `GO TO ...
DEPENDING ON`, `SEARCH`, `PERFORM VARYING ... AFTER` and `EXIT PARAGRAPH`
have zero or one site in CardDemo, so they cost nothing here and everything
on an estate that uses them. `conformance/microdiff` is the place to fix
them, because it measures the language rather than the corpus - which is
the only defence against tuning the tool to one teaching sample.

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
- **A literal can wear a prefix.** `X'0A1B'` is hexadecimal, `Z'..'` is
  null-terminated, `N'..'` is national. Parsed as names they become
  variables nobody writes, so every condition testing one is permanently
  false - which is exactly how CSUTLDTC sat at 50% with ten dead arms.
- **A conditional phrase is a decision, not a suffix.** `READ ... AT END
  <stmts>`, `INVALID KEY`, `ON SIZE ERROR` and their `NOT` forms run their
  body only on that outcome. Parsed as plain siblings the body runs
  unconditionally, so a read loop sets end-of-file on its first pass and
  everything it was written to do is unreachable. That is the shape of
  batch COBOL, not an edge case - it took one program from 12.5% to 100%.
- **Copybooks: read what is `COPY`ed.** Loading the directory gave CBACT04C
  2,640 fields instead of 129, inflating the `declared` set that live-in
  filtering and record association depend on.
- **Reaching a frame is not taking a direction.** A plan built to make one
  decision go one way can enter the paragraph without evaluating it, evaluate
  it the other way, or stop on a limit first. All three were reported as
  successes. Measured over 3,288 directions: 804 verified, 234 took the
  *wrong* direction, 662 never reached the target, 605 never evaluated the
  decision. Of the 2,501 plans that solved cleanly, 32% did what they were
  built to do. Run the plan and check the guard event before calling anything
  a witness — `cli._verify_direction`.
- **A settled obligation must be *emitted*, not merely bound.** The third
  costume of the repository's oldest defect. `IF WS-A = 'A'` guards the
  PERFORM and a later `MOVE 'Z' TO WS-A` makes provenance name a `literal`
  producer, the solver binds the right value against it, and `input_state()`
  filters by producer kind — so the plan reports no open obligation, carries
  the value internally, and ships an entry state without it. Bound, not
  reported, not emitted: pick any two and the plan fails for a reason nothing
  records. The flag is on the *binding* (`Binding.at_entry`), never by
  rewriting the producer kind: kind is half of `slot`, and a second slot for
  one variable stops two obligations from ever colliding. Trying it the blunt
  way changed 61 COACTUPC plans and dropped the very field their target edits.
- **An index shared with another program is not an identity.** Two tools can
  both number the decisions in a paragraph, agree on the paragraph, and mean
  different decisions by the same integer — this tool counts statement
  position, Specter counts per (paragraph, kind). The number is *plausible* on
  both sides, so nothing raises: 1,251 of 1,644 CardDemo targets silently
  pointed at the wrong decision. Join on what the program says (condition
  text, source line), never on what either side counted, and treat a foreign
  index as a hint that is worth *reporting when it disagrees* — see
  `directions.py`. The general form: when an identifier crosses a process
  boundary, either both sides derive it from the shared artifact or it is not
  an identifier.
- **Inserting a dataclass field is an API change.** Adding `aliases` in the
  middle of `Operation` silently redirected every positional construction's
  fourth argument, so `matches_on_state` landed in `aliases` and every lookup
  raised. New fields go last, and `TestOperationAliases` now pins the order.

## Generalisation is checked, not assumed

Every mechanism here was developed against CardDemo, so each one is
re-measured on unrelated source before it is believed: IBM's Global Auto
Mart sample (a different vendor, CICS+BMS+DB2+IMS), CardDemo's own
`app-*` sample applications, and a synthetic AML screener.

That check has earned its keep. The frontier search that took CardDemo from
51% to 71% pooled moved the Global Auto Mart programs by **exactly zero** -
four of the five sat at 2-9% - because every one of them opens with

    IF EIBCALEN = LENGTH OF DFHCOMMAREA ... ELSE EXEC CICS RETURN

and returned on its first statement, so there was no frontier to extend.
CardDemo writes `IF EIBCALEN = 0` instead and never exposed the gate.
Folding `LENGTH OF` to a constant took those four to 41-100%.

The lesson generalises past that one bug: a mechanism measured on one
codebase is measured on one codebase. Run the others before claiming
anything.

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

## Four things that raise coverage, and why they compose

Measured independently and in combination on the whole corpus. They are
listed together because the interaction is the point:

- **A complement value in the sample pool.** The program names the values it
  distinguishes; the complement of that set is the only *other* thing it can
  distinguish. Without one, a field compared only against SPACES has a
  single reachable state and the negative direction of its own comparison
  cannot be sampled into. Evidence-derived, so nothing about it is
  corpus-specific.
- **Every derived plan run in every I/O world.** The plans were already
  right; the harness only ran them in `bare`, where a batch program abends
  at its first OPEN and every later failure path is unreachable.
- **Overlays on the free slots.** A plan pins only the slots its obligations
  reached; the rest take the same default on every run. Two random draws
  over the remainder is the knee -- eight cost four times as much for a
  quarter more.
- **Harvesting `EVALUATE TRUE / WHEN <condition>` arms.** Alone this is
  worth almost nothing. In combination it is worth an order of magnitude
  more, because harvesting the literals is useless until something varies
  them. That is the strongest interaction measured here and the reason to
  distrust any of these numbers taken alone.

**Search bought almost nothing; diagnosis bought everything.** Three
mechanisms were designed, built and measured against this problem, and the
result was consistent enough to be worth writing down:

| mechanism | measured | what it was actually worth |
|---|---|---|
| frontier lifting from a reached state | large | the one search idea that paid |
| branch-distance fitness + conflict learning | +2 directions | localised REDEFINES aliasing |
| CICS transaction state-machine search | +5 directions | localised six semantic defects |

Both near-zero results paid for themselves by pointing at a defect. The
transaction search failed for a reason worth keeping: **distinct commarea
states discovered were 1, 1, 1, 2, 5, 9, 13** across the screen programs,
because the screen data is re-received from the map on every task, so
history does not decide the path. Sequences are a real mechanism and this
corpus barely uses them.

Before building a search, check whether the thing it would search for is
actually being computed correctly. It usually is not.

**Raw budget buys nothing.** 33x the samples and 6x the routes moved the
corpus by 0.16 points for 8x the runtime. When coverage is stuck the answer
is a missing mechanism, not a bigger number.

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
`coverage --branches --lift 600`, two corpora measured separately because
one of them is the corpus this was built against:

| | programs | median | range | pooled |
|---|---|---|---|---|
| CardDemo | 28 | **90.7%** | 57.1-100% | 2525/3288 = **76.8%** |
| everything else | 17 | **84.2%** | 43.9-100% | 1660/1992 = **83.3%** |

**Those are commit `31d3afa`'s figures and the code has not produced them
since.** Re-measured on the same corpora with the same command two commits
later, the first corpus pools **1817/3288 = 55.3%** (median 89.3) and the
second **1636/1992 = 82.1%** (median 84.2). The 199 directions are one hunk:
`b8ff856` gave `Provenance.visible` a base-name fallback, and its own message
records the change as *measured at zero on both corpora*. It is not zero.
Reverting that hunk alone brings the largest program back to 256/858 =
**29.8%** exactly, from 12.9%.

The mechanism is the one the paragraphs below already describe, arriving from
the other side. A qualified BMS input field now finds the `EXEC CICS RECEIVE
MAP` that fills it instead of finding no writer at all, so it stops being an
entry input and becomes a stub output — and a stub output the plan cannot
deliver is an uncovered direction. Whether 55.3% or 61.0% is the honest
number is exactly the open item below; what is not defensible is a table that
describes neither the code nor a stated commit. **Re-measure before quoting,
and say which commit.**

The two CardDemo numbers moved in opposite directions when the byte-level
store landed, and both are right. The **median rose** (88.1 -> 90.7) because
most programs got more accurate. The **pooled figure fell** (71.4 -> 61.0)
because seven large CICS screen programs lost heavily, for one reason,
verified rather than assumed: a BMS output map REDEFINES its input map, the
program clears the output map before sending, and that clear lands on the
bytes the operator's input will occupy. The old field map kept the two
descriptions as separate cells so the input survived a clear that had
already discarded it. `redefines_cleared_through_alias` fails on the old
store and passes now.

Delivering terminal input at `EXEC CICS RECEIVE ... INTO(a)` recovers this
where the harness supplies the field - COUSR01C went 44.4% -> 97.2%. Where
it does not, the direction is honestly unreachable rather than falsely
covered, and **that is the largest single piece of open work in the repo.**

"Everything else" is IBM's Global Auto Mart sample, CardDemo's own `app-*`
applications, and a synthetic AML screener - 17 programs by three
unrelated authors.

**The pooled figure is higher off-corpus than on it**, which is the result
to check after any change here. It has not always been true: before the
`LENGTH OF` and `AT END` fixes the same set pooled 76.2% with a floor of
1.9%. Both defects were invisible on CardDemo.

Without `--lift`, CardDemo pools 51.2% - the frontier search is most of the
difference and all of it on the deep programs.

That is a third lower than this file claimed a day earlier, and the drop is
the point. The old figure was measuring an artefact: every variable in the
entry state was frozen for the whole run (see *Nothing is pinned* below), so
the sampler ran each program with exactly the fields that gate its branches
turned into constants. GnuCOBOL, driven with the tool's own states, confirmed
only 61% of the directions that number claimed.

Quote the pooled figure alongside the median. The median flatters: the
failures are concentrated in the large CICS programs, where a plan has to
survive the program's own writes all the way to the target and mostly does
not. COACTUPC is at 6.4% and that is an honest measurement of the planner,
not a bug. Quote the median and the
range.

The lowest is CORPT00C at 72.5%. It dipped to 58.8% when the interpreter
learned `FUNCTION CURRENT-DATE` -- the program does `ADD 1 TO
WS-CURDATE-MONTH` and then tests `> 12`, reachable every December and
unreachable against a fixed instant. It recovered without anyone
special-casing dates. Two of its directions still need open item 2.

**The residual is over-reported success, not dead code.** Of the directions
still missing at the previous measurement, the tool proved 7 infeasible and
112 had a plan claiming `solved` that did not deliver. Before believing a
program has hit its ceiling, check `contested`. CSUTLDTC, which sat at 50% for most of this
work, is at 100% -- its ten dead EVALUATE arms were all testing 88-levels
whose VALUE was a hexadecimal literal the parser read as a variable name.

## Open work, in the order I would take it

0. **Temporal, route-sensitive provenance: which write reaches *this* read on
   *this* route?** The single highest-value item in the repository. It gates
   two finished branches and the largest disposition on both corpora.

   The diagnosis, measured rather than argued. For every plan that fails to
   reach its target - 662 of 3,288 here, 54% of the RCO100B funnel - ask how
   far along its own chain it got. Nearly all of it: the modal shapes are
   2/3, 1/2, 3/4. The plan walks the route and misses the **last hop**, so
   the failure sits in the guard that admits it to the target. Traced to the
   end on one case: the plan binds a field at entry, a conditional `SET ...
   TO LOW-VALUES` in the mainline resets it before the read, and the
   88-level condition admitting the last hop then goes the wrong way.

   Both branches fail the same way when the missing writes are modelled -
   correctness up, witnesses down - because negating the guard on such a
   write is often unsatisfiable on the route being taken:

   | | verified | late failures removed |
   |---|---:|---:|
   | `blocking-writes-set` | 804 -> 703 | 626 |
   | `initialize-provenance` | 804 -> 796 | 584 |

   Neither lands until the solver can ask whether a write can actually run
   between the binding and the read *on this route*. Do that and both branches
   become pure gain. `writes_to` is a global lookup; `visible(var, at)` orders
   writers but does not filter them, and `execution_order` is documented as a
   preference precisely because an `ALTER`ed dispatcher makes any static order
   a guess.

   The cost of not having it is measured. Modelling `INITIALIZE` as a real
   write - which is plainly correct, since the interpreter has always executed
   it and the two models disagreeing about one program is the thing this file
   warns about - converts 584 late silent failures into early honest ones and
   *also* turns 99 plans that verifiably work into unsolved obligations, so
   `verified` falls 804 -> 697. On COACTUPC the clear-down of
   `CDEMO-FROM-PROGRAM` is guarded by the same condition the target direction
   needs, so steering around it demands `EIBCALEN != 0` while reaching the
   branch demands `EIBCALEN = 0`. A real contradiction on that route - and the
   interpreter takes the direction anyway, because the obligation being
   steered around was not load-bearing for that decision.

   The work is on the `initialize-provenance` branch with its numbers. It
   lands when `verified` is >= 804 with it applied, and not before: coverage
   is the product, and a change that diagnoses better while producing fewer
   witnesses is not yet an improvement.

0b. **The rest of the RCO100B list, with local prevalence measured.** Each was
   surveyed on this corpus so the next person starts from evidence rather
   than re-deriving it. Counts are CardDemo + the four side corpora, 41
   programs.

   - **Computation inversion** (their item 7). 79 `COMPUTE`, 92 `ADD`, 19
     `SUBTRACT`, 1 `DIVIDE`, and **32 IF conditions naming a field a COMPUTE
     writes**. Arithmetic writers are indexed with the statement as their
     source, but the producer walk only follows `MOVE`, so an obligation on a
     computed field falls through to an `unknown` producer and is bound
     directly in the entry state - which the program then overwrites with the
     computed value. The hard part is not the producer: it is that inverting
     needs the *obligation* transformed, `X = 100` through `COMPUTE X = Y + 5`
     becoming `Y = 95`, and that is the solver's algebra rather than a lookup.
     Do it narrowly - integer fields, literal operand, no scaling - or the
     truncation and overflow rules make it wrong in the silent direction.
   - **OCCURS / REDEFINES identity** (their item 8). 64 OCCURS declarations
     and 1,808 REDEFINES here; the runtime store is byte-aware but planner
     provenance still keys on the base name, so `FIELD(1)` and `FIELD(2)` are
     one knob. Related to item 1 in this list.
   - **Precompiled SQL cadence** (their item 11), **replay queues from
     observed chronology** (12), **compiled-feedback lifting** (13). Not
     surveyed; 13 already has its instrument - `directions` reports whether
     the harness reached any frame this interpreter cannot, which is the
     number that decides whether it can pay at all.

1. **REDEFINES is never aliased at runtime** - an upper bound of 382
   directions across 17 programs, the largest untouched item. Needs the
   byte-level store that item 4 also calls for; doing it once brings MOVE
   truncation and real subscripts with it.
2. **The environment is not a planned input.** `FUNCTION CURRENT-DATE` is a
   fixed instant, so every branch that depends on the date being a
   particular month or day is unreachable rather than planned. It is a knob
   like a file status, not a constant. Seeding it blindly into the sampler
   measured at -2 (one more name dilutes every other draw), so it wants
   deriving, not sampling.
3. ~~Surviving an earlier sibling call is not yet an obligation.~~ **Done**
   (`graph.survival_atoms`). The earlier prototype over-produced; this one
   caps the obligations and negates only the innermost conjunct, which was
   the difference. An *un*guarded terminator is reported as a proof of
   unreachability rather than turned into an obligation.
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
