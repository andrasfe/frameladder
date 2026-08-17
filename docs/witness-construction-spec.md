# Witness Construction by Base-and-Spoil: Implementation Spec

A high-level specification for implementing the approach that took pooled
residual reduction from 29.6% to 56.9% on the CardDemo corpus. Written for
an implementing agent working in any codebase that can parse and execute
COBOL deterministically. No code here — contracts, phases, and the lessons
that were paid for. Every rule in this document traces to a measurement.

---

## 1. Purpose

Given a COBOL program, produce **witnesses**: stored, replayable recipes
that demonstrably drive individual branch directions when executed from
program entry. Maximize the number of branch directions holding at least
one witness; for every direction left without one, produce a *named*
reason rather than silence.

## 2. Definitions

- **Direction** — one side of one decision, identified as
  `(paragraph, ordinal, kind, direction)` where ordinal counts decisions
  of that kind within the paragraph and direction is true/false (each WHEN
  arm of an EVALUATE is its own decision).
- **Recipe** — the complete input of one run: entry state (variable →
  value), I/O world, stub outcome series (what each external operation
  returns, in order), terminals. A recipe must be **self-contained**: a
  fresh interpreter given only the stored recipe must reproduce the run.
- **Witness** — a recipe plus a direction its from-entry run demonstrably
  takes. One recipe usually witnesses many directions.
- **First-match chain** — an EVALUATE (or IF cascade) where exactly one
  arm fires per run: the earliest whose condition holds. The dominant hard
  structure in screen programs (cursor positioning, attribute setup).
- **Face** — one failure mode of one field's verdict. A field's validator
  typically produces one pass state and two failure faces (e.g. NOT-OK
  and BLANK), each with its own arm in downstream chains.
- **Pseudo-conversation** — CICS task cycles. One *recipe* may span
  several cycles if the interpreter carries the commarea across task
  boundaries within a single run; the recipe is still entry-only.

## 3. Host requirements (build nothing until these hold)

1. **A deterministic interpreter is the crediting authority**, and a real
   compiler (GnuCOBOL) is the authority over the interpreter. Any
   interpreter change must be checked against compiled behavior on a
   minimal program before trusting results built on it.
2. **One crediting path.** Every candidate recipe — from any phase — is
   executed from entry through a single deduplicating `run()` into a
   single ledger. Nothing is credited on a generator's say-so. The ledger
   credits **every** direction the trace took, not only the targeted one,
   and keeps the first (cheapest) recipe per direction.
3. **From-disk reproduction is a hard gate.** After writing witnesses,
   rebuild a fresh interpreter from each stored row alone and confirm the
   recorded direction is re-taken. The bar is 100%. Anything less means
   state leaked outside the recipe — find it; do not ship the number.
4. **Evidence rule.** Everything staged must come from (a) the program's
   own text — compared literals, 88-level VALUE clauses, PIC shapes,
   declared constants, its own WHEN arms — or (b) platform-fixed
   vocabulary (FILE STATUS, SQLCODE, DFHRESP, DFHAID, DIBSTAT, intrinsic
   accepting sets). Never from a variable's *name*. Enforce mechanically:
   a token-level scan of executable code for corpus-specific identifiers
   must print zero.

## 4. The algorithm

Four phases, strictly ordered by cost. The measured economics justify the
ordering: base construction produced tens of directions per hundred runs;
per-goal search produced ~1 per 15,000. Spend accordingly.

### Phase 0 — Evidence harvest

From the program and its copybooks, per variable: compared literals,
88-level values **including THRU/THROUGH ranges** (emit endpoints plus an
interior representative), class-condition shapes (NUMERIC, alphabetic
letters-runs), and slice relationships (an 88 on a 2-byte slice of a
4-byte field composes with evidence for the other slice). **Render every
value at the field's declared PIC width** — the integer 1 is not the
screen byte `'01'`; unrendered evidence silently satisfies nothing.
Chase evidence across MOVE hops and REDEFINES twins by byte position:
the validator often tests a work copy several moves away from the field
you can actually set.

### Phase 1 — Base construction (the cycle probe)

Construct a small number of *deliberate* runs that arrive deep in the
program's real modes:

- Entry shaped as the platform delivers it (e.g. `EIBCALEN=0` first
  cycle), an attention key **the source itself compares against**.
- A **success world**: every status channel primed with its family's
  success code, so fetches succeed and the program advances through its
  modes (fetch → update → confirm) across task cycles within one run.
- An **all-valid screen**: every input field at its best-known pass shape
  from Phase 0.

This phase is where most coverage comes from. It is forward construction,
not search: tens of runs, not thousands.

### Phase 2 — Repair-to-green (credit-blind)

The base screen will not be fully valid on the first try. Repair it —
**without harvesting credit during repair**; fusing repair with harvest
was the direct cause of a long plateau:

- Metric: the position of the **first failure** in each first-match
  chain. A repair is accepted only if the first-failure moves *strictly
  deeper*. Nothing else is monotone — not per-field validity, not run
  depth, not state richness. Five locally-plausible per-field refinements
  were once measured to jointly cut yield 62→26; optimize only the
  frontier position.
- Recover **face-pairs as blocks** (two arms sharing a duplicated body
  are the two faces of one field): swapping NOT-OK for BLANK on the same
  field is lateral motion and must never count as progress.
- Escalate stalls with cheap, named tactics: fit 88-range members at PIC
  width; split a joint 88's enumeration members across the two fields it
  constrains; mirror equality constraints by staging the stub-delivered
  side to the observed operand value. Escalate to combinatorial cover
  only if per-arm construction *measurably* conflicts — in practice it
  never did.

End state: one fully-green background per chain (or a named blocker per
field that cannot reach green).

### Phase 3 — Per-arm harvest

With a green background, every arm of a first-match chain costs one run:
spoil **exactly one field to exactly one face** (blank for the BLANK arm;
a wrong-shape value for NOT-OK), all else untouched. Generate one
background per missing `(field, face)`, run each once from entry, credit
through the standard path. This converts a combinatorial residual into a
linear family.

### Phase 4 — Generous sweep and residual classification

Run whatever cheap enumerative battery exists (plans, samples, worlds,
staged stubs) for everything outside chain structures, credited by the
same ledger. Then classify every remaining direction with a name:

- **statically dead** — e.g. a face whose only SET is unconditionally
  overwritten before every observable use;
- **outside the recipe envelope** — e.g. requires a mid-conversation
  attention-key change if recipes fix one AID per run;
- **open with a named obligation** — e.g. screen must byte-equal a
  fetched record across N fields including packed decimals;
- **infeasibility certificate** — only after exhaustive enumeration of
  every in-scope evidence source. **Certificates are hypotheses until the
  named lever is built**: two of them fell in this project the moment
  someone implemented the lever they claimed was needed.

## 5. The diagnostic spine (optional but recommended)

A goal-directed **upstream walk** — start at a missing direction, carry a
requirement set (variable → satisfying *set*, not exact value), step
paragraph-by-paragraph toward entry, reconcile at each hop (what does
this paragraph write / clobber / require) — is measurably **not** a yield
engine: on the reference corpus only ~22% of directions were reachable by
any goal-directed method, and 11% were unreachable by construction (they
fire only as side effects of runs, never as solvable goals). Build it for
its *refusals*: "clobbered at hop 0 by paragraph X", "wanted message A,
producer can only emit B" are addresses that direct Phase 1/2 effort.
Walk hop-by-hop; do not jump to dataflow writers — the jump is blind to
intervening clobbers and every shortcut taken here had to be repaired
later.

## 6. What not to build (measured dead — do not re-propose)

- Iterated refinement / epochs: five separate confirmations of zero at
  the second pass. Progress is *spatial* (deeper bases, later first
  failures), never repetition.
- Symbolic/SMT path solving over COBOL semantics.
- Cross-program recipe transfer; recipe splicing/fusion/union in any
  form; free-slot mutation; raw budget increases (all measured inside a
  rejected band, ~0.0–1.6 new directions per 100 runs vs ~10 for
  derivation).
- Exhaustive enumeration of 1-byte domains (zero firings, twice).
- Screen-field evidence from BMS mapsets, DDL, or JCL (measured: zero
  bits beyond the program text).

## 7. Verification protocol (every claim, every merge)

- **Three arms**: A = existing baseline battery, B = this approach,
  C = A ∪ B by direction key. The headline is residual reduction
  `(missing_A − missing_C) / missing_A`, pooled and per program.
- At least one **untouched control program** per measurement; it must not
  move at all.
- Standing gates: full unit suite green; conformance/differential counts
  *byte-identical* to before; genericity scan prints 0; from-disk
  reproduction 100%.
- Verify from **raw artifacts** (the witness files), never from a
  generator's own logs — counting errors flatter; one probe reported 82
  where the truth was 9.

## 8. Pitfalls ledger (each of these actually happened)

1. Nested intrinsics (`FUNCTION LENGTH(FUNCTION TRIM(X))`) mis-parsed
   into a guard on a phantom variable — unconditionally true, phantom
   coverage plus one unwitnessable direction per site.
2. Multi-operand `STRING A B(1:2) DELIMITED BY SIZE` read as one term —
   every STRING-composed work field silently empty.
3. 88 THRU/THROUGH ranges never decoded — no valid date could ever be
   constructed; an entire cascade masked behind one field.
4. Evidence not rendered at PIC width — right value, wrong bytes.
5. Dedup keys that *sort* mappings while runs apply them in insertion
   order — a credited recipe the stored form cannot restate. Canonicalize
   application order or key on it; catch via the 100% reproduction gate.
6. `PERFORM A THRU B` is a range entry, not a call to "A THRU B" — bit
   three separate mechanisms.
7. A validator that convicts what it cannot evaluate ("cannot judge" must
   be no-evidence, never evidence-against).
8. The replay oracle must fold decision kinds the same way the ledger
   does; a mismatched oracle silently reports success (bit two probes).
9. Static satisfaction is not reachability: a value satisfying a
   predicate proves nothing until a run *arrives* at the predicate in the
   right mode. Verify dynamically, from entry, always.

## 9. Order of effort, summarized

Evidence → one great base per mode (probe) → repair it green, credit-blind
→ harvest arms linearly → sweep generously → name the residual. When
stuck: suspect the parser and interpreter before the planner; find the
single structural cause before assuming many hard directions; and prefer
building the named lever over trusting the diagnosis that named it.
