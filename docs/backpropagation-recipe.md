# The Backpropagation Recipe

The goal-directed half of witness discovery: start at a target deep in the
program, derive what it needs, and carry that requirement **upstream, one
paragraph at a time, until it reaches program entry** — then run forward
once to validate. One loop. Its induction variable is the frontier's
position in the program, not an iteration counter.

This document specifies only that algorithm. It assumes the host already
has: a deterministic interpreter, a from-entry deduplicating crediting
path, an evidence harvester, and forward base construction. No code —
contracts and steps.

---

## 1. Objects

- **Goal** — one branch direction: `(paragraph, ordinal, kind, direction)`.
- **Requirement set R** — the algorithm's moving state: a map
  `variable → satisfying SET of values`. Sets, never single exact values;
  demanding one exact byte string where the guard accepts a whole class is
  the single most measured cause of false "unsolvable" verdicts.
- **Frontier P** — the paragraph R is currently attached to. Invariant:
  *any state arriving at P that satisfies R will drive the goal direction
  when execution continues forward from P.*
- **Pass-value table T[Q]** — per paragraph, accumulated facts of the form
  *"started with inputs σ, Q produced outcomes ω and post-state π"*. Each
  fact is machine-verified by executing Q in isolation, so it is true of
  the program forever, independent of reachability. Tables are write-once,
  monotonically growing, shared across all goals — this is where the
  "store all pass values by para" idea lives, and it is what makes the
  hundredth goal cheaper than the first.

## 2. Initialization — the local solve (at the leaf)

Run the goal's paragraph (plus its PERFORM closure) in isolation. Find an
input assignment that fires the goal direction, using the evidence
harvest (the guard's own compared literals, 88 values with ranges
decoded, class shapes — all rendered at declared PIC width). Consult
T[paragraph] first; only sweep when the table has no matching fact.
Reduce the firing assignment to its essential pairs (drop a variable,
re-run, keep the drop if the direction still fires). The essential pairs,
widened to satisfying sets wherever the guard admits a class, become the
initial R. If no assignment fires the direction even in isolation, stop:
refusal `local-unsolvable` — this direction cannot be reached by any
goal-directed method and belongs to forward construction.

## 3. The loop — one hop upstream per step

While P is not the entry paragraph, identify Q, the paragraph that
executes immediately before P on the route being walked, and reconcile R
across the Q→P boundary. **Walk; do not jump.** Jumping straight to a
dataflow writer skips the paragraphs in between and is blind to what they
overwrite — every shortcut of this kind had to be repaired later. Three
cases per requirement, plus one obligation:

1. **Q writes the variable.** Solve Q under an *output constraint* —
   inputs to Q that make it emit a value inside the requirement's
   satisfying set. Two modes, strictly in this order:
   - **Demand-driven**: search Q's input evidence for an assignment whose
     post-state lands in the satisfying set.
   - **Offer-driven**: if demand fails, intersect Q's *achievable
     outputs* — read from T[Q], the facts it already has — with the
     satisfying set. Adopt any member of the intersection.
   An empty intersection after both modes is a refusal, and it is a
   strong one: *no achievable output of the actual producer satisfies the
   target* — recorded with the hop address, the variable, and both sets.
   On success, Q's own input requirements for producing that output
   **join R** (this is the transformer: R is a weakest precondition,
   computed concretely by execution rather than symbolically — the
   symbolic version measured zero).
2. **Q does not touch the variable.** The requirement passes through
   unchanged. This case is only trustworthy *because* you walk hop by
   hop.
3. **Q clobbers the variable** (writes it with something outside the
   satisfying set, unconditionally). Record the clobber with its hop
   address. Either the clobbering write is itself solvable (case 1 applied
   to the clobber), or the requirement must be satisfied *downstream* of
   Q — which usually means the value must arrive by a different channel
   (a stub delivery, a later screen receive) — or the goal is refused
   here, at a named line, for a named reason.
4. **Donation.** Every run executed during this step — demand sweeps,
   offer checks, all of them — donates its (σ, ω, π) facts to T[Q].
   Failures donate as much as successes.

Then P ← Q, and the loop continues.

## 4. Termination at the top

When the frontier reaches entry, every surviving requirement is one of:

- **Entry-controlled** — nothing on the route writes it: pin it in the
  recipe's entry state.
- **Stub-controlled** — it is written by an external operation's return:
  stage the required value in the recipe's stub outcome series, at the
  right position, drawn from platform vocabulary or the intersection
  computed in step 1.
- **Prior-cycle-controlled** — written only by the program's own previous
  task cycle (mode flags, carried commarea): the "top" is not the top.
  Recurse the **same loop** with the previous cycle as the program: the
  goal becomes "end cycle k−1 at its terminal with the commarea
  satisfying these requirements." Cap the recursion (two cycles covered
  every case measured). The final recipe remains entry-only: it simply
  spans the whole conversation in one run.

## 5. The forward pass — one, not many

Compose the recipe and run it from entry through the standard crediting
path. Credit **everything** the trace takes, not just the goal. Two
outcomes:

- The goal direction is taken: done; the ledger keeps the recipe.
- The run **diverges** — some guard upstream went the wrong way. Record
  the *first* divergent guard with the operand values actually observed;
  donate those observed in-flight values (things the program computed,
  present in no static pool) to the evidence pools; emit the divergence
  as a refusal with its address. Do **not** build an outer retry loop
  around this: five separate measurements confirmed a second pass over
  the same evidence adds nothing. The divergence record's value is
  diagnostic — it tells forward construction which base is missing — not
  fuel for iteration.

## 6. Output contract

For every goal, exactly one of:

- **A witness** — a self-contained recipe, reproduced from disk by a
  fresh interpreter (100% bar, no exceptions).
- **A named refusal** — one of: `local-unsolvable` (direction fires in no
  isolated run; forward construction's territory by proof),
  `empty-intersection @ hop N, variable V` (no achievable producer output
  satisfies the target), `clobbered @ hop N by paragraph Q`,
  `stub-terminal-unsolved`, `cycle-cap`, `validation-diverged @ guard G
  with observed operands`. The hop address is the point: a refusal
  without an address is a shrug; a refusal with one is a work item.

## 7. Calibration — what to expect (measured on the reference corpus)

- Goal-directed backpropagation reached **~20–25%** of a hard residual;
  the rest needed forward-constructed bases (deep-mode probes, repaired
  screens) that no backward derivation produces. Run this algorithm
  *after* forward construction, on what remains — and treat its refusal
  addresses as the specification for the next base to construct.
- Roughly one in ten residual directions was `local-unsolvable`: they
  fire only as side effects of other runs, never as solvable goals. The
  initialization check catches them in milliseconds; do not spend budget
  walking them.
- Memoize producer solves on `(paragraph, required-output-set)` and let
  T[·] carry across goals; the walk's cost is dominated by producer
  solves, and distinct requirements are far fewer than goals.
- Termination is structural: chain depth × cycle cap bounds the loop; no
  fixpoint detection is needed because there is no outer iteration.
