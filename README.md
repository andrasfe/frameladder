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

Two mechanisms carry the weight:

**Rendezvous.** When a guard requires two *produced* values to be equal, there
is nothing to solve. The obligation is that two independent producers agree, so
the ladder picks a value and plants it at both. Any value works — agreement is
the whole content of the obligation, and it costs O(1) here where sampling
costs the size of the domain squared.

**Guard avoidance.** An obligation that contradicts a literal assignment is not
dead if that assignment sits under a condition. `MOVE 'Y' TO END-OF-FILE` under
`WHEN '10'` means `END-OF-FILE != 'Y'` is reachable by making the return code
anything else. The obligation moves onto the guard, and the ladder recurses.

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

Every reachable paragraph, planned and then verified by execution:

| program | lines | targets | reached | max chain |
|---|---|---|---|---|
| COACTUPC | 4,236 | 84 | 83 | 6 frames |
| COCRDLIC | 1,459 | 38 | 38 | 6 frames |
| COCRDUPC | 1,560 | 44 | 44 | 3 frames |
| CBSTM03A | 924 | 24 | 17 | 5 frames |

CBSTM03A is the hard one on purpose: its control flow is an `ALTER`-driven
dispatcher that re-enters one paragraph with a different selector each pass.
See *Limits*.

`plan` reporting open obligations while `verify` reports REACHED is normal —
`solved` is deliberately conservative, and some obligations gate nothing.
Trust `verify`.

## Limits

Stated rather than hidden; each is reported in the output when it bites.

- **A variable that must hold different values at different moments.** One
  binding per variable cannot express a dispatcher selector walking
  TRNXFILE → READTRNX → XREFFILE. Bind its initial value and let the program
  advance it.
- **`--terminal` is per operation, not per discriminator**, so a program
  routing opens and reads through one subprogram cannot have both a succeeding
  open and an ending read.
- **Subscripts are flattened**: `WS-TAB(I)` and `WS-TAB` are one cell, so
  table-indexed plans are verified loosely.
- **`COMPUTE` is not evaluated.**
- Verification is by the built-in interpreter, not a compiled binary.

## Tests

```bash
python3 -m pytest tests/test_frameladder.py -q     # 20 unit tests, self-contained
python3 tests/parser_agreement.py                  # parser vs reference ASTs
```
