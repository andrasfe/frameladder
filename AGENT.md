# Frame Ladder — agent protocol

You are the agent in this loop. Everything mechanical is done by the
`frameladder` CLI; you supply the judgment it cannot. This file is the only
static input. The program source and the call trace you are asked about arrive
dynamically, as arguments.

## What the tool does, and what you do

The ladder starts at the frame you want to reach and walks **outwards** along
the call chain, rewriting each obligation into one on the caller's own
arguments, until what is left names things the harness can set — stub returns
and entry state. That is deterministic and it is not your job.

Your job begins where the derivation runs out:

- the shortest chain is not the chain you want
- a plan is symbolically complete but does not reach the target
- an obligation is left open with a reason you can read the source and resolve
- a run loops instead of arriving
- a value needs to mean something (a valid date, a matching key) rather than
  merely satisfy an inequality

## The loop

```
trace   →  see the chain and every guard on it
plan    →  see what the ladder bound, and what it could not
verify  →  run it; if it fails, read exactly where
explain →  read that one frame and its variables' provenance
bind    →  record your decision
verify  →  again
```

Stop when `verify` says REACHED. Record what you learned with `note` so the
next session does not rediscover it.

## Commands

Every command takes the program first: a `.cbl` (parsed here) or a `.ast`
(pre-parsed). Add `--json` for machine-readable output, `--work-dir DIR` to
persist decisions.

| Command | Use it to |
|---|---|
| `frames` | rank reachable paragraphs by depth and guard weight — find worthwhile targets |
| `trace TARGET [--via A,B]` | see the call chain and the obligations each hop imposes |
| `plan TARGET` | see bindings, rendezvous couplings, and open obligations |
| `verify TARGET` | run the plan; on failure, get the first unreached frame and the guards that went the wrong way |
| `explain FRAME --variables A,B --source` | read one frame: its source, and where each variable is produced |
| `sweep` | plan and verify every target; the unreached ones are your work list |
| `bind --bind VAR=VALUE --why "..."` | record a decision (needs `--work-dir`) |
| `note TEXT` / `resume` | journal an observation / reload state after a restart |

## Reading a failed verify

```
NOT REACHED   0000-MAIN -> 9700-CHECK-CHANGE-IN-REC-EXIT
of which      0000-MAIN -> 2000-DECIDE-ACTION -> 9600-WRITE-PROCESSING
first frame not entered: 9700-CHECK-CHANGE-IN-REC-EXIT
guards on the chain that went the wrong way:
   9700-CHECK-CHANGE-IN-REC:4115  IF  ACCT-ACTIVE-STATUS EQUAL ACUP-OLD-ACTIVE-STATUS ...
        actual: {"ACCT-ACTIVE-STATUS": "", "ACUP-OLD-ACTIVE-STATUS": ""}
```

Read it in this order:

1. **`of which`** — how far it got. The frame after the last one listed is
   where to look.
2. **`stopped`** — `runaway loop in X` means it never arrived because `X` ran
   hundreds of times. That is a stub-sequencing problem, not a guard problem;
   go to *Stub outcomes* below.
3. **`guards ... that went the wrong way`** — with the actual values. If a
   variable is empty when it should hold something, ask why: `explain` the
   frame and look at its provenance.
4. **open obligations** — each carries the reason it could not be discharged.

## The four judgment calls

**Choose a different chain.** The default is the shortest chain, and shortest
often means *skipping the set-up that makes the target reachable*. If `verify`
shows the run arriving at a frame with nothing initialised, force the route:
`--via 8100-FILE-OPEN,8500-READTRNX-READ`. Waypoints are visited in order.

**Bind a value the ladder cannot derive.** Open obligations that say
`no witness value` or `strict ordering between two produced values` are asking
for a decision. `explain` the frame, read the source, and `bind`. Your
bindings win over anything derived, and persist in the journal.

**Supply stub outcomes.** An external operation returns a *sequence*, not a
constant: records, then end-of-file. Three knobs, and they are different
things:

- `--default OP:VAR=VALUE` — when no planned outcome matches this call at all
  (an OPEN succeeding while the plan only describes a READ)
- `--stub-repeat N` — how many times each planned outcome is delivered
- `--terminal OP:VAR=VALUE` — what comes back once the planned ones run out,
  which is how a read loop ends

Getting these wrong is the usual cause of `runaway loop`. A terminal that
makes reads end will also make *opens* fail if the program routes both through
one subprogram — that is a real limitation, noted below.

**Accept a partial answer.** `plan` reporting open obligations while `verify`
reports REACHED is normal and fine: `solved` is conservative, and some
obligations turn out not to gate anything. Trust `verify`.

## What is derived for you — do not redo it by hand

- **Rendezvous.** When a guard requires two *produced* values to be equal
  (a key read from one file matching a key read from another), there is
  nothing to solve: the ladder picks a value and plants it at both producers.
  Any value works; agreement is the whole content of the obligation.
- **Guard avoidance.** An obligation contradicting a literal assignment is not
  dead if that assignment sits under a condition. The obligation moves onto
  the guard and the ladder recurses.
- **Escape avoidance.** Reaching anything at line N requires that no earlier
  guarded `GO TO` in the paragraph fired.
- **`ALTER`, `PERFORM THRU`, fall-through, `EVALUATE TRUE`.** All modelled.
- **Provenance.** Which stub invocation produces a field, told apart by the
  literals set before the call.

## Known limits — recognise these rather than fight them

- **A variable that must hold different values at different moments.** A
  dispatcher's file selector walks TRNXFILE → READTRNX → XREFFILE. One
  binding per variable cannot express that. Bind its *initial* value and let
  the program advance it; if the chain re-enters the dispatcher, expect the
  ladder to bind only one of the values it needs.
- **Per-invocation stub sequencing.** `--terminal` is per operation, not per
  discriminator, so a program that routes opens and reads through one
  subprogram cannot have both a succeeding open and an ending read.
- **Subscripts are flattened.** `WS-TAB(I)` and `WS-TAB` are one cell, so
  table-indexed plans are verified loosely. `approximations` in the output
  says when this bit.
- **`COMPUTE` is not evaluated.** Reported, not hidden.

## Worked example

```bash
P=path/to/COACTUPC.cbl

frameladder $P frames --limit 20                      # pick a deep target
frameladder $P trace 9700-CHECK-CHANGE-IN-REC-EXIT    # see the chain
frameladder $P verify 9700-CHECK-CHANGE-IN-REC-EXIT   # NOT REACHED, blocked at the EXIT
```

The chain went straight to the EXIT and never entered the frame that gates it,
so no obligations were lifted. Force the route:

```bash
frameladder $P verify 9700-CHECK-CHANGE-IN-REC-EXIT --via 9700-CHECK-CHANGE-IN-REC
# REACHED
```

One `--via`, derived from reading one diagnostic. That is the shape of the job.
