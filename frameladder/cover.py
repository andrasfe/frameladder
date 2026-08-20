"""Per-arm background construction for first-match verdict chains.

The lateral trap, named by the v6 window walk: a first-match chain over
per-field verdicts fires exactly one arm per run - the earliest field
whose verdict fails - and each field has two failure faces (NOT-OK and
BLANK) with an arm each. A walk that repairs fields *for credit* spends
each field as a spoil to reach its arms, and every spent field then
masks everything deeper: extinguishing one face re-lights the other,
and no single background the walk keeps is below both.

This module dissolves the trap by separating two jobs the walk fused:

1. **Repair to green.** Build ONE background screen that passes every
   field - both faces quiet everywhere - judged not by credit but by a
   monotone measure: the deepest chain block the background's own run
   still fires. A candidate value is adopted only when that first
   failure moves strictly deeper (or vanishes). Credit is incidental;
   the background is the deliverable.
2. **Harvest per-arm.** With a green (or deepest-achieved) background
   B, the background for missing arm k = (field F, face) is simply B
   with F alone set to the value expressing that face - every earlier
   field passes because B passes it, every later field is irrelevant
   because first-match never reads past k. One run per face per field,
   all through the same deduplicating from-entry crediting the rest of
   the battery uses.

Where no candidate moves the first failure past a field, that field is
the measured blocker: it is reported by arm and condition, with every
arm it masks counted - a named refusal, not an absence. A candidate
that fixes the target field while breaking an earlier one (the max
measure regresses) is recorded as a *conflict*; measured first, and
only if conflicts actually occur does a multi-background cover become
the formulation.

Everything staged obeys the evidence rule: pass shapes and spoils come
from `chain._valid_screen` / `chain._spoil_family` - the program's own
comparisons, 88-levels, class conditions and slice compositions - and
the platform status vocabulary reaches stubs only through
`chain._success_world`. Nothing here reads a variable's name.
"""

from __future__ import annotations

import json

from .conditions import condition_atoms
from .conformance_defaults import WORLDS, io_defaults
from .interpreter import Interpreter
from .ledger import Ledger, _freeze
from .chain import (MAX_VALUES, _Budget, _Index, _cycle_bases,
                    _cycle_fields, _direction_key, _materialise,
                    _screen_variants, _spoil_family, _statements,
                    _success_world, _valid_screen)

MIN_ARMS = 8            # WHEN arms before an EVALUATE counts as a chain
MAX_ROUNDS_EXTRA = 16   # repair rounds past one-per-block
# Values tried per field per repair round: the chain's sweep cap, so a
# field whose accepting set is wide (a message pool, an attention-key
# enumeration) is fully sweepable here exactly when it is there. The
# trials ceiling scales with it - it was 160 at the old cap of 8.
MAX_CANDIDATES = MAX_VALUES
MAX_TRIALS_PER_ROUND = 20 * MAX_CANDIDATES
DEPTH_SLACK = 12        # direction-count collapse that voids an adoption
SWEEP_KINDS_PER_ROUND = 2   # spoil kinds per field on interim harvests


def _body_signature(arm) -> str:
    """Two consecutive arms with identical bodies are one field's faces.

    The parser has already copied a shared fall-through body into every
    WHEN of its group, so the grouping the source expressed positionally
    survives only as body identity.
    """
    return json.dumps([(c.get("type"), c.get("attributes"))
                       for c in arm.get("children") or []], sort_keys=True,
                      default=str)


def _find_chains(index, cycle_fields) -> list:
    """Every first-match verdict chain: EVALUATE TRUE, many arms, and a
    majority of arm conditions naming state that is NOT carried across
    the task boundary (a mode dispatcher routes on the commarea; a
    verdict chain judges this cycle's fields)."""
    names = frozenset(index.model.condition_names or ())
    chains = []
    for para_name in index.names:
        para = index.paragraphs.get(para_name, {})
        for stmt in _statements(para):
            if stmt.get("type") != "EVALUATE":
                continue
            subject = str((stmt.get("attributes") or {}).get("subject")
                          or "").strip().upper()
            if subject != "TRUE":
                continue
            arms = [c for c in (stmt.get("children") or [])
                    if c.get("type") == "WHEN"]
            if len(arms) < MIN_ARMS:
                continue
            rows, verdict_count, judged = [], 0, 0
            for arm in arms:
                cond = str((arm.get("attributes") or {}).get("value")
                           or "").strip()
                rows.append({"ordinal": arm.get("ordinal"),
                             "condition": cond,
                             "other": cond.upper() in ("OTHER", "ANY"),
                             "signature": _body_signature(arm)})
                if rows[-1]["other"]:
                    continue
                judged += 1
                is_verdict = False
                try:
                    groups = condition_atoms(cond, names=names)
                except Exception:                            # noqa: BLE001
                    groups = []
                for group in groups:
                    for atom in group:
                        for side in (atom.lhs, atom.rhs):
                            if getattr(side, "kind", "") != "var":
                                continue
                            name = str(side.name).upper()
                            entry = (index.model.condition_names
                                     or {}).get(name)
                            if not entry:
                                continue    # a verdict arm names an 88
                            parent = str(entry[0]).upper()
                            if parent not in cycle_fields \
                                    and parent.split(" OF ")[0] \
                                    not in cycle_fields:
                                is_verdict = True
                if is_verdict:
                    verdict_count += 1
            if not judged or verdict_count * 2 <= judged:
                continue
            # Blocks: consecutive arms with identical bodies are the
            # faces of one field; the OTHER arm stands alone.
            blocks, block_of, current, last_sig = [], {}, [], None
            for row in rows:
                sig = ("OTHER",) if row["other"] else row["signature"]
                if current and sig != last_sig:
                    blocks.append(current)
                    current = []
                current.append(row["ordinal"])
                last_sig = sig
                block_of[row["ordinal"]] = len(blocks)
            if current:
                blocks.append(current)
            other_arms = {row["ordinal"] for row in rows if row["other"]}
            chains.append({
                "paragraph": para_name,
                "arms": rows,
                "ordinals": [row["ordinal"] for row in rows],
                "condition_of": {row["ordinal"]: row["condition"]
                                 for row in rows},
                "blocks": blocks,
                "block_of": block_of,
                "other": other_arms,
            })
    return chains


def _merge_stubs(*worlds) -> dict:
    out: dict = {}
    for world in worlds:
        for op, fields in (world or {}).items():
            for field, value in fields.items():
                out.setdefault(op, {}).setdefault(field, value)
    return out


def _candidates(index, union, field, held) -> list:
    """Values worth trying as a field's pass shape, pass-shaped end of
    the evidence first (the tail is the complement / class shape / range
    endpoint; the head is the failing literals the program compares
    against), then the two class shapes - the letters run and the digits
    run - that answer alpha-only and numeric edits whose accepting sets
    appear in no comparison literal (the same two shapes
    `chain._spoil_family` uses from the failing side)."""
    from .heuristics import complement_value
    merged = []
    values = [v for v in union.get(field, ()) if isinstance(v, str)]
    for value in list(reversed(values)) + values:
        if value != held and value not in merged:
            merged.append(value)
    extra = complement_value(field, index.model.pic_of(field), values)
    if extra is not None and extra != held and extra not in merged:
        merged.append(extra)
    width = index.width(field) or len(str(held)) or 1
    for shaped in ("A" * width, "9" * width):
        if shaped != held and shaped not in merged:
            merged.append(shaped)
    return merged[:MAX_CANDIDATES]


def _joint_pool(index) -> list:
    """``[(parent, [values])]`` - every 88-level VALUE list big enough to
    be an enumeration table. A cross-field edit (a state+zip-prefix
    combo, an area-code table) publishes its accepting set as exactly
    such a list on a work field the program STRINGs together; the list
    is the program's own text, so composing screen bytes from its
    members obeys the evidence rule."""
    from .chain import _literal
    pool: dict = {}
    for name, entry in (index.model.condition_names or {}).items():
        if not entry:
            continue
        parent = str(entry[0]).upper()
        values = []
        for raw in (entry[1] or []):
            value = _literal(raw)
            if isinstance(value, int) and not isinstance(value, bool):
                # A THRU range arrives expanded but unpadded: month 1 is
                # the bytes '01' in the PIC 9(2) the 88 sits on.
                width = index.width(parent)
                value = str(value).zfill(width) if width else str(value)
            if isinstance(value, str) and len(value) >= 2:
                values.append(value)
        if 4 <= len(values) <= 600:
            bucket = pool.setdefault(parent, [])
            for value in values:
                if value not in bucket:
                    bucket.append(value)
    return sorted(pool.items())


def run_cover(program, budget=4000, baseline=(), ledger=None) -> dict:
    """Construct per-arm backgrounds for every verdict chain; return the
    report, crediting every run into ``ledger`` (fresh one if None)."""
    from .ladder import analyse
    index = _Index(program)
    _graph, prov = analyse(program)
    entry = index.names[0]
    ledger = ledger if ledger is not None else Ledger()
    the_budget = _Budget(budget)
    seen_runs: set = set()
    cycle_fields = _cycle_fields(program, index)
    chains = _find_chains(index, cycle_fields)
    report = {"budget": budget, "chains": [], "runs": 0}
    if not chains:
        report["note"] = "no first-match verdict chain in this program"
        return {"report": report, "ledger": ledger}

    bases = _cycle_bases(program, index) \
        or [({}, world) for world in WORLDS]
    success_world = _success_world(index, prov)
    variants = _screen_variants(index, prov)
    union = dict(getattr(_valid_screen, "__evidence__", {}) or {})
    joint_pool = _joint_pool(index)

    def execute(state, world, screen, tag):
        """From-entry run under the success world plus one screen.

        Credits through the deduplicating ledger path when the recipe is
        novel; observes through a fresh uncredited interpreter when the
        recipe was already run (its trace is still the measurement)."""
        if the_budget.left() <= 0:
            return None
        stubs = _materialise(_merge_stubs(success_world, screen)) or None
        key = (_freeze(state or {}), world, _freeze(stubs or {}))
        the_budget.spend()
        try:
            interp = Interpreter(program, dict(state or {}), stubs=stubs,
                                 defaults=io_defaults(program, world))
            trace = interp.run(entry)
        except Exception:                                    # noqa: BLE001
            return None
        if key not in seen_runs:
            seen_runs.add(key)
            ledger.credit(trace, state or {}, world, stubs, None, tag)
        return trace

    def depth(trace):
        return len({_direction_key(g) for g in trace.guards})

    have_before = set(baseline or ()) | ledger.covered()

    # ------------------------------------------------------------------
    # Probes: every screen variant under every base, credited; the
    # per-chain machinery below reads these traces for structure.
    # ------------------------------------------------------------------
    probes = []
    for number, screen in enumerate(variants):
        for base_state, world in bases:
            trace = execute(dict(base_state), world, screen,
                            "cover:probe:%d" % number)
            if trace is not None:
                probes.append((screen, dict(base_state), world, trace))

    for chain in chains:
        para = chain["paragraph"]
        ordinals = set(chain["ordinals"])
        block_of = chain["block_of"]
        other = chain["other"]
        chain_report = {"paragraph": para, "arms": len(chain["arms"]),
                        "blocks": len(chain["blocks"]),
                        "adoptions": [], "conflicts": [], "blockers": [],
                        "green": False, "rounds": 0}
        report["chains"].append(chain_report)

        def fired_true(trace):
            return {g.ordinal for g in trace.guards
                    if g.paragraph == para and g.kind == "WHEN"
                    and g.result and g.ordinal in ordinals}

        touched = [p for p in probes if fired_true(p[3])]
        if not touched:
            chain_report["note"] = "chain never reached by any probe"
            continue
        structural = frozenset.intersection(
            *[frozenset(fired_true(p[3])) for p in touched])
        chain_report["structural"] = sorted(structural)

        def failure(trace):
            """The deepest chain block this run's own screen fails, or
            None when only structural / head / OTHER arms fired. Deepest,
            because the update-mode evaluation is the one the screen
            owns; earlier cycles fire their own artifacts (a blank-map
            arm on task 1) which the structural set already holds."""
            fired = fired_true(trace) - structural - other
            if not fired:
                return None
            return max(block_of[o] for o in fired)

        best = max(touched, key=lambda p: (failure(p[3]) or -1, depth(p[3])))
        current = {op: dict(fields) for op, fields in best[0].items()}
        base_state, world = best[1], best[2]
        bg_trace = best[3]

        owned: dict = {}          # field -> set of chain arms its spoils raise
        field_blocks: set = set()   # block indices demonstrably field-owned

        def sweep(spoil_source, bg, tag, kinds_cap=None):
            """Spoil each field of ``spoil_source`` over the *current*
            background; credit every run and record which arms each
            field's failure owns. Each spoiled run IS the constructed
            per-arm background: every earlier field passes because the
            background passes it, the spoiled field expresses one face,
            first-match never reads deeper."""
            base_arms = fired_true(bg) if bg is not None else set()
            per_field: dict = {}
            for op, field, kind, value in _spoil_family(index, spoil_source):
                per_field.setdefault((op, field), []).append((kind, value))
            # A field whose pass shape is not a digits run fails its own
            # edit on the digits run - the mirror of `_spoil_family`'s
            # letters-run spoil against a digits pass - and the NOT-OK
            # face of an alpha-only field is expressible no other way.
            for op, fields in spoil_source.items():
                for field, pass_value in fields.items():
                    text = str(pass_value)
                    if not text.strip().isdigit():
                        width = max(len(text), index.width(field) or 1)
                        spoils = per_field.setdefault((op, field), [])
                        if all(v != "9" * width for _k, v in spoils):
                            spoils.append(("digits", "9" * width))
            for (op, field), spoils in per_field.items():
                if kinds_cap is not None:
                    spoils = spoils[:kinds_cap]
                for kind, value in spoils:
                    if the_budget.left() <= 0:
                        return
                    spoiled = {o: dict(f) for o, f in current.items()}
                    spoiled.setdefault(op, {})[field] = value
                    trace = execute(dict(base_state), world, spoiled,
                                    "%s:%s:%s" % (tag, field, kind))
                    if trace is None:
                        continue
                    raised = (fired_true(trace) - base_arms) - other
                    if raised:
                        owned.setdefault(field, set()).update(raised)
                        field_blocks.update(block_of[o] for o in raised)

        sweep(current, bg_trace, "cover:sweep0", kinds_cap=None)

        rounds_cap = len(chain["blocks"]) + MAX_ROUNDS_EXTRA
        stalled = None
        for round_number in range(rounds_cap):
            if bg_trace is None or the_budget.left() <= 0:
                break
            chain_report["rounds"] = round_number
            target_block = failure(bg_trace)
            if target_block is not None:
                field_blocks.add(target_block)
            head_blocks = {b for b in range(len(chain["blocks"]))
                           if field_blocks and b < min(field_blocks)}
            if target_block is None:
                # All-passing: no non-structural verdict arm fires. The
                # head arms' own feasibility is a separate question (a
                # found-data message-88 may be overwritten before the
                # reader on every route) - greenness is about the
                # fields, and the fields are all quiet.
                chain_report["green"] = bool(fired_true(bg_trace))
                chain_report["head_fired"] = sorted(
                    o for o in fired_true(bg_trace) - other
                    if block_of[o] in head_blocks)
                break
            bg_depth = depth(bg_trace)
            target_arms = set(chain["blocks"][target_block])
            # Fields whose measured spoils raise this block go first -
            # the field that owns the failing arm is almost always among
            # them; the rest follow in screen order.
            fields = [(op, field) for op, held in current.items()
                      for field in held]
            fields.sort(key=lambda pair: 0 if owned.get(
                pair[1], set()) & target_arms else 1)
            adopted = None
            trials = 0
            for op, field in fields:
                held = current[op][field]
                for candidate in _candidates(index, union, field, held):
                    if trials >= MAX_TRIALS_PER_ROUND \
                            or the_budget.left() <= 0:
                        break
                    trials += 1
                    trial = {o: dict(f) for o, f in current.items()}
                    trial[op][field] = candidate
                    trace = execute(dict(base_state), world, trial,
                                    "cover:repair%d" % round_number)
                    if trace is None:
                        continue
                    new_block = failure(trace)
                    if depth(trace) < bg_depth - DEPTH_SLACK:
                        continue          # a diversion, not a repair
                    if new_block is None or new_block > target_block:
                        adopted = (op, field, held, candidate, trace,
                                   new_block)
                        break
                    if new_block < target_block:
                        # Fixing this field broke an earlier one: the
                        # measured conflict the set-cover formulation
                        # would answer. Recorded; not adopted.
                        if len(chain_report["conflicts"]) < 24:
                            chain_report["conflicts"].append(
                                {"field": field,
                                 "value": repr(candidate)[:16],
                                 "regressed_to_block": new_block,
                                 "from_block": target_block})
                        chain_report["conflict_count"] = \
                            chain_report.get("conflict_count", 0) + 1
                if adopted or trials >= MAX_TRIALS_PER_ROUND \
                        or the_budget.left() <= 0:
                    break
            if not adopted and the_budget.left() > 0:
                # Joint repair: no single value passes the field because
                # its edit reads another field too (measured: the single
                # sweep exhausted the evidence). The program publishes
                # cross-field accepting sets as 88 VALUE enumerations on
                # work fields it composes from several inputs; splitting
                # a member across the stalled field and a neighbour is
                # the program's own recipe run backwards. Both fields
                # are assigned - the neighbour takes the member's head,
                # the stalled field its remainder - and the two fill
                # shapes answer the remainder's own class edit.
                owner_fields = [
                    (op2, f2) for op2, held2 in current.items()
                    for f2 in held2
                    if owned.get(f2, set()) & target_arms]
                # The failing field may be one no sweep has owned yet -
                # its arms sit at the frontier, maskable only from
                # inside. The fields still unaccounted for (never owned,
                # never adopted) are exactly the frontier, so pool
                # members are fitted to them first.
                adopted_names = {row["field"]
                                 for row in chain_report["adoptions"]}
                unknown_fields = [
                    (op2, f2) for op2, held2 in current.items()
                    for f2 in held2
                    if f2 not in owned and f2 not in adopted_names]
                solo_trials = 0
                pairs = []
                for op2, field2 in (owner_fields + unknown_fields)[:16]:
                    held2 = str(current[op2][field2])
                    width2 = max(len(held2), index.width(field2) or 1)
                    for parent, combos in joint_pool:
                        if not combos or len(combos[0]) > width2:
                            continue
                        exact = 0 if len(combos[0]) == width2 else 1
                        pairs.append((exact, op2, field2, held2, width2,
                                      parent, combos))
                pairs.sort(key=lambda row: row[0])
                for (_exact, op2, field2, held2, width2, parent,
                     combos) in pairs:
                    if adopted or solo_trials >= 120 \
                            or the_budget.left() <= 0:
                        break
                    step = max(1, len(combos) // 4)
                    for combo in combos[::step][:4]:
                        if adopted or len(combo) > width2:
                            continue
                        pad = width2 - len(combo)
                        fill = ("9" if combo.isdigit() else "A") * pad
                        new_value = combo + fill
                        if new_value == held2:
                            continue
                        solo_trials += 1
                        trial = {o: dict(f)
                                 for o, f in current.items()}
                        trial[op2][field2] = new_value
                        trace = execute(dict(base_state), world, trial,
                                        "cover:pool%d" % round_number)
                        if trace is None:
                            continue
                        new_block = failure(trace)
                        if depth(trace) < bg_depth - DEPTH_SLACK:
                            continue
                        if new_block is None \
                                or new_block > target_block:
                            adopted = (op2, field2, held2, new_value,
                                       trace, new_block)
                            chain_report.setdefault("pool", []).append(
                                {"parent": parent, "value": combo,
                                 "field": field2})
                            break
                if solo_trials:
                    chain_report["pool_trials"] = \
                        chain_report.get("pool_trials", 0) + solo_trials
                neighbours = [
                    (gop, gf) for gop, gheld in current.items()
                    for gf in gheld]
                neighbours.sort(key=lambda pair: min(
                    [abs(block_of[o] - target_block)
                     for o in owned.get(pair[1], ())] or [99]))
                joint_trials = 0
                for op2, field2 in ((owner_fields + unknown_fields)[:8]
                                    or fields[:1]):
                    if adopted:
                        break
                    held2 = str(current[op2][field2])
                    width2 = max(len(held2), index.width(field2) or 1)
                    for parent, combos in joint_pool:
                        for gop, gfield in neighbours[:6]:
                            if adopted or joint_trials >= 80 \
                                    or the_budget.left() <= 0:
                                break
                            if (gop, gfield) == (op2, field2):
                                continue
                            g = str(current[gop][gfield]).strip()
                            wg = index.width(gfield) or len(g)
                            ordered = [v for v in combos
                                       if g and v.startswith(g)]
                            step = max(1, len(combos) // 8)
                            ordered += [v for v in combos[::step]
                                        if v not in ordered]
                            for combo in ordered[:10]:
                                splits = []
                                if g and combo.startswith(g):
                                    splits.append(len(g))
                                if 0 < wg < len(combo):
                                    splits.append(wg)
                                for split in dict.fromkeys(splits):
                                    rem = combo[split:]
                                    if not rem or len(rem) > width2:
                                        continue
                                    pad = width2 - len(rem)
                                    fills = [
                                        ("9" if rem.isdigit() else "A")
                                        * pad, held2[len(rem):]]
                                    for fill in dict.fromkeys(fills):
                                        if adopted or joint_trials >= 80 \
                                                or the_budget.left() <= 0:
                                            break
                                        new_value = rem + fill
                                        new_anchor = combo[:split]
                                        if new_value == held2 \
                                                and new_anchor == g:
                                            continue
                                        joint_trials += 1
                                        trial = {o: dict(f) for o, f
                                                 in current.items()}
                                        trial[op2][field2] = new_value
                                        trial[gop][gfield] = new_anchor
                                        trace = execute(
                                            dict(base_state), world,
                                            trial,
                                            "cover:joint%d" % round_number)
                                        if trace is None:
                                            continue
                                        new_block = failure(trace)
                                        if depth(trace) < bg_depth \
                                                - DEPTH_SLACK:
                                            continue
                                        if new_block is None \
                                                or new_block \
                                                > target_block:
                                            current = {
                                                o: dict(f) for o, f
                                                in current.items()}
                                            current[gop][gfield] = \
                                                new_anchor
                                            adopted = (op2, field2,
                                                       held2, new_value,
                                                       trace, new_block)
                                            chain_report.setdefault(
                                                "joint", []).append(
                                                {"parent": parent,
                                                 "combo": combo,
                                                 "anchor": gfield,
                                                 "anchor_value":
                                                     new_anchor,
                                                 "field": field2,
                                                 "value": new_value})
                                            break
                        if adopted:
                            break
                    if adopted:
                        break
                if joint_trials:
                    chain_report["joint_trials"] = \
                        chain_report.get("joint_trials", 0) + joint_trials
            if not adopted:
                owner = sorted(f for f, arms in owned.items()
                               if arms & target_arms)
                stalled = {
                    "block": target_block,
                    "arms": sorted(target_arms),
                    "conditions": [chain["condition_of"][o]
                                   for o in sorted(target_arms)],
                    "owner_field": owner[0] if owner else None,
                    "candidates_tried": trials,
                    "masked_blocks": sorted(
                        b for b in set(block_of.values())
                        if b > target_block),
                }
                break
            op, field, held, candidate, bg_trace, new_block = adopted
            current = {o: dict(f) for o, f in current.items()}
            current[op][field] = candidate
            chain_report["rounds"] = round_number + 1
            chain_report["adoptions"].append(
                {"field": field, "from": repr(held)[:16],
                 "to": repr(candidate)[:16],
                 "failure_moved": [target_block, new_block]})
            # The repaired field's own faces are expressible exactly now:
            # spoil it every way over the new background. Every few
            # rounds a full sweep keeps ownership current with the
            # deeper window (and harvests arms the jump unmasked).
            if round_number % 4 == 3:
                sweep(current, bg_trace, "cover:harvest%d" % round_number)
            else:
                sweep({op: {field: current[op][field]}}, bg_trace,
                      "cover:face%d" % round_number)

        # Equality mirror: a chain arm that judges sameness (the
        # no-change message-88, a key match) compares this cycle's
        # values against operation-delivered state, and no single-field
        # value can force equality - but the failing guard's own
        # observed operands say exactly what each side held. Every
        # var-vs-var comparison whose one side has a stub route (a
        # direct stub write, or one MOVE from a stub-written field)
        # gets that side staged to the other side's observed value;
        # fixpoint over a few credited runs, values propagating one
        # delivery per round. The construction is `chain._mirror_pairs`
        # made concrete by the trace.
        from .chain import _stub_writers, _writers
        from .ir import parse_term
        names_table = frozenset(index.model.condition_names or ())
        mirror_rounds = 0
        mirror_trace = bg_trace
        for _mirror in range(3):
            if mirror_trace is None or the_budget.left() <= 0:
                break
            staged: dict = {}
            for g in mirror_trace.guards:
                if not g.values:
                    continue
                try:
                    groups = condition_atoms(str(g.condition or ""),
                                             names=names_table)
                except Exception:                            # noqa: BLE001
                    continue
                for group in groups:
                    for atom in group:
                        lhs, rhs = atom.lhs, atom.rhs
                        if getattr(lhs, "kind", "") != "var" \
                                or getattr(rhs, "kind", "") != "var":
                            continue
                        for side_x, side_y in ((lhs, rhs), (rhs, lhs)):
                            X = str(side_x.name).upper()
                            Y = str(side_y.name).upper()
                            value = g.values.get(Y)
                            if value is None or value == "":
                                value = g.values.get(Y.split(" OF ")[0])
                            if value is None or value == "":
                                continue
                            head = X.split(" OF ")[0]
                            for w in _stub_writers(prov, head):
                                staged.setdefault(w.op_key, {}) \
                                    .setdefault(head, value)
                                break
                            else:
                                for w in _writers(prov, head):
                                    if w.kind != "MOVE" \
                                            or not getattr(w, "source",
                                                           None):
                                        continue
                                    try:
                                        src = parse_term(w.source)
                                    except Exception:      # noqa: BLE001
                                        continue
                                    if src.kind != "var" or src.refmod:
                                        continue
                                    src_head = str(src.name).upper() \
                                        .split(" OF ")[0]
                                    stubs_of = _stub_writers(prov,
                                                             src_head)
                                    if stubs_of:
                                        staged.setdefault(
                                            stubs_of[0].op_key, {}) \
                                            .setdefault(src_head, value)
            if not staged:
                break
            mirror_rounds += 1
            mirrored = _merge_stubs(staged, current)
            mirror_trace = execute(dict(base_state), world, mirrored,
                                   "cover:mirror%d" % mirror_rounds)
        if mirror_rounds:
            chain_report["mirror_rounds"] = mirror_rounds

        # The finished background under every other base: a different
        # attention key routes the confirm cycle (fetch, edit, save)
        # that no screen byte can reach - the green screen is what makes
        # the confirm path's edits all pass on the way there.
        for extra_state, extra_world in bases:
            if extra_state == base_state and extra_world == world:
                continue
            execute(dict(extra_state), extra_world, current,
                    "cover:final-base")

        # Final full harvest over the deepest background achieved.
        sweep(current, bg_trace, "cover:final", kinds_cap=None)
        # Missing faces retry: any arm still unwitnessed whose block has
        # a measured owner gets every spoil kind of that owner tried
        # once more over the final background (cheap, bounded).
        witnessed_now = ledger.covered() | set(baseline or ())
        for ordinal in chain["ordinals"]:
            if the_budget.left() <= 0:
                break
            key = (para, ordinal, "WHEN", True)
            if key in witnessed_now or ordinal in other:
                continue
            owners = [f for f, arms in owned.items() if ordinal in arms]
            for field in owners[:2]:
                for op, held in current.items():
                    if field not in held:
                        continue
                    for _op, _field, kind, value in _spoil_family(
                            index, {op: {field: current[op][field]}}):
                        spoiled = {o: dict(f) for o, f in current.items()}
                        spoiled[op][field] = value
                        execute(dict(base_state), world, spoiled,
                                "cover:retry:%s:%s" % (ordinal, kind))

        if stalled:
            # Count what the blocker actually masks: unwitnessed arms in
            # blocks strictly deeper than the stall.
            witnessed_now = ledger.covered() | set(baseline or ())
            masked = [o for o in chain["ordinals"]
                      if block_of[o] > stalled["block"]
                      and (para, o, "WHEN", True) not in witnessed_now]
            stalled["masked_arms"] = masked
            stalled["masked_count"] = len(masked)
            chain_report["blockers"].append(stalled)

        # Arm-by-arm accounting for this chain.
        witnessed_now = ledger.covered() | set(baseline or ())
        accounting = []
        for ordinal in chain["ordinals"]:
            key = (para, ordinal, "WHEN", True)
            if key in witnessed_now:
                status = "witnessed" if key in have_before else "witnessed-new"
            elif stalled and block_of[ordinal] > stalled["block"]:
                status = "blocked:%s" % (stalled["owner_field"]
                                         or "block-%d" % stalled["block"])
            elif stalled and block_of[ordinal] == stalled["block"]:
                status = "blocker-arm"
            else:
                status = "unwitnessed"
            accounting.append({"ordinal": ordinal,
                               "condition": chain["condition_of"][ordinal],
                               "status": status})
        chain_report["accounting"] = accounting
        chain_report["arms_witnessed_before"] = sum(
            1 for o in chain["ordinals"]
            if (para, o, "WHEN", True) in have_before)
        chain_report["arms_witnessed_after"] = sum(
            1 for o in chain["ordinals"]
            if (para, o, "WHEN", True) in witnessed_now)

    report["runs"] = the_budget.spent
    return {"report": report, "ledger": ledger}
