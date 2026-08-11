"""The toolbox an agent drives. Every subcommand is deterministic."""

from __future__ import annotations

import argparse
import json
import os
import sys

from .cobol import load_program
from .graph import build_graph, depths, shortest_chain
from .interpreter import verify
from .journal import Journal
from .ladder import build_plan
from .provenance import Provenance


def _program(args):
    pack = getattr(args, "conventions", None)
    if pack:
        from .heuristics import load_pack
        load_pack(pack)
    return load_program(args.program, args.copybooks)


def _entry(program, args) -> str:
    return (args.entry or program.paragraph_names[0]).upper()


def _capability(args, program=None):
    """What the harness says it can do, or a proxy, or nothing stated.

    Nothing stated is the default and means "no constraints", which is the
    behaviour every command had before profiles existed. A proxy is derived
    from the source and is labelled as one wherever it is used, because a
    figure measured against a guess about a harness is a figure about the
    guess.
    """
    from .capability import Capability, load
    path = getattr(args, "capability", None)
    if path:
        return load(path), "stated"
    proxy = getattr(args, "proxy", None)
    if proxy and program is not None:
        from .represent import proxy_profile
        return proxy_profile(program, fields=proxy,
                             max_outcomes=getattr(args, "max_outcomes", 0) or 0), \
            "proxy:%s" % proxy
    return Capability(), "none"


def _via(args) -> list:
    return [w.strip().upper() for w in (args.via or "").split(",") if w.strip()]


def _binds(args, journal, target) -> dict:
    out = journal.bindings(target)
    for item in args.bind or []:
        name, _, value = item.partition("=")
        out[name.strip().upper()] = _coerce(value.strip())
    return out


def _terminals(args) -> dict:
    """--terminal OP:VAR=VALUE, the value a stub returns once its planned
    outcomes run out. Read loops need one or they never end."""
    out: dict = {}
    for item in getattr(args, "terminal", None) or []:
        head, _, value = item.partition("=")
        op, _, var = head.rpartition(":")
        if op and var:
            out.setdefault(op.upper(), {})[var.upper()] = _coerce(value.strip())
    return out


def _defaults(args) -> dict:
    """--default OP:VAR=VALUE, used when no planned outcome matches a call."""
    out: dict = {}
    for item in getattr(args, "default", None) or []:
        head, _, value = item.partition("=")
        op, _, var = head.rpartition(":")
        if op and var:
            out.setdefault(op.upper(), {})[var.upper()] = _coerce(value.strip())
    return out


def _coerce(text: str):
    if text.startswith(("'", '"')) and text.endswith(("'", '"')):
        return text[1:-1]
    try:
        return int(text)
    except ValueError:
        pass
    try:
        return float(text)
    except ValueError:
        return text


def _emit(payload, as_json: bool, render):
    if as_json:
        print(json.dumps(payload, indent=2, default=str))
    else:
        render(payload)
    return payload


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------

def cmd_frames(args):
    """What is reachable, how deep, and how heavily guarded."""
    program = _program(args)
    graph = build_graph(program)
    entry = _entry(program, args)
    dist = depths(graph, entry)
    rows = []
    for name in program.paragraph_names:
        chain = shortest_chain(graph, entry, name)
        if name == entry:
            rows.append({"paragraph": name, "depth": 0, "guards": 0, "edges": []})
            continue
        if chain is None:
            continue
        rows.append({
            "paragraph": name,
            "depth": len(chain),
            "guards": sum(len(s.guards) for s in chain),
            "edges": [s.kind for s in chain],
        })
    rows.sort(key=lambda r: (-r["guards"], -r["depth"], r["paragraph"]))
    if args.limit:
        rows = rows[: args.limit]
    payload = {"program": program.name, "entry": entry,
               "paragraphs": len(program.paragraph_names),
               "reachable": len(dist), "frames": rows}

    def render(p):
        print("%s   entry %s   %d/%d paragraphs reachable"
              % (p["program"], p["entry"], p["reachable"], p["paragraphs"]))
        print("%-34s %6s %7s  %s" % ("paragraph", "depth", "guards", "edges"))
        for r in p["frames"]:
            print("%-34s %6d %7d  %s"
                  % (r["paragraph"], r["depth"], r["guards"], ",".join(r["edges"])))
    return _emit(payload, args.json, render)


def cmd_trace(args):
    """The call trace to a target, frame by frame, with each frame's guards."""
    program = _program(args)
    graph = build_graph(program)
    entry = _entry(program, args)
    from .graph import chain_via
    via = _via(args)
    chain = (chain_via(graph, entry, via, args.target.upper()) if via
             else shortest_chain(graph, entry, args.target.upper()))
    if chain is None:
        payload = {"error": "no chain", "entry": entry, "target": args.target}
        return _emit(payload, args.json, lambda p: print("no chain from %s to %s"
                                                         % (entry, args.target)))
    payload = {
        "entry": entry, "target": args.target.upper(),
        "frames": [{"caller": s.caller, "callee": s.callee, "line": s.line,
                    "edge": s.kind,
                    "guards": [{"atom": str(a), "origin": a.origin} for a in s.guards]}
                   for s in chain],
        "depth": len(chain),
        "total_guards": sum(len(s.guards) for s in chain),
    }

    def render(p):
        print("%s  ->  %s     depth %d, %d guards"
              % (p["entry"], p["target"], p["depth"], p["total_guards"]))
        for f in p["frames"]:
            print("\n  %s --%s--> %s   (line %d)"
                  % (f["caller"], f["edge"], f["callee"], f["line"]))
            for g in f["guards"]:
                print("      requires  %-44s [%s]" % (g["atom"], g["origin"]))
    return _emit(payload, args.json, render)


def cmd_plan(args):
    program = _program(args)
    journal = Journal(args.work_dir)
    target = args.target.upper()
    capability, _source = _capability(args, program)
    plan = build_plan(program, target, entry=args.entry, via=_via(args),
                      agent_bindings=_binds(args, journal, target),
                      capability=capability)
    payload = plan.to_dict()
    # A plan that cannot be replayed is not a failure of the derivation, and
    # it is not a reason to withhold it either - it is a fact the caller has
    # to know before spending a run on it.
    from .capability import unrepresentable
    payload["unrepresentable"] = unrepresentable(plan, capability)

    def render(p):
        print("target  %s" % p["target"])
        if p["unrepresentable"]:
            print("NOT REPRESENTABLE by the stated harness:")
            for reason in p["unrepresentable"]:
                print("   %s" % reason)
        print("chain   %s" % " -> ".join(p["chain"]))
        print("edges   %s" % ",".join(p["edges"]))
        print("\nobligations lifted (%d)" % len(p["obligations"]))
        for o in p["obligations"]:
            print("   %-46s [%s]" % (o["atom"], o["origin"]))
        if p["derived"]:
            print("\nderived by guard avoidance (%d)" % len(p["derived"]))
            for d in p["derived"]:
                print("   %-46s %s" % (d["atom"], d["why"]))
        print("\nbindings (%d)" % len(p["bindings"]))
        for b in p["bindings"]:
            mark = " <agent>" if b["source"] == "agent" else ""
            print("   %-46s := %r%s" % (b["slot"], b["value"], mark))
            print("        %s" % b["reason"])
            if b["provenance"]:
                print("        provenance: %s%s" % (" <- ".join(b["provenance"]),
                                                    "   (inferred)" if b["inferred"] else ""))
        if p["rendezvous"]:
            print("\nrendezvous couplings (%d)" % len(p["rendezvous"]))
            for r in p["rendezvous"]:
                print("   %s\n     == %s\n     both := %r"
                      % (r["left"], r["right"], r["value"]))
        print("\nopen obligations (%d)" % len(p["open"]))
        for o in p["open"]:
            print("   %-46s %s" % (o["atom"], o["why"]))
        print("\nstate: %s" % json.dumps(p["flat_state"], default=str))
        print("solved: %s" % p["solved"])
    return _emit(payload, args.json, render)


def cmd_verify(args):
    program = _program(args)
    journal = Journal(args.work_dir)
    target = args.target.upper()
    entry = _entry(program, args)
    plan = build_plan(program, target, entry=args.entry, via=_via(args),
                      agent_bindings=_binds(args, journal, target))
    extra = _terminals(args)
    merged = dict(plan.terminals)
    for op, vals in extra.items():
        merged.setdefault(op, {}).update(vals)
    result = verify(program, plan, entry, terminals=merged,
                    defaults=_defaults(args),
                    repeat=getattr(args, "stub_repeat", 1) or 1)
    result["terminals"] = merged
    result["open_obligations"] = [{"atom": str(a), "why": w}
                                  for a, w in plan.open_obligations]
    result["state"] = plan.flat_state()
    journal.append("verify", target=target, reached=result["reached"],
                   state=plan.flat_state(),
                   first_missing=result["first_missing_frame"])

    def render(p):
        status = "REACHED" if p["reached"] else "NOT REACHED"
        print("%s   %s -> %s" % (status, p["entry"], p["target"]))
        print("chain      %s" % " -> ".join(p["chain"]))
        print("of which   %s" % " -> ".join(p["chain_reached"]))
        print("steps %d, %d paragraphs entered%s"
              % (p["steps"], p["paragraphs_entered"],
                 ", stopped: " + p["stopped"] if p["stopped"] else ""))
        if p["open_obligations"]:
            print("\nopen obligations (%d)" % len(p["open_obligations"]))
            for o in p["open_obligations"]:
                print("   %-46s %s" % (o["atom"], o["why"]))
        if not p["reached"]:
            print("\nfirst frame not entered: %s" % p["first_missing_frame"])
            if p["blocking_guards"]:
                print("guards on the chain that went the wrong way:")
                for g in p["blocking_guards"]:
                    print("   %s:%d  %s  %s" % (g["paragraph"], g["line"],
                                                g["kind"], g["condition"]))
                    print("        actual: %s" % json.dumps(g["values"], default=str))
        if p.get("external_calls"):
            print("external calls: %s" % json.dumps(p["external_calls"]))
        if p["approximations"]:
            print("\ninterpreter approximations: %s" % "; ".join(p["approximations"]))
    return _emit(payload := result, args.json, render)


def cmd_explain(args):
    """Everything about one frame an agent needs in order to decide."""
    program = _program(args)
    graph = build_graph(program)
    from .graph import execution_order
    prov = Provenance(program, execution_order(graph, program.paragraph_names[0]))
    frame = args.frame.upper()
    para = program.paragraph(frame)
    if para is None:
        return _emit({"error": "no such paragraph", "frame": frame}, args.json,
                     lambda p: print("no such paragraph: %s" % frame))

    variables = {}
    for name in (args.variables or "").split(","):
        name = name.strip().upper()
        if not name:
            continue
        producer = prov.producer(name)
        variables[name] = {
            "kind": producer.kind, "slot": producer.slot,
            "op_key": producer.op_key, "site": producer.site,
            "when": producer.discriminators, "inferred": producer.inferred,
            "provenance": list(producer.trace),
            "pic": program.model.pic.get(name),
            "literals_compared_against": sorted(prov.literals.get(name, set()),
                                                key=repr),
            "writers": [{"paragraph": w.para, "line": w.line, "kind": w.kind,
                         "source": w.source, "conditional": w.conditional,
                         "guards": [str(g) for g in w.guards]}
                        for w in prov.writes_to(name)][:12],
        }

    source = prov.frame_source(frame)
    payload = {"frame": frame, "line_start": para.get("line_start"),
               "line_end": para.get("line_end"),
               "callees": [s.callee for s in graph.get(frame, [])],
               "variables": variables,
               "source": [{"line": n, "text": t} for n, t in source]
               if args.source else []}

    def render(p):
        print("frame %s   lines %s-%s" % (p["frame"], p["line_start"], p["line_end"]))
        print("calls: %s" % ", ".join(p["callees"]) or "(none)")
        for name, info in p["variables"].items():
            print("\n%s   pic=%s" % (name, info["pic"]))
            print("   producer: %s  (%s)%s" % (info["slot"], info["kind"],
                                               "  INFERRED" if info["inferred"] else ""))
            if info["provenance"]:
                print("   provenance: %s" % " <- ".join(info["provenance"]))
            if info["literals_compared_against"]:
                print("   compared against: %s"
                      % ", ".join(repr(v) for v in info["literals_compared_against"]))
            for w in info["writers"]:
                print("   written %s:%d %s %s%s"
                      % (w["paragraph"], w["line"], w["kind"], w["source"][:40],
                         "   [guarded: %s]" % "; ".join(w["guards"]) if w["conditional"] else ""))
        if p["source"]:
            print("\nsource:")
            for row in p["source"]:
                print("%6d  %s" % (row["line"], row["text"]))
    return _emit(payload, args.json, render)


def _constraint_of(binding):
    """The comparison a binding had to satisfy, if it was against a constant."""
    atom = binding.atom
    if atom is None:
        return None, None
    if atom.rhs.kind == "const":
        return atom.op, atom.rhs.value
    if atom.lhs.kind == "const":
        from .ir import flip
        return flip(atom.op), atom.lhs.value
    return None, None


def cmd_coverage(args):
    """What a whole plan set exercises, and what it leaves untouched."""
    program = _program(args)
    journal = Journal(args.work_dir)
    from .coverage import empty as _empty_coverage, missing
    from .interpreter import Interpreter
    from .ladder import analyse, build_family
    from .learned import Learned
    from .provenance import Provenance
    from .conformance_defaults import io_defaults, WORLDS
    _graph, prov = analyse(program)
    entry = _entry(program, args)
    known = journal.bindings()

    learned = Learned(args.learn)
    # Values that have worked before are offered as *preferences*, so they
    # are taken where the ladder has a free choice and ignored where a
    # constraint decides. A warm dictionary can therefore only help.
    warm = {name: learned.best(name) for name in learned.fields
            if learned.best(name) is not None}
    seen_directions: set = set()

    # Folded as they arrive rather than kept. See `coverage.Coverage.observe`.
    cov = _empty_coverage(program)

    def record(trace) -> None:
        if trace is not None:
            cov.observe(trace)

    # A whole-program sweep is linear in decisions and each run is linear in
    # the program, so the work is quadratic in the source and there is a size
    # past which "it finishes" stops being true. A budget makes the run
    # bounded and, more importantly, makes what it did not get to *reported*
    # rather than silently missing. Off by default: with no budget the run is
    # a function of the program alone, which is the invariant everywhere else.
    import time as _time
    deadline = (_time.monotonic() + args.time_budget) if args.time_budget else None
    stopped: dict = {}

    def out_of_time(stage: str, done: int, total: int) -> bool:
        if deadline is None or _time.monotonic() < deadline:
            return False
        stopped.setdefault("reason", "time-budget")
        stopped.setdefault("seconds", args.time_budget)
        stopped.setdefault("stages", {})[stage] = "%d/%d" % (done, total)
        return True

    def run_plan(plan, world="bare"):
        """Run it, and remember the values if it covered anything new."""
        interp = Interpreter(program, plan.input_state(),
                             stubs=plan.stub_plan(), terminals=plan.terminals,
                             defaults=io_defaults(program, world))
        try:
            trace = interp.run(entry)
        except Exception:                                    # noqa: BLE001
            return None
        fresh = {(g.paragraph, g.ordinal, g.kind, bool(g.result))
                 for g in trace.guards} - seen_directions
        seen_directions.update(fresh)
        if args.learn:
            learned.record(plan.flat_state(), len(fresh))
        return trace

    import random as _random
    _rng = _random.Random(args.seed)

    # Loaded here, not inside the `--branches` block: the payload below reads
    # it unconditionally, so scoping it to one branch of the command left
    # plain `coverage`, `coverage --sample N` and `--lift-only` raising
    # UnboundLocalError. A profile is a property of the run, not of one stage.
    from .capability import load as _load_capability, unrepresentable
    capability = _load_capability(getattr(args, "capability", None))
    # Resolved against this program, never read as raw ordinals: the harness
    # and this tool number decisions differently, and taking the number at
    # face value pointed 1,251 of 1,644 targets on the CardDemo corpus at a
    # decision nobody asked for. See `directions`.
    resolution = capability.resolve_uncovered(program)
    wanted = resolution.wanted
    skipped_covered = skipped_unrepresentable = 0

    # The value pool, built once. Every literal the program compares a field
    # against, plus one value it compares against nothing - without the
    # complement a field tested only for SPACES has a single reachable state
    # here and the negative direction of its own comparison is unsamplable.
    from .heuristics import complement_value
    pool: dict = {}
    for name, values in prov.literals.items():
        if not values:
            continue
        ordered = sorted(values, key=repr)
        other = complement_value(name, program.model.pic_of(name), ordered)
        if other is not None:
            ordered = ordered + [other]
        pool[name] = ordered

    # An operation returns a sequence, and until now no world could say so:
    # every READ got one status for the whole run, so every iteration of a
    # read loop processed the same record. These worlds deliver N records with
    # rotating payloads and then end-of-file, which is the shape a batch
    # program is written against.
    from .sequences import sequence_worlds, fault_worlds
    sequences = []
    if getattr(args, "sequences", 0):
        sequences = sequence_worlds(
            program, prov, prov.literals,
            lengths=tuple(range(1, args.sequences + 1)))
        # "The third record is the one that fails" is an outcome list and
        # nothing else can express it: a world that names one status per
        # operation can only make the lookup fail on every record, which is a
        # different route through the program.
        sequences += fault_worlds(program, prov, prov.literals,
                                  length=args.sequences,
                                  codes=args.fault_codes)

    lift_stats = None
    # Every derived plan is a place the frontier search can start from, and
    # the two reach different things: derivation gets past a guard the search
    # would have to arrive at first, and the search extends a plan past the
    # point where the program overwrites it. Seeding one with the other is
    # cheap - the plans are being built anyway - and it is the only way the
    # search can begin inside a world where a file has already ended.
    lift_seeds = [({}, w, None, None) for w in WORLDS]
    # A sequence is a seed as much as a plan is: it puts the run somewhere no
    # entry state can reach on its own - past the end of a file that returned
    # three records first - and the frontier search then solves the guards it
    # finds there.
    for world in sequences:
        lift_seeds.append(({}, world["world"], world["stubs"],
                           world["terminals"]))

    if args.lift_only:
        args.branches = False
        args.sample = 0

    if args.branches:
        # One plan per decision *direction*, which is what the metric counts.
        from .coverage import branches_of
        from .ladder import plan_for_branch
        for b in branches_of(program):
            for direction in (True, False):
                # The harness's own work list, when it supplied one. Planning
                # for a direction it has already covered spends the budget on
                # something that cannot pay - measured on one integration,
                # every plan that survived to execution landed on covered
                # code.
                if wanted and (b.paragraph.upper(), b.ordinal, b.kind.upper(),
                               bool(direction)) not in wanted:
                    skipped_covered += 1
                    continue
                try:
                    plan = plan_for_branch(program, b.paragraph, b.line,
                                           direction, entry=args.entry,
                                           agent_bindings=known,
                                           preferred=warm,
                                           max_routes=args.routes,
                                           ordinal=b.ordinal)
                except Exception:                            # noqa: BLE001
                    continue
                if not plan.chain:
                    continue
                # A binding the harness cannot inject is a value it will drop
                # in projection, and the plan then runs meaning nothing. Far
                # better to know here, where it costs one comparison, than
                # after the program has been compiled and run.
                blocked = unrepresentable(plan, capability)
                if blocked:
                    skipped_unrepresentable += 1
                    continue
                for world in WORLDS:
                    record(run_plan(plan, world))
                if args.lift:
                    lift_seeds.append((plan.input_state(), "bare",
                                       plan.stub_plan(), plan.terminals))
                # A plan pins only the slots its obligations reached; the rest
                # keep whatever the defaults give, identically on every run.
                # Overlaying the free slots costs nothing the plan cares about
                # and is what lets a harvested literal actually be tried.
                fixed = plan.input_state()
                for _ in range(args.overlays):
                    state = {n: _rng.choice(v) for n, v in pool.items()
                             if n not in fixed}
                    state.update(fixed)
                    interp = Interpreter(program, state,
                                         stubs=plan.stub_plan(),
                                         terminals=plan.terminals,
                                         defaults=io_defaults(program, "bare"))
                    try:
                        record(interp.run(entry))
                    except Exception:                        # noqa: BLE001
                        continue
            # The inner loop broke on the budget, so break the outer one too.
            else:
                continue
            break

    if args.sample:
        # Deliberate hybrid. Backward derivation reaches guards that sampling
        # never will; sampling reaches statements whose obligations the ladder
        # cannot lift at all. Measured on COACTUPC the two sets differ by
        # ~100 directions each way, and the literature on directed symbolic
        # execution reports the same: mixing beats either pure strategy.
        for _ in range(args.sample):   # noqa: B007  - _ selects the world
            if out_of_time("sample", _, args.sample):
                break
            state = {name: _rng.choice(values) for name, values in pool.items()}
            interp = Interpreter(program, state,
                                 defaults=io_defaults(program,
                                                      WORLDS[_ % len(WORLDS)]))
            try:
                record(interp.run(entry))
            except Exception:                                # noqa: BLE001
                continue

    # The sequences, run on their own. A seed only pays off if the frontier
    # search is on; these runs are what makes the mechanism measurable
    # without it, and they are the whole of what a plain `coverage` gains.
    for world in sequences:
        states = [{}] + [{n: _rng.choice(v) for n, v in pool.items()}
                         for _ in range(max(0, args.overlays))]
        for state in states:
            interp = Interpreter(program, state, stubs=world["stubs"],
                                 terminals=world["terminals"],
                                 defaults=io_defaults(program, world["world"]))
            try:
                record(interp.run(entry))
            except Exception:                                # noqa: BLE001
                continue

    paragraph_targets = [] if args.lift_only else program.paragraph_names[1:]
    for _index, target in enumerate(paragraph_targets):
        if out_of_time("paragraph_targets", _index, len(paragraph_targets)):
            break
        plans = []
        if args.families:
            plans = [m["plan"] for m in
                     build_family(program, target, entry=args.entry,
                                  limit=args.families)]
        if not plans:
            plan = build_plan(program, target, entry=args.entry,
                              agent_bindings=known, preferred=warm)
            plans = [plan] if plan.chain else []
        for plan in plans:
            for world in WORLDS:
                record(run_plan(plan, world))

    if args.lift:
        from .lift import lift as _lift
        result = _lift(program, entry, seeds=lift_seeds,
                       defaults_for=lambda w: io_defaults(program, w),
                       budget=args.lift, fanout=args.lift_fanout,
                       on_trace=record,
                       should_stop=(None if deadline is None else
                                    lambda: out_of_time("frontier", 0, args.lift)))
        lift_stats = result["stats"]
        for trace in result["traces"]:
            seen_directions.update((g.paragraph, g.ordinal, g.kind,
                                    bool(g.result)) for g in trace.guards)

    if args.learn:
        learned.save()
    gaps = missing(program, cov)
    payload = dict(cov.summary())
    payload.update({
        "program": program.name, "entry": entry,
        "learned": learned.summary() if args.learn else None,
        "lift": lift_stats,
        "capability": ({"targets_skipped_already_covered": skipped_covered,
                        "plans_skipped_unrepresentable": skipped_unrepresentable,
                        "work_list": resolution.summary()}
                       if capability.stated else None),
        "stopped_early": stopped or None,
        "unreached_paragraphs": gaps["paragraphs"],
        "untouched_branches": [{"paragraph": b.paragraph, "line": b.line,
                                "kind": b.kind, "ordinal": b.ordinal,
                                "condition": b.condition}
                               for b in gaps["untouched"]],
        "one_way_only": [{"paragraph": b.paragraph, "line": b.line,
                          "kind": b.kind, "ordinal": b.ordinal,
                          "condition": b.condition, "only": went}
                         for b, went in gaps["one_way_only"]],
    })

    # The still-uncovered directions, in the shape `--capability` reads. A
    # sweep that had to stop is only useful if the next one can pick up where
    # it left off, and the work list is what carries that across: run two of
    # the same command with `--capability` plans the directions run one did
    # not reach and skips the ones it did.
    if args.work_list:
        # `condition` and `line` travel with every entry because they are the
        # only identity a *different* tool can match on - the ordinal is this
        # one's own statement numbering and means nothing outside it.
        work = [{"paragraph": b.paragraph, "ordinal": b.ordinal,
                 "kind": b.kind, "direction": d, "condition": b.condition,
                 "line": b.line}
                for b in gaps["untouched"] for d in (True, False)]
        work += [{"paragraph": b.paragraph, "ordinal": b.ordinal,
                  "kind": b.kind, "direction": not went,
                  "condition": b.condition, "line": b.line}
                 for b, went in gaps["one_way_only"]]
        # Only when the run was cut short: a run that finished tried
        # everything, so holding its failures back would leave a work list
        # that says there is nothing left to do.
        deferred = 0
        if stopped and attempted:
            fresh = [d for d in work
                     if (d["paragraph"].upper(), d["ordinal"],
                         d["kind"].upper(), d["direction"]) not in attempted]
            deferred = len(work) - len(fresh)
            work = fresh
        with open(args.work_list, "w") as fh:
            json.dump({"schema_version": "1.0", "program": program.name,
                       # Our own ordinals, so the next run may use them as an
                       # identity. Any profile without this stamp is matched
                       # on text instead.
                       "ordinal_source": "frameladder",
                       "uncovered_directions": work}, fh, indent=1)
        payload["work_list"] = {"path": args.work_list, "directions": len(work),
                                "held_back_already_attempted": deferred}

    def render(p):
        print("%s   %d runs" % (p["program"], p["runs"]))
        if p["step_capped_runs"]:
            # Worth its own line rather than a footnote: a program whose runs
            # end on the statement budget has an upper bound on coverage that
            # no amount of planning can lift, and the number that is stuck is
            # not the planner's.
            print("  step-capped %d of %d runs stopped on the statement budget"
                  % (p["step_capped_runs"], p["runs"]))
        print("  paragraphs %-12s %5.1f%%" % (p["paragraphs"], p["paragraph_pct"]))
        print("  directions %-12s %5.1f%%" % (p["directions"], p["direction_pct"]))
        if p.get("learned"):
            print("  dictionary %s" % json.dumps(p["learned"]))
        if p.get("lift"):
            print("  frontier   %s" % json.dumps(p["lift"]))
        if p.get("stopped_early"):
            print("  STOPPED    %s" % json.dumps(p["stopped_early"]))
        if p.get("work_list"):
            print("  work list  %s" % json.dumps(p["work_list"]))
        if p["unreached_paragraphs"]:
            print("\nnever entered (%d): %s"
                  % (len(p["unreached_paragraphs"]),
                     ", ".join(p["unreached_paragraphs"][:10])))
        if p["untouched_branches"]:
            print("\nnever evaluated (%d):" % len(p["untouched_branches"]))
            for b in p["untouched_branches"][: args.limit]:
                print("   %s:%d %-5s %s" % (b["paragraph"], b["line"],
                                            b["kind"], b["condition"][:60]))
        if p["one_way_only"]:
            print("\nonly ever went one way (%d):" % len(p["one_way_only"]))
            for b in p["one_way_only"][: args.limit]:
                print("   %s:%d %-5s %-46s always %s"
                      % (b["paragraph"], b["line"], b["kind"],
                         b["condition"][:46], b["only"]))
    return _emit(payload, args.json, render)


def cmd_names(args):
    """Sweep this program's own vocabulary, rather than assume a prior one.

    A fixed token table is a guess about how other people name things, and
    programs are not consistent enough for that to hold. What *is* consistent
    is a single program: it was written by a team with one convention, so the
    convention is discoverable from the source. This lists the tokens that
    actually occur, weighted by how many undecided values each would settle,
    so one pass of judgment covers the program instead of one field at a time.
    """
    program = _program(args)
    journal = Journal(args.work_dir)
    from .ladder import analyse
    from .heuristics import from_evidence
    _graph, prov = analyse(program)
    entry = _entry(program, args)
    known = journal.bindings()

    undecided: dict = {}
    for target in program.paragraph_names[1:]:
        try:
            plan = build_plan(program, target, entry=args.entry,
                              agent_bindings=known)
        except Exception:                                    # noqa: BLE001
            continue
        for b in plan.bindings:
            var = b.producer.var
            if not b.free or var in known:
                continue
            pic = program.model.pic.get(var, "")
            op, other = _constraint_of(b)
            if from_evidence(prov.literals.get(var, ()), pic, op, other) is not None:
                continue
            undecided.setdefault(var, pic)

    def described(var: str) -> str:
        """PIC alone is not the type. USAGE decides the representation, and a
        REDEFINES means the bytes are shared with something else."""
        model = program.model
        parts = [model.pic.get(var) or "(no PIC)"]
        usage = model.usage.get(var)
        if usage:
            parts.append(usage)
        if model.sign.get(var):
            parts.append("SIGN " + model.sign[var])
        if model.occurs.get(var):
            parts.append("OCCURS %d" % model.occurs[var])
        if model.redefines.get(var):
            parts.append("REDEFINES " + model.redefines[var])
        return " ".join(parts)

    groups: dict = {}
    for var, _pic in undecided.items():
        for token in var.split("-"):
            if len(token) < 2 or token.isdigit():
                continue
            entry_ = groups.setdefault(token, {"fields": [], "types": set(),
                                               "origins": set()})
            entry_["fields"].append(var)
            entry_["types"].add(described(var))
            entry_["origins"].add(program.model.origin.get(var, "(undeclared)"))

    rows = sorted(({"token": t, "fields": sorted(v["fields"]),
                    "types": sorted(v["types"]),
                    "declared_in": sorted(v["origins"]),
                    "count": len(v["fields"])}
                   for t, v in groups.items()),
                  key=lambda r: (-r["count"], r["token"]))
    if args.limit:
        rows = rows[: args.limit]
    payload = {"program": program.name, "entry": entry,
               "copybooks": list(program.model.copybooks),
               "undecided_fields": len(undecided), "tokens": rows}

    def render(p):
        print("%s: %d values the program never pins down, sharing %d tokens."
              % (p["program"], p["undecided_fields"], len(p["tokens"])))
        print("copybooks read: %s\n"
              % (", ".join(p["copybooks"]) or "(none COPYed)"))
        print("%-14s %6s  %-30s %-18s %s"
              % ("token", "fields", "type", "declared in", "examples"))
        for r in p["tokens"]:
            print("%-14s %6d  %-30s %-18s %s"
                  % (r["token"], r["count"], "; ".join(r["types"][:1])[:30],
                     ",".join(r["declared_in"][:1])[:18],
                     ", ".join(r["fields"][:2])))
        print("\nDecide a token once and it settles every field carrying it:")
        print("  frameladder %s --work-dir DIR bind --bind \"<FIELD>=<value>\" "
              "--why \"...\"" % args.program)
    return _emit(payload, args.json, render)


def cmd_questions(args):
    """The slots where the tool would have to invent a value, so it asks.

    A naming table is a guess about how other people name things, and it
    measured as worth zero targets. What a value should be, where the
    program itself never says, is a judgment - so it is put to whoever is
    driving, once, and recorded. After that it is data like any other.
    """
    program = _program(args)
    journal = Journal(args.work_dir)
    from .ladder import analyse
    from .heuristics import from_evidence
    _graph, prov = analyse(program)
    entry = _entry(program, args)
    known = journal.bindings()

    targets = ([args.target.upper()] if args.target
               else program.paragraph_names[1:])
    asked, seen = [], set()
    for target in targets:
        plan = build_plan(program, target, entry=args.entry,
                          agent_bindings=known)
        if not plan.chain:
            continue
        for b in plan.bindings:
            var = b.producer.var
            if not b.free or var in seen or var in known:
                continue
            pic = program.model.pic.get(var, "")
            evidence = sorted(prov.literals.get(var, ()), key=repr)
            op, other = _constraint_of(b)
            if from_evidence(evidence, pic, op, other) is not None:
                continue
            seen.add(var)
            asked.append({
                "variable": var, "pic": pic or "(undeclared)",
                "constraint": str(b.atom) if b.atom else "(free)",
                "origin": b.atom.origin if b.atom else "",
                "chose": b.value, "target": target,
                "slot": b.slot, "evidence": evidence,
            })
    if args.limit:
        asked = asked[: args.limit]
    payload = {"program": program.name, "entry": entry, "questions": asked}

    def render(p):
        if not p["questions"]:
            print("Nothing to ask: every free value came from the program.")
            return
        print("%d values the program never pins down. It currently invents "
              "these; decide them once and they are recorded.\n"
              % len(p["questions"]))
        for q in p["questions"]:
            print("%s   PIC %s" % (q["variable"], q["pic"]))
            print("   must satisfy : %s   [%s]" % (q["constraint"], q["origin"]))
            print("   invented     : %r" % (q["chose"],))
            print("   answer with  : frameladder %s --work-dir DIR bind "
                  "--bind \"%s=<value>\" --why \"...\""
                  % (args.program, q["variable"]))
            print()
    return _emit(payload, args.json, render)


def cmd_crossroads(args):
    """At a decision point: what each route obliges you to control."""
    program = _program(args)
    from .ladder import analyse, build_plan
    from .dependencies import commitments, route_options
    graph, prov = analyse(program)
    entry = _entry(program, args)
    target = args.target.upper()

    plan = build_plan(program, target, entry=args.entry, via=_via(args))
    along = commitments(program, graph, prov, plan.chain, plan)
    options = route_options(program, graph, prov, entry, target)
    if args.limit:
        options = options[: args.limit]
    payload = {
        "target": target, "entry": entry,
        "chain": [{"frame": c.frame, "operations": sorted(c.operations),
                   "uncontrolled": sorted(c.uncontrolled)} for c in along],
        "routes": options,
    }

    def render(p):
        print("%s -> %s" % (p["entry"], p["target"]))
        print("\nalong the chosen chain, what each frame commits you to")
        print("%-34s %5s  %s" % ("frame", "ops", "not yet controlled"))
        for c in p["chain"]:
            print("%-34s %5d  %s" % (c["frame"], len(c["operations"]),
                                     ", ".join(c["uncontrolled"]) or "-"))
        print("\nroutes in, cheapest first")
        print("%-30s %6s %7s %5s  %s" % ("via", "depth", "guards", "ops",
                                         "operations"))
        for o in p["routes"]:
            print("%-30s %6d %7d %5d  %s"
                  % (o["via"] or "(shortest)", o["depth"], o["guards"],
                     len(o["operations"]), ", ".join(o["operations"][:3])))
    return _emit(payload, args.json, render)


def cmd_family(args):
    """A set of tests that all reach the target, differing only where free."""
    program = _program(args)
    entry = _entry(program, args)
    from .ladder import build_family
    members = build_family(
        program, args.target.upper(), entry=args.entry, via=_via(args),
        limit=args.limit,
        verify_each=(None if args.no_verify
                     else lambda pl: verify(program, pl, entry)["reached"]))
    payload = {"target": args.target.upper(), "entry": entry,
               "members": [{"varied": m["varied"], "category": m["category"],
                            "why": m["why"], "value": m.get("value"),
                            "state": m["plan"].flat_state()} for m in members]}

    def render(p):
        print("%d tests, all reaching %s" % (len(p["members"]), p["target"]))
        print("%-22s %-18s %s" % ("varied", "category", "why"))
        for m in p["members"]:
            print("%-22s %-18s %s" % (m["varied"] or "(baseline)",
                                      m["category"], m["why"]))
            print("   %s" % json.dumps(m["state"], default=str)[:150])
    return _emit(payload, args.json, render)


def cmd_why(args):
    """Where the attempts die, which is what says what to build next.

    A coverage percentage tells you that something is wrong and nothing
    about what. This classifies every branch-directed attempt by the point
    at which it failed, and reports the distribution against chain length -
    because on every program measured so far coverage has been a function of
    how far a plan has to survive, not of how large the program is.
    """
    import collections
    from .coverage import branches_of
    from .ladder import plan_for_branch
    from .interpreter import Interpreter
    from .conformance_defaults import io_defaults, WORLDS

    program = _program(args)
    entry = _entry(program, args)
    buckets = collections.Counter()
    by_depth = collections.defaultdict(lambda: [0, 0])   # depth -> [covered, all]
    stalls = collections.Counter()

    # The frontier search is what the tool actually ships, so a diagnosis that
    # ignores it describes a planner nobody runs. Its directions are collected
    # first and counted as covered wherever they land, which keeps the
    # depth table honest: a direction the entry-rooted plan cannot reach and
    # the frontier can is a fact about the *planner*, not about the target.
    from_lift: set = set()
    if args.lift:
        from .lift import lift as _lift
        try:
            result = _lift(program, entry,
                           seeds=[({}, w, None, None) for w in WORLDS],
                           defaults_for=lambda w: io_defaults(program, w),
                           budget=args.lift, fanout=2)
            for trace in result["traces"]:
                for g in trace.guards:
                    from_lift.add((g.paragraph, g.ordinal, g.kind,
                                   bool(g.result)))
        except Exception:                                # noqa: BLE001
            from_lift = set()

    for b in branches_of(program):
        for direction in (True, False):
            try:
                plan = plan_for_branch(program, b.paragraph, b.line, direction,
                                       entry=entry, max_routes=args.routes,
                                       ordinal=b.ordinal)
            except Exception:                            # noqa: BLE001
                buckets["planner raised"] += 1
                continue
            if not plan.chain:
                buckets["no call chain to the paragraph"] += 1
                continue
            depth = len(plan.chain)
            by_depth[depth][1] += 1
            if plan.open_obligations:
                buckets["plan unsolved (open obligations)"] += 1
                continue
            arrived = decided = False
            for world in WORLDS:
                interp = Interpreter(program, plan.input_state(),
                                     stubs=plan.stub_plan(),
                                     terminals=plan.terminals,
                                     defaults=io_defaults(program, world))
                try:
                    trace = interp.run(entry)
                except Exception:                        # noqa: BLE001
                    continue
                if b.paragraph in trace.entered_set:
                    arrived = True
                    seen = trace.entered_set
                    for step, frame in enumerate(plan.chain):
                        if frame not in seen:
                            stalls[step] += 1
                            break
                if any((g.paragraph, g.ordinal) == (b.paragraph, b.ordinal)
                       and bool(g.result) == direction for g in trace.guards):
                    decided = True
                    break
            if not decided and (b.paragraph, b.ordinal, b.kind,
                                bool(direction)) in from_lift:
                buckets["covered only by the frontier search"] += 1
                by_depth[depth][0] += 1
                continue
            if decided:
                buckets["covered"] += 1
                by_depth[depth][0] += 1
            elif arrived:
                buckets["arrived, decision went the other way"] += 1
            else:
                buckets["plan solved but paragraph never entered"] += 1

    total = max(1, sum(buckets.values()))
    depths = {d: {"covered": v[0], "attempts": v[1],
                  "pct": round(100.0 * v[0] / max(1, v[1]), 1)}
              for d, v in sorted(by_depth.items())}
    payload = {"program": program.name, "attempts": sum(buckets.values()),
               "outcomes": {k: v for k, v in buckets.most_common()},
               "by_chain_length": depths,
               "stalled_at_chain_step": dict(stalls.most_common(8))}
    if args.json:
        print(json.dumps(payload, indent=2, default=str))
        return
    print("%-10s %d attempts" % (program.name, sum(buckets.values())))
    for name, count in buckets.most_common():
        print("   %-46s %5d  %5.1f%%" % (name, count, 100.0 * count / total))
    if depths:
        print("\n   covered, by how far the plan has to survive:")
        for d, row in depths.items():
            print("      chain length %-3d %4d/%-4d %5.1f%%"
                  % (d, row["covered"], row["attempts"], row["pct"]))
    if stalls:
        print("\n   where the ones that never arrived stalled:")
        for step, count in stalls.most_common(8):
            print("      chain step %-3d %5d" % (step, count))


def cmd_sweep(args):
    """Plan and verify every reachable paragraph. The unsolved ones are the
    work list an agent should pick up."""
    program = _program(args)
    from .ladder import analyse
    graph, _prov = analyse(program)
    entry = _entry(program, args)
    journal = Journal(args.work_dir)
    rows, reached, planned = [], 0, 0
    for name in program.paragraph_names:
        if name == entry:
            continue
        chain = shortest_chain(graph, entry, name)
        if chain is None:
            continue
        plan = build_plan(program, name, entry=entry,
                          agent_bindings=journal.bindings(name))
        result = verify(program, plan, entry)
        planned += plan.solved
        reached += result["reached"]
        rows.append({"paragraph": name, "depth": len(chain),
                     "obligations": len(plan.atoms),
                     "bindings": len(plan.bindings),
                     "rendezvous": len(plan.rendezvous),
                     "open": len(plan.open_obligations),
                     "solved": plan.solved, "reached": result["reached"],
                     "blocked_at": result["first_missing_frame"]})
    payload = {"program": program.name, "entry": entry, "targets": len(rows),
               "plans_complete": planned, "verified_reached": reached,
               "rows": rows}

    def render(p):
        print("%s   entry %s   %d targets" % (p["program"], p["entry"], p["targets"]))
        print("%-34s %5s %5s %5s %5s %6s %8s  %s"
              % ("paragraph", "depth", "obl", "bind", "open", "solved", "reached",
                 "blocked at"))
        for r in p["rows"]:
            print("%-34s %5d %5d %5d %5d %6s %8s  %s"
                  % (r["paragraph"], r["depth"], r["obligations"], r["bindings"],
                     r["open"], "yes" if r["solved"] else "no",
                     "yes" if r["reached"] else "NO", r["blocked_at"] or ""))
        print("\nplans complete %d/%d   verified reached %d/%d"
              % (p["plans_complete"], p["targets"], p["verified_reached"],
                 p["targets"]))
    return _emit(payload, args.json, render)


def cmd_replay(args):
    """The whole ordered series a harness runs, with every refusal named."""
    program = _program(args)
    journal = Journal(args.work_dir)
    target = args.target.upper()
    entry = _entry(program, args)
    capability, source = _capability(args, program)
    from .ladder import plan_representable
    from .replay import replay_script
    binds = _binds(args, journal, target)
    if capability.stated and not args.no_profile_aware:
        plan = plan_representable(program, target, capability=capability,
                                  entry=args.entry, agent_bindings=binds)
    else:
        plan = build_plan(program, target, entry=args.entry, via=_via(args),
                          agent_bindings=binds, capability=capability)

    world = None
    if args.world:
        from .ladder import analyse
        from .sequences import fault_worlds, sequence_worlds
        _graph, prov = analyse(program)
        worlds = (sequence_worlds(program, prov, prov.literals)
                  + fault_worlds(program, prov, prov.literals))
        world = next((w for w in worlds if w["name"] == args.world), None)
        if world is None:
            return _emit({"error": "no such world", "world": args.world,
                          "available": [w["name"] for w in worlds]},
                         args.json,
                         lambda p: print("no such world: %s\navailable: %s"
                                         % (p["world"], ", ".join(p["available"]))))

    payload = replay_script(plan, capability, program=program, entry=entry,
                            world=world)
    payload["profile"] = source

    def render(p):
        print("%s -> %s     profile: %s" % (p["entry"], p["target"], p["profile"]))
        print("solved %s   representable %s"
              % (p["solved"], "yes" if p["representable"] else "NO"))
        print("\ninput state (%d)" % len(p["input_state"]))
        for name, value in sorted(p["input_state"].items()):
            print("   %-30s := %r" % (name, value))
        for entry_ in p["refused_inputs"]:
            print("   %-30s := %r   REFUSED: %s"
                  % (entry_["variable"], entry_["value"], entry_["why"]))
        for op in p["operations"]:
            print("\n%s" % op["op_key"])
            if not op["replayable"]:
                print("   NOT REPLAYABLE")
            for outcome in op["outcomes"]:
                print("   call %-3d %-40s%s"
                      % (outcome["call"],
                         json.dumps(outcome["set"], default=str),
                         "   when " + json.dumps(outcome["when"], default=str)
                         if outcome["when"] else ""))
            print("   then     %s"
                  % (json.dumps(op["terminal"], default=str)
                     if op["terminal"] else "(no terminal derived)"))
        if p["reasons"]:
            print("\ncannot be replayed (%d):" % len(p["reasons"]))
            for reason in p["reasons"]:
                print("   %s" % reason)
        for note in p["notes"]:
            print("note: %s" % note)
    return _emit(payload, args.json, render)


def cmd_represent(args):
    """How much of what the tool emits a harness could actually run."""
    program = _program(args)
    capability, source = _capability(args, program)
    if not capability.stated:
        payload = {"error": "no capability profile",
                   "how": "pass --capability FILE, or --proxy status to "
                          "derive one from the source"}
        return _emit(payload, args.json,
                     lambda p: print("%s: %s" % (p["error"], p["how"])))
    from .represent import PROXY_CAVEAT, classify
    payload = classify(program, capability, entry=args.entry,
                       profile_aware=args.profile_aware,
                       max_routes=args.routes,
                       measure_precheck=True)
    payload["profile"] = source
    # A stated profile may still omit a section, which means "no constraint"
    # and is not the same as an empty one. `None` here is a count of nothing
    # stated, not a crash.
    payload["injectable_variables"] = len(capability.injectable or ())
    payload["replayable_operations"] = len(capability.operations or ())
    if source.startswith("proxy"):
        payload["caveat"] = PROXY_CAVEAT

    def render(p):
        print("%s   entry %s   profile %s%s"
              % (p["program"], p["entry"], p["profile"],
                 "   (profile-aware planning)" if p["profile_aware"] else ""))
        print("   %d injectable variables, %d replayable operations"
              % (p["injectable_variables"], p["replayable_operations"]))
        for label in ("emitted", "solved"):
            row = p[label]
            print("   %-8s plans %4d   unrepresentable %4d  %5.1f%%"
                  % (label, row["plans"], row["unrepresentable"], row["pct"]))
        print("   solved AND representable %4d   (the comparable figure: "
              "refusing a route also makes a plan unsolved)" % p["runnable"])
        if p["reason_categories"]:
            print("\n   why, by category")
            for name, count in p["reason_categories"].items():
                print("      %-38s %5d" % (name, count))
        if p["precheck_false_refusals"]:
            print("\n   precheck refused %d route(s) the full solve found "
                  "representable: %s"
                  % (len(p["precheck_false_refusals"]),
                     ", ".join(p["precheck_false_refusals"][:6])))
        bad = [r for r in p["rows"] if not r["representable"]]
        if bad:
            print("\n   the first %d, with reasons"
                  % min(args.limit, len(bad)))
            for row in bad[: args.limit]:
                print("      %-34s %s" % (row["target"],
                                          "; ".join(row["reasons"][:2])))
        if p.get("caveat"):
            print("\n   %s" % p["caveat"])
    return _emit(payload, args.json, render)


def _frame_headroom(capability, program, args) -> dict:
    """Does the harness get anywhere this interpreter cannot?

    This is the whole question behind re-planning from a failed attempt's
    `first_missing_frame`. Resuming from a frame the harness reached only pays
    if that frame is somewhere derivation cannot already start; if this
    interpreter reaches everything the harness does and more, the frames are a
    ranking of seeds rather than new ground.

    Measured here it was the latter, decisively - over seven GnuCOBOL-runnable
    programs the interpreter reached 53 chain frames and the real compiled run
    13, because the compiled program abends on files that are not there. That
    is a property of a corpus with no data behind its mocks, and an estate
    with real data may well invert it. So the number is computed rather than
    assumed, from whatever attempts the profile carries, and it is reported
    without changing what the planner does.
    """
    attempts = getattr(capability, "attempts", ()) or ()
    reached: set = set()
    for attempt in attempts:
        reached |= {str(f).upper() for f in attempt.reached_frames}
        if attempt.first_missing_frame:
            reached.add(str(attempt.first_missing_frame).upper())
    if not attempts:
        return {"attempts": 0, "reached": 0, "beyond_us": [], "unknown": [],
                "verdict": "no attempts in the profile"}

    entry = _entry(program, args)
    graph = build_graph(program)
    ours = {name.upper() for name in depths(graph, entry)}
    known = {name.upper() for name in program.paragraph_names}
    beyond = sorted(name for name in reached if name in known and name not in ours)
    unknown = sorted(name for name in reached if name not in known)

    if beyond:
        verdict = ("%d frame(s) the harness reached are unreachable from %s "
                   "here - re-planning from them would open ground derivation "
                   "cannot start on, so it is worth doing"
                   % (len(beyond), entry))
    else:
        verdict = ("every frame the harness reached is already reachable from "
                   "%s here, so resuming from them ranks seeds rather than "
                   "adding reach" % entry)
    return {"attempts": len(attempts), "reached": len(reached),
            "beyond_us": beyond, "unknown": unknown, "verdict": verdict}


def cmd_directions(args):
    """How a harness's work list lands on this program's decisions.

    A diagnostic, and the first thing to run against a new profile. It answers
    the question that was previously unanswerable from either side: of the
    directions you asked for, which ones do I believe I can name, how did I
    name them, and what did I have to guess.
    """
    program = _program(args)
    capability, source = _capability(args, program)
    resolution = capability.resolve_uncovered(program)
    from .directions import program_mismatch
    payload = dict(resolution.summary())
    payload.update({
        "program": program.name, "profile": source,
        "wrong_program": program_mismatch(capability, program) or None,
        "duplicate_paragraphs": program.duplicate_paragraphs or None,
        "entries": len(capability.raw_uncovered),
        "ordinals_trusted": capability.trust_ordinals,
        "unresolved": list(resolution.unresolved)[: args.limit],
        "ambiguous": list(resolution.ambiguous)[: args.limit],
        "conflicts": list(resolution.conflicts)[: args.limit],
        "frames": _frame_headroom(capability, program, args),
    })

    def render(p):
        print("%s   profile %s" % (p["program"], p["profile"]))
        if p["wrong_program"]:
            print("\n   WRONG PROGRAM: %s\n" % p["wrong_program"])
        if p["duplicate_paragraphs"]:
            # Worth saying before anything else about targeting: a work list
            # naming one of these names cannot mean a single decision, and
            # nothing downstream can tell which body it reached.
            print("\n   DUPLICATE PARAGRAPH NAMES - a chain naming one of "
                  "these reaches the first, and later namesakes are "
                  "unreachable by name:")
            for name, count in sorted(p["duplicate_paragraphs"].items()):
                print("      %-32s declared %d times" % (name, count))
        print("   %d entries -> %d directions on %d decisions"
              % (p["entries"], p["directions"], p["entries_matched"]))
        for how, count in p["by_method"].items():
            print("      %-28s %5d" % (how, count))
        if p["entries_unresolved"]:
            print("\n   unresolved %d" % p["entries_unresolved"])
            for row in p["unresolved"]:
                print("      %-24s %s" % (row.get("paragraph", "?"),
                                          row["reason"]))
        if p["ordinal_conflicts"]:
            # The single most useful line for an integrator. Ordinals that
            # disagree are not a fault in either tool; they are two counting
            # schemes, and a profile matched on text is unaffected. Silence
            # here would have hidden the mismatch that made 1,251 of 1,644
            # targets on this corpus point at the wrong decision.
            print("\n   %d entries carry an ordinal that disagrees with the "
                  "decision their text names." % p["ordinal_conflicts"])
            print("   Text won, which is correct unless the profile sets "
                  "ordinal_source: frameladder.")
        if p["ambiguous_entries"]:
            print("\n   %d entries name more than one decision; all are "
                  "targeted" % p["ambiguous_entries"])
            for row in p["ambiguous"]:
                print("      %-24s %d decisions via %s"
                      % (row["paragraph"], row["matched"], row["how"]))
        frames = p["frames"]
        if frames["attempts"]:
            print("\n   frames from %d attempt(s): harness reached %d, of "
                  "which this interpreter cannot reach %d"
                  % (frames["attempts"], frames["reached"],
                     len(frames["beyond_us"])))
            for name in frames["beyond_us"][:8]:
                print("      %s" % name)
            print("   %s" % frames["verdict"])
    return _emit(payload, args.json, render)


# Every attempted direction ends on exactly one of these, in the order it
# would meet them. Named for what the *harness* would call them, because the
# whole point of the breakdown is that both sides can talk about the same
# number: "1,033 attempted, 0 exported" is not a diagnosis, it is a mystery,
# and 927 of those attempts previously vanished without a classification.
#
# The split is by what would *fix* it. A target with no call chain needs a
# graph that models the language better; an unsolved obligation needs a better
# solver; an unrepresentable input needs a wider harness; a wrong direction
# needs neither, and is a plan that would have been reported as a success.
_STAGES = (
    "not_wanted",                # not on the harness's work list
    "planner_exception",         # the planner raised
    "no_call_chain",             # nothing routes to the paragraph
    "unsolved_obligation",       # routed, but a value was never derived
    "precheck_refused",          # route needs what the harness cannot carry
    "unrepresentable_input",     # binds a variable the harness cannot inject
    "unsupported_operation",     # needs a mock the harness cannot replay
    "unsupported_output_field",  # mock cannot set that payload field
    "replay_sequence_too_long",  # more outcomes than the harness holds
    "target_not_reached",        # ran, never entered the paragraph
    "decision_not_observed",     # entered, that decision never evaluated
    "wrong_direction",           # evaluated, never the way asked for
    "step_limit",                # ran out of statement budget first
    "loop_limit",                # a loop did not terminate
    "verified",                  # observed taking the requested direction
)

# Everything from here on is a plan that exists and is representable, and
# failed only when it was actually run.
_RUN_STAGES = ("target_not_reached", "decision_not_observed", "wrong_direction",
               "step_limit", "loop_limit", "verified")


def _verify_direction(program, plan, branch, direction: bool, entry: str):
    """Did this plan actually take the decision the way it was asked to?

    Returns one of the run dispositions and a sentence for the histogram.

    Reaching a paragraph is not the request. A run can enter the paragraph
    without evaluating this decision at all (it sits under another condition),
    evaluate it the other way, or stop on the statement budget before getting
    there - and all three used to be reported as an exported candidate. The
    decision is identified the same way everywhere else in this repository:
    paragraph, ordinal within that paragraph, kind. Line is not enough,
    because COPY expansion puts several decisions on one.
    """
    from .interpreter import MAX_STEPS, Interpreter
    from .conformance_defaults import io_defaults

    try:
        interp = Interpreter(program, plan.input_state(),
                             stubs=plan.stub_plan(), terminals=plan.terminals,
                             defaults=io_defaults(program, "bare"))
        trace = interp.run(entry)
    except Exception as exc:                                 # noqa: BLE001
        return "planner_exception", "interpreter raised %s" % type(exc).__name__

    # Limits first: a run that stopped early did not decline to take the
    # direction, it never got the chance, and calling that a wrong direction
    # would send someone to fix the solver instead of the budget.
    if trace.runaway:
        return "loop_limit", "loop did not terminate in %s" % trace.runaway
    if trace.steps >= MAX_STEPS:
        return "step_limit", ("ran out of statement budget (%d) before the "
                              "decision" % MAX_STEPS)

    key = (branch.paragraph, branch.ordinal, branch.kind)
    seen = {bool(g.result) for g in trace.guards
            if (g.paragraph, g.ordinal,
                _KIND_OF_GUARD.get(g.kind, g.kind)) == key}
    if seen:
        if bool(direction) in seen:
            return "verified", ""
        return "wrong_direction", ("%s ordinal %d went only %s"
                                   % (branch.paragraph, branch.ordinal,
                                      sorted(seen)[0]))
    if branch.paragraph not in trace.entered_set:
        return "target_not_reached", ("never entered %s" % branch.paragraph)
    return "decision_not_observed", ("entered %s but ordinal %d was never "
                                     "evaluated" % (branch.paragraph,
                                                    branch.ordinal))


# The interpreter names a loop by the verb it saw, `branches_of` by what it
# is. Same join `coverage._KIND` makes; without it every LOOP direction is
# unverifiable and is reported as never observed.
_KIND_OF_GUARD = {"PERFORM_UNTIL": "LOOP", "PERFORM_VARYING": "LOOP"}


def _obligation_text(obligation) -> str:
    """An unsolved obligation in the words of the program, not the dataclass.

    A histogram is only useful if its keys are readable and *repeat*; a raw
    `Atom(lhs=Term(kind='var', ...))` is neither, since the value fields make
    every entry unique and the count is always one.
    """
    atoms = obligation if isinstance(obligation, (tuple, list)) else [obligation]
    names = []
    for atom in atoms:
        for side in ("lhs", "rhs"):
            term = getattr(atom, side, None)
            name = getattr(term, "name", None)
            if name and name not in names:
                names.append(name)
    if not names:
        return str(obligation)[:80]
    joined = ", ".join(names[:3])
    return "no value derived for %s" % joined


def cmd_export(args):
    """Plan every uncovered direction the harness asked for, and account for
    every one that did not make it.

    The previous integration reported 268 targets analysed and one candidate
    exported, with no way to tell a target the planner could not route to from
    one it routed to and could not solve, from one it solved into a plan the
    harness cannot represent. Those three call for completely different fixes
    - a better route, a better solver, a wider capability - so they are
    counted separately and each carries its reasons.
    """
    program = _program(args)
    capability, source = _capability(args, program)
    entry = _entry(program, args)
    from .capability import unrepresentable
    from .coverage import branches_of
    from .ladder import plan_for_branch, precheck
    from .replay import replay_script

    resolution = capability.resolve_uncovered(program)
    wanted = resolution.wanted
    counts = {stage: 0 for stage in _STAGES}
    reasons: dict = {}
    scripts: list = []
    rows: list = []
    # Route refusals are per paragraph, not per direction, and a paragraph
    # carries many decisions. Asking once and remembering saves the dominant
    # cost on a large program.
    refusals: dict = {}

    def note(bucket: str, text: str) -> None:
        key = "%s: %s" % (bucket, text)
        reasons[key] = reasons.get(key, 0) + 1

    for branch in branches_of(program):
        for direction in (True, False):
            key = (branch.paragraph.upper(), branch.ordinal,
                   branch.kind.upper(), bool(direction))
            if wanted and key not in wanted:
                counts["not_wanted"] += 1
                continue
            if capability.stated and args.precheck:
                if branch.paragraph not in refusals:
                    try:
                        refusals[branch.paragraph] = precheck(
                            program, branch.paragraph, capability,
                            entry=args.entry)
                    except Exception:                        # noqa: BLE001
                        refusals[branch.paragraph] = []
                refused = refusals[branch.paragraph]
                if refused:
                    counts["precheck_refused"] += 1
                    for reason in refused[:2]:
                        note("precheck_refused", reason)
                    continue
            try:
                plan = plan_for_branch(program, branch.paragraph, branch.line,
                                       direction, entry=args.entry,
                                       max_routes=args.routes,
                                       ordinal=branch.ordinal,
                                       capability=(capability if args.profile_aware
                                                   else None))
            except Exception as exc:                         # noqa: BLE001
                counts["planner_exception"] += 1
                note("planner_exception", type(exc).__name__)
                continue
            if not plan.chain:
                counts["no_call_chain"] += 1
                note("no_call_chain", "nothing routes to %s from %s"
                     % (branch.paragraph, entry))
                continue
            if plan.open_obligations:
                counts["unsolved_obligation"] += 1
                for obligation in plan.open_obligations[:2]:
                    note("unsolved_obligation", _obligation_text(obligation))
                continue
            blocked = unrepresentable(plan, capability)
            if blocked:
                from .capability import refusal_kind
                # One disposition per attempt, so the first reason decides.
                # Every reason still reaches the histogram, since a target
                # blocked on three things needs all three widened.
                counts[refusal_kind(blocked[0])] += 1
                for reason in blocked[:3]:
                    note(refusal_kind(reason), reason)
                continue

            # A plan that solves and is representable has still not been shown
            # to do the thing it was asked to do. Reaching the paragraph is
            # not the request: the request is that *this* decision goes *this*
            # way, and a run can enter the paragraph without ever evaluating
            # it, or evaluate it the other way, or stop on a limit before
            # arriving. Counting those as successes is how a witness comes
            # back green having covered nothing.
            verdict, detail = _verify_direction(program, plan, branch,
                                                direction, entry)
            counts[verdict] += 1
            if verdict != "verified":
                note(verdict, detail)
                continue
            row = {"paragraph": branch.paragraph, "ordinal": branch.ordinal,
                   "kind": branch.kind, "direction": direction,
                   "condition": branch.condition, "line": branch.line}
            rows.append(row)
            if args.out:
                script = replay_script(plan, capability, program=program,
                                       entry=entry)
                script["direction"] = row
                scripts.append(script)
            if args.limit and counts["verified"] >= args.limit:
                break
        else:
            continue
        break

    attempted = sum(counts[s] for s in _STAGES if s != "not_wanted")
    # The invariant this section exists to provide, checked rather than
    # asserted in prose: every direction considered ended on exactly one
    # disposition, so the columns add up to the work that was done.
    considered = sum(counts.values())
    unaccounted = considered - attempted - counts["not_wanted"]
    from .directions import program_mismatch
    payload = {
        "program": program.name, "entry": entry, "profile": source,
        "wrong_program": program_mismatch(capability, program) or None,
        "work_list": resolution.summary(),
        "attempted": attempted, "counts": counts,
        "unaccounted": unaccounted,
        "reasons": dict(sorted(reasons.items(), key=lambda kv: -kv[1])[:20]),
        "exported": rows,
    }
    if args.out:
        with open(args.out, "w") as fh:
            json.dump({"schema_version": "1.0", "program": program.name,
                       "entry": entry, "candidates": scripts}, fh, indent=1)
        payload["written"] = {"path": args.out, "candidates": len(scripts)}

    def render(p):
        print("%s   entry %s   profile %s" % (p["program"], p["entry"],
                                              p["profile"]))
        if p["wrong_program"]:
            print("\n   WRONG PROGRAM: %s\n" % p["wrong_program"])
        work = p["work_list"]
        if work["directions"]:
            print("   work list: %d directions from %d entries, %d unresolved"
                  % (work["directions"], work["entries_matched"],
                     work["entries_unresolved"]))
        print("\n   %d attempted, each with exactly one disposition"
              % p["attempted"])
        for stage in _STAGES:
            if stage == "not_wanted":
                continue
            count = p["counts"][stage]
            if not count and stage not in ("verified",):
                continue
            mark = "  <- ran, and did the thing asked" if stage == "verified" \
                else ("  (ran)" if stage in _RUN_STAGES else "")
            print("      %-26s %5d%s" % (stage, count, mark))
        if p["counts"]["not_wanted"]:
            print("      %-26s %5d   (not on the work list)"
                  % ("skipped", p["counts"]["not_wanted"]))
        if p["unaccounted"]:
            # Should be impossible; said out loud rather than trusted,
            # because "every attempt has exactly one disposition" is the
            # whole point of the section.
            print("      %-26s %5d   ACCOUNTING BUG"
                  % ("unaccounted", p["unaccounted"]))
        if p["reasons"]:
            print("\n   why")
            for reason, count in p["reasons"].items():
                print("      %5d  %s" % (count, reason))
        if p.get("written"):
            print("\n   wrote %d replayable candidate(s) to %s"
                  % (p["written"]["candidates"], p["written"]["path"]))
    return _emit(payload, args.json, render)


def cmd_bind(args):
    journal = Journal(args.work_dir)
    if not args.work_dir:
        print("--work-dir is required to record a binding", file=sys.stderr)
        return 2
    for item in args.bind or []:
        name, _, value = item.partition("=")
        journal.append("bind", name=name.strip().upper(), value=_coerce(value.strip()),
                       target=(args.target or "").upper() or None, why=args.why or "")
        print("recorded %s = %r" % (name.strip().upper(), _coerce(value.strip())))
    return 0


def cmd_note(args):
    journal = Journal(args.work_dir)
    journal.append("note", text=args.text, target=(args.target or "").upper() or None)
    print("noted")
    return 0


def cmd_resume(args):
    journal = Journal(args.work_dir)
    print(json.dumps(journal.snapshot(), indent=2, default=str))
    return 0


def build_parser():
    p = argparse.ArgumentParser(
        prog="frameladder",
        description="Derive inputs that reach a deep target by lifting its "
                    "obligations outwards along the call chain.")
    p.add_argument("program", help="COBOL source (.cbl) or pre-parsed AST (.ast)")
    p.add_argument("--copybooks", help="directory of copybooks")
    p.add_argument("--conventions", metavar="FILE",
                   help="naming-convention pack; the built-in one is en-US "
                        "and only used where the program itself says nothing")
    p.add_argument("--entry", help="paragraph to start from (default: the first)")
    p.add_argument("--work-dir", help="directory for the journal")
    p.add_argument("--capability", metavar="FILE",
                   help="what the harness that will run these plans can "
                        "inject and replay; without one nothing is assumed "
                        "and no plan is refused")
    p.add_argument("--json", action="store_true", help="machine-readable output")
    sub = p.add_subparsers(dest="command", required=True)

    f = sub.add_parser("frames", help="reachable paragraphs, ranked by guard weight")
    f.add_argument("--limit", type=int, default=25)
    f.set_defaults(func=cmd_frames)

    t = sub.add_parser("trace", help="the call trace to a target, with guards")
    t.add_argument("target")
    t.add_argument("--via", help="comma-separated frames the trace must pass through")
    t.set_defaults(func=cmd_trace)

    pl = sub.add_parser("plan", help="lift obligations and bind what they name")
    pl.add_argument("target")
    pl.add_argument("--via")
    pl.add_argument("--bind", action="append", metavar="VAR=VALUE")
    pl.set_defaults(func=cmd_plan)

    v = sub.add_parser("verify", help="run the plan and report where it failed")
    v.add_argument("target")
    v.add_argument("--via")
    v.add_argument("--bind", action="append", metavar="VAR=VALUE")
    v.add_argument("--terminal", action="append", metavar="OP:VAR=VALUE",
                   help="what a stub returns after its planned outcomes")
    v.add_argument("--default", action="append", metavar="OP:VAR=VALUE",
                   help="what a stub returns when no planned outcome matches")
    v.add_argument("--stub-repeat", type=int, default=1,
                   help="how many times each planned outcome is delivered")
    v.set_defaults(func=cmd_verify)

    e = sub.add_parser("explain", help="dump a frame and its variables' provenance")
    e.add_argument("frame")
    e.add_argument("--variables", help="comma-separated variable names")
    e.add_argument("--source", action="store_true", help="include the source text")
    e.set_defaults(func=cmd_explain)

    cv = sub.add_parser("coverage", help="what a plan set exercises, and what "
                                        "it leaves untouched")
    cv.add_argument("--sample", type=int, default=150,
                    help="also run N states sampled from the program's own "
                         "literals, in each I/O world; complementary to the "
                         "derived plans and on by default because the union "
                         "beats either alone. 0 disables it")
    cv.add_argument("--seed", type=int, default=7,
                    help="seed for --sample, so runs are reproducible")
    cv.add_argument("--overlays", type=int, default=2,
                    help="random draws over the slots each derived plan left "
                         "free; 2 is the knee, 0 disables")
    cv.add_argument("--routes", type=int, default=4,
                    help="alternative ways in to try when the chain itself "
                         "conflicts with the decision")
    cv.add_argument("--learn", metavar="FILE",
                    help="record values that covered something, and reuse them")
    cv.add_argument("--branches", action="store_true",
                    help="also aim a plan at each decision direction")
    cv.add_argument("--families", type=int, default=0,
                    help="also run N divergence-family members per target")
    cv.add_argument("--capability", metavar="FILE",
                    help="harness capability profile: which variables it can "
                         "inject, which operations it can replay, and which "
                         "branch directions it still needs. Plans it could "
                         "not represent are skipped before solving instead of "
                         "being dropped in projection afterwards")
    cv.add_argument("--lift", type=int, default=0, metavar="N",
                    help="up to N runs of the frontier search: solve for the "
                         "next decision from a state that already reached it, "
                         "then re-run the whole program to check. Reaches deep "
                         "targets a plan placed at entry cannot survive to")
    cv.add_argument("--lift-fanout", type=int, default=2,
                    help="candidate states offered per unreached direction")
    cv.add_argument("--lift-only", action="store_true",
                    help="run only the frontier search, for measuring it")
    cv.add_argument("--sequences", type=int, default=3, metavar="N",
                    help="derive outcome sequences up to N records long for "
                         "every file the program gives a FILE STATUS: N "
                         "records with rotating payloads, then end-of-file. "
                         "0 disables, and the fixed-outcome worlds remain")
    cv.add_argument("--fault-codes", type=int, default=3, metavar="N",
                    help="within a sequence, also fail each operation at one "
                         "point with each of its N most-likely statuses - the "
                         "ones the program tests for first, then the "
                         "platform's own. 0 keeps the sequences clean")
    cv.add_argument("--time-budget", type=float, default=0.0, metavar="SECONDS",
                    help="stop planning after this long and report what was "
                         "not reached. The work is quadratic in the size of "
                         "the source - one plan per decision direction, each "
                         "run linear in the program - so on a large program "
                         "the choice is a budget or an unknown wait. Off by "
                         "default, because without it a run is a function of "
                         "the program alone")
    cv.add_argument("--work-list", metavar="FILE",
                    help="write the directions still uncovered, in the format "
                         "--capability reads, so the next run continues this "
                         "one instead of repeating it")
    cv.add_argument("--limit", type=int, default=12)
    cv.set_defaults(func=cmd_coverage)

    nm = sub.add_parser("names", help="this program's own naming vocabulary, "
                                     "ranked by how much it would settle")
    nm.add_argument("--limit", type=int, default=15)
    nm.set_defaults(func=cmd_names)

    qs = sub.add_parser("questions", help="values the program never pins "
                                         "down, for a human or agent to decide")
    qs.add_argument("target", nargs="?")
    qs.add_argument("--limit", type=int, default=10)
    qs.set_defaults(func=cmd_questions)

    cr = sub.add_parser("crossroads", help="what each route obliges you to "
                                          "control in the outside world")
    cr.add_argument("target")
    cr.add_argument("--via")
    cr.add_argument("--limit", type=int, default=10)
    cr.set_defaults(func=cmd_crossroads)

    fm = sub.add_parser("family", help="many tests that reach one target, "
                                       "differing only in the free values")
    fm.add_argument("target")
    fm.add_argument("--via")
    fm.add_argument("--limit", type=int, default=12)
    fm.add_argument("--no-verify", action="store_true",
                    help="skip re-verifying each member (faster, less safe)")
    fm.set_defaults(func=cmd_family)

    wy = sub.add_parser("why", help="where the attempts die, and against what "
                                    "chain length - run this before tuning "
                                    "anything")
    wy.add_argument("--routes", type=int, default=4)
    wy.add_argument("--lift", type=int, default=0, metavar="N",
                    help="also run the frontier search, so the diagnosis "
                         "describes the tool that ships rather than the "
                         "entry-rooted planner alone")
    wy.set_defaults(func=cmd_why)

    sw = sub.add_parser("sweep", help="plan and verify every reachable target")
    sw.set_defaults(func=cmd_sweep)

    rp = sub.add_parser("replay", help="the complete ordered outcome series "
                                       "for one target, ready to run")
    rp.add_argument("target")
    rp.add_argument("--via")
    rp.add_argument("--bind", action="append", metavar="VAR=VALUE")
    rp.add_argument("--world", metavar="NAME",
                    help="use a derived sequence world instead of the plan's "
                         "own outcomes, e.g. READ:F=10@2")
    rp.add_argument("--proxy", nargs="?", const="status",
                    choices=["status", "outputs"],
                    help="derive a capability profile from the source when "
                         "the harness has not stated one; a proxy, and "
                         "labelled as one")
    rp.add_argument("--max-outcomes", type=int, default=0,
                    help="outcomes per operation the harness can hold, for a "
                         "derived profile; 0 states no limit")
    rp.add_argument("--no-profile-aware", action="store_true",
                    help="derive the plan without letting the profile pick "
                         "the route, to see what the harness would refuse")
    rp.set_defaults(func=cmd_replay)

    rr = sub.add_parser("represent", help="which plans the harness could run, "
                                          "and why the rest could not")
    rr.add_argument("--proxy", nargs="?", const="status",
                    choices=["status", "outputs"],
                    help="derive a capability profile from the source when "
                         "the harness has not stated one")
    rr.add_argument("--max-outcomes", type=int, default=0)
    rr.add_argument("--profile-aware", action="store_true",
                    help="let the planner reject before solving and prefer "
                         "routes the profile permits")
    rr.add_argument("--routes", type=int, default=4)
    rr.add_argument("--limit", type=int, default=12)
    rr.set_defaults(func=cmd_represent)

    dr = sub.add_parser("directions", help="how a harness's work list lands "
                                           "on this program's decisions")
    dr.add_argument("--proxy", nargs="?", const="status",
                    choices=["status", "outputs"])
    dr.add_argument("--limit", type=int, default=12)
    dr.set_defaults(func=cmd_directions)

    ex = sub.add_parser("export", help="plan every uncovered direction the "
                                       "harness asked for, and account for "
                                       "every one that did not make it")
    ex.add_argument("--out", metavar="FILE",
                    help="write the replayable candidates as JSON")
    ex.add_argument("--limit", type=int, default=0,
                    help="stop after this many exported candidates; 0 is all")
    ex.add_argument("--routes", type=int, default=4)
    ex.add_argument("--proxy", nargs="?", const="status",
                    choices=["status", "outputs"])
    ex.add_argument("--max-outcomes", type=int, default=0)
    ex.add_argument("--profile-aware", action="store_true",
                    help="let the profile pick the route, not just judge it")
    ex.add_argument("--no-precheck", dest="precheck", action="store_false",
                    help="solve every target even when the route is already "
                         "known to need something the harness cannot carry")
    ex.set_defaults(func=cmd_export, precheck=True)

    b = sub.add_parser("bind", help="record a decision the agent made")
    b.add_argument("--bind", action="append", required=True, metavar="VAR=VALUE")
    b.add_argument("--target")
    b.add_argument("--why")
    b.set_defaults(func=cmd_bind)

    n = sub.add_parser("note", help="record an observation in the journal")
    n.add_argument("text")
    n.add_argument("--target")
    n.set_defaults(func=cmd_note)

    r = sub.add_parser("resume", help="print the journal snapshot")
    r.set_defaults(func=cmd_resume)
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    result = args.func(args)
    if isinstance(result, int):
        return result
    if isinstance(result, dict) and "reached" in result:
        return 0 if result["reached"] else 1
    if isinstance(result, dict) and "solved" in result:
        return 0 if result["solved"] else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
