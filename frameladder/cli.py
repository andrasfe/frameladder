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
    return load_program(args.program, args.copybooks)


def _entry(program, args) -> str:
    return (args.entry or program.paragraph_names[0]).upper()


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
    plan = build_plan(program, target, entry=args.entry, via=_via(args),
                      agent_bindings=_binds(args, journal, target))
    payload = plan.to_dict()

    def render(p):
        print("target  %s" % p["target"])
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
                        for w in prov.writers.get(name, [])][:12],
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
    p.add_argument("--entry", help="paragraph to start from (default: the first)")
    p.add_argument("--work-dir", help="directory for the journal")
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

    sw = sub.add_parser("sweep", help="plan and verify every reachable target")
    sw.set_defaults(func=cmd_sweep)

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
