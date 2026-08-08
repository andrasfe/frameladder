"""What each paragraph commits you to in the outside world.

Nine paragraphs of COACTUPC contain an external operation. Sixty of its
eighty-five *depend* on one, because the operation is two or three PERFORMs
further down. The direct view is the one the code makes obvious and the
transitive view is the one that decides whether a route is cheap: choosing to
go through a frame means agreeing to control every external operation it can
reach, and a test can only control what it knows to name.

This is deliberately computed rather than stored. The whole index for a
4,236-line program builds in well under a tenth of a second, so a persisted
copy would buy nothing and cost the usual price of a second source of truth -
being wrong the moment the source changes.
"""

from __future__ import annotations

from dataclasses import dataclass, field

_ROUNDS = 24            # deep enough for any real call graph; guards cycles


def direct_operations(program, provenance) -> dict:
    """Paragraph -> external operations performed *in* it.

    Taken from the operation index rather than from the writers, because an
    operation that hands nothing back - CLOSE, SYNCPOINT, a CALL with no
    USING - writes no variable and would otherwise be invisible, while still
    being something a test has to account for.
    """
    return {para: set(ops) for para, ops in
            getattr(provenance, "operations", {}).items()}


def external_reach(program, graph, provenance) -> dict:
    """Paragraph -> every external operation reachable from it.

    A fixpoint over the call graph rather than a walk, because COBOL call
    graphs are full of cycles - a dispatcher that GO TOs back to itself, a
    read loop, an abend handler everything performs.
    """
    cached = getattr(program, "_external_reach", None)
    if cached is not None:
        return cached
    direct = direct_operations(program, provenance)
    reach = {name: set(direct.get(name, ())) for name in program.paragraph_names}
    for _ in range(_ROUNDS):
        changed = False
        for name in program.paragraph_names:
            for site in graph.get(name, []):
                new = reach.get(site.callee, set()) - reach[name]
                if new:
                    reach[name] |= new
                    changed = True
        if not changed:
            break
    try:
        program._external_reach = reach
    except AttributeError:
        pass
    return reach


@dataclass
class Commitment:
    """What routing through a frame obliges a test to control."""
    frame: str
    operations: set = field(default_factory=set)
    planned: set = field(default_factory=set)

    @property
    def uncontrolled(self) -> set:
        return self.operations - self.planned

    @property
    def cost(self) -> int:
        return len(self.uncontrolled)


def commitments(program, graph, provenance, chain, plan=None) -> list:
    """Frame by frame along a chain, what it commits you to and what the plan
    already supplies."""
    reach = external_reach(program, graph, provenance)
    planned = set((plan.stub_plan() if plan else {}).keys())
    return [Commitment(frame, set(reach.get(frame, ())), set(planned))
            for frame in chain]


def route_options(program, graph, provenance, entry: str, target: str) -> list:
    """Alternative ways in, ranked by how much of the outside world each needs.

    The default chain is the shortest, which is not the same as the cheapest
    to control - and for parity work it is usually the one that skips the
    validation worth testing. Seeing the trade lets it be chosen rather than
    inherited.
    """
    from .graph import chain_via, shortest_chain

    reach = external_reach(program, graph, provenance)
    def cost_of(frames):
        # The entry is common to every route and reaches almost everything,
        # so counting it makes all routes look identical. What distinguishes
        # them is what the *choice* commits you to beyond it.
        chosen = frames[1:]
        return sorted(set().union(*(reach.get(f, set()) for f in chosen))
                      if chosen else set())

    base = shortest_chain(graph, entry, target)
    options = []
    if base is not None:
        frames = [entry] + [s.callee for s in base]
        options.append({
            "via": None, "frames": frames, "depth": len(base),
            "guards": sum(len(s.guards) for s in base),
            "operations": cost_of(frames),
        })

    seen = {tuple(options[0]["frames"])} if options else set()
    for waypoint in program.paragraph_names:
        if waypoint in (entry, target):
            continue
        leg = chain_via(graph, entry, [waypoint], target)
        if leg is None:
            continue
        frames = [entry] + [s.callee for s in leg]
        key = tuple(frames)
        if key in seen:
            continue
        seen.add(key)
        options.append({
            "via": waypoint, "frames": frames, "depth": len(leg),
            "guards": sum(len(s.guards) for s in leg),
            "operations": cost_of(frames),
        })
    options.sort(key=lambda o: (len(o["operations"]), o["depth"]))
    return options
