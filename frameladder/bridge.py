"""Fuzz one paragraph massively, learn its inverse, feed the next.

Every existing phase asks a paragraph for one thing at a time: fire this
direction, emit this value. This module asks a different question first -
*what can this paragraph do at all?* - and answers it by brute observation:
thousands of isolated runs of the stuck paragraph's closure, every one
recorded as a machine-verified fact ``(inputs, directions fired,
post-state)``. The table is the product; everything after it is retrieval.

Two retrievals are built in. The *direct* one is the user's own idea taken
literally: every recorded post-state is tried as an entry state for the
next paragraph, so anything the stuck paragraph has ever been seen to
produce is offered downstream. The *learned* one generalises the table: an
MLP is trained backward, post-state to inputs, and asked to propose inputs
for post-states the fuzz never quite hit. The model only ever *selects*
among values that appeared in real runs or in the program's own text - it
proposes, it never invents bytes - and nothing it proposes counts until a
real run of the actual paragraph confirms it. The model is a search
heuristic with a verifier, not an oracle.

The output is not witnesses - a witness is from-entry, and nothing here
runs from entry. The output is *facts* in the shape ``chain.run_chain``
consumes, so the upstream walk can carry a verified bridge back to program
entry and credit it through the one ledger path. Per goal the contract is
the usual one: a bridged fact, or a named refusal.

The learned half degrades honestly: without numpy and scikit-learn the
direct half still runs and the report says why the model did not.
"""

from __future__ import annotations

import json
import random
import time

from .chain import (_Budget, _Index, _direction_key, _guard_evidence,
                    _attempts_for, _satisfied, local_solve)
from .conformance_defaults import io_defaults
from .coverage import branches_of
from .interpreter import Interpreter
from .ladder import analyse

DEFAULT_RUNS = 20000     # fuzz budget for the stuck paragraph
STALL = 2500             # consecutive novelty-free runs before stopping early
MUTATE_SHARE = 0.5       # of the random budget, spent mutating firing states
VOCAB_CAP = 16           # one-hot width per field; the tail shares a bucket
TOP_K = 24               # model proposals per goal
VERIFY_CAP = 40          # candidate verifications per goal (direct + model)
MAX_GOALS = 400          # missing directions worked per invocation
MAX_ROWS = 20000         # rows retained; past it only new signatures are
MODEL_FIELDS = 24        # fields encoded, and models fitted, at most
SEARCH_GOALS = 40        # goals stage 3b attempts; the rest are named
FACT_FIELDS = 48         # a fact donated to the chain is trimmed to this many
_BOUNDARY = ("", " ", "0", "1", "9", "\x00", "\xff", "00000000", "99999999")


def _learn_backend():
    try:
        import numpy                                  # noqa: F401
        from sklearn.neural_network import MLPClassifier
        return numpy, MLPClassifier
    except Exception:                                 # noqa: BLE001
        return None, None


# ---------------------------------------------------------------------------
# Stage 1 - the table: massive fuzz of the stuck paragraph
# ---------------------------------------------------------------------------

class Table:
    """Machine-verified facts about one paragraph, from isolated runs.

    ``rows`` hold ``{"state": inputs, "staged": stub series, "fired":
    [direction keys], "post": projected post-state}``. ``written`` is every
    field the closure was *observed* to change - the concrete answer to
    "which requirements downstream can this paragraph satisfy", with no
    static analysis to be wrong about it.

    ``state`` is the *delta* from the run's constant base state, not the
    whole entry state. Storing the merge instead put a copy of all 2,823
    declared fields in every row; at a 60,000-run budget that is upwards of
    a hundred million dictionary entries per process, and twelve such
    processes exhausted a 28GB machine. The base is constant and re-applied
    wherever a row is replayed, so the delta loses nothing.

    ``cap`` bounds retention: past it only rows showing a new signature are
    kept, so memory tracks distinct *behaviour* rather than run count, and
    what was dropped is counted rather than silently lost.
    """

    def __init__(self, paragraph: str, watch, cap: int = MAX_ROWS):
        self.paragraph = paragraph
        self.watch = tuple(watch)
        self.cap = cap
        self.dropped = 0
        self.rows: list = []
        self.written: set = set()
        self.signatures: set = set()
        self.crashed = 0          # runs the interpreter could not finish

    def record(self, state, staged, fired, post, before=None) -> bool:
        """Keep one run; True when it showed something new.

        ``before`` is the interpreter's own state *after initialisation and
        before execution* - not the supplied entry state. A field the entry
        state never mentioned still holds its declared VALUE at that point,
        and counting the difference against the entry state instead marked
        every such field as written by a paragraph that never touched it.
        """
        for name, value in post.items():
            was = (before or {}).get(name, state.get(name))
            if str(was) != str(value):
                self.written.add(name)
        signature = (fired, tuple(sorted((k, str(v)[:64])
                                         for k, v in post.items())))
        fresh = signature not in self.signatures
        self.signatures.add(signature)
        if fresh or len(self.rows) < self.cap:
            self.rows.append({"state": dict(state), "staged": staged or {},
                              "fired": fired, "post": post})
        else:
            self.dropped += 1
        return fresh

    def dump(self, path: str) -> None:
        with open(path, "w") as handle:
            for row in self.rows:
                record = dict(row)
                record["fired"] = [list(key) for key in row["fired"]]
                handle.write(json.dumps(record, default=str) + "\n")


def _pools(index, evidence, rng, downstream=None) -> dict:
    """Per-field candidate values: the program's own words, plus the
    figurative boundaries every platform defines. Nothing here comes from
    a field's name.

    ``downstream`` is the *consumer's* evidence. Seeding the producer's
    pools with it aims the fuzz at values the next paragraph actually
    distinguishes: producers routinely move an input straight through, so
    a literal only the consumer compares against is reachable at the
    producer's input and was previously never tried there. Still the
    program's own text - just a different paragraph's share of it.
    """
    merged = {name: list(values) for name, values in evidence.items()}
    for name, values in (downstream or {}).items():
        merged.setdefault(name, [])
        merged[name] = list(merged[name]) + [v for v in values
                                             if v not in merged[name]]
    evidence = merged
    pools = {}
    for name, values in evidence.items():
        seen, pool = set(), []
        for value in list(values) + list(_BOUNDARY):
            key = str(value)
            if key not in seen:
                seen.add(key)
                pool.append(str(value))
        # a field compared only against digits is numeric in practice;
        # give the fuzzer a few magnitudes the text never wrote down
        if values and all(str(v).lstrip("-").isdigit()
                          for v in values if str(v).strip()):
            for _ in range(3):
                extra = str(rng.randint(0, 10 ** rng.randint(1, 8)))
                if extra not in seen:
                    seen.add(extra)
                    pool.append(extra)
        pools[name] = pool
    return pools


def fuzz(program, index, prov, current: str, watch, runs: int, seed: int,
         base_state=None, progress=None, deadline=None,
         downstream=None) -> Table:
    """Run the stuck paragraph's closure under everything we can think of.

    Evidence-built attempts first (they carry staged stub series the random
    stage inherits), then random pool combinations, then one-field
    mutations of any state that fired a new signature. Deterministic under
    ``seed``. Stops early after ``STALL`` runs without novelty, or when
    ``deadline`` passes - run count is a poor unit of cost, because per-run
    execution time varies thirtyfold across closures and the same ``runs``
    budget is a minute on one paragraph and half an hour on another.
    """
    members = index.closure(current)
    sub = index.sub_program(members)
    rng = random.Random(seed)
    evidence = _guard_evidence(index, members)
    pools = _pools(index, evidence, rng, downstream=downstream)
    fields = sorted(pools)
    table = Table(current, watch)
    defaults = io_defaults(program, "populated")

    def execute(state, staged):
        merged = dict(base_state or {})
        merged.update(state)
        def snapshot(interp):
            out = {}
            for name in table.watch:
                try:
                    value = interp.state.get(name)
                except Exception:                         # noqa: BLE001
                    value = None
                if value is not None:
                    out[name] = value
            return out

        try:
            interp = Interpreter(sub, dict(merged), stubs=staged or None,
                                 defaults=defaults)
            before = snapshot(interp)
            trace = interp.run(current if current in members else members[0])
        except Exception:                                 # noqa: BLE001
            table.crashed += 1
            return None
        fired = frozenset(_direction_key(g) for g in trace.guards)
        # the delta, not `merged`: see Table's docstring
        return table.record(state, staged, fired, snapshot(interp), before)

    if progress:
        progress("fuzz: evidence attempts", 0, runs, force=True)
    attempts = _attempts_for(index, prov, members)
    stagings = [staged for _s, staged in attempts if staged] or [{}]
    spent = 0
    for state, staged in attempts:
        if spent >= runs or (deadline and time.time() > deadline):
            break
        execute(state, staged)
        spent += 1
        if progress:
            progress("fuzz: evidence attempts", spent, runs,
                     len(table.signatures), unit="signatures")

    interesting = list(range(len(table.rows)))
    stall = 0
    while spent < runs and stall < STALL and fields \
            and not (deadline and time.time() > deadline):
        if interesting and rng.random() < MUTATE_SHARE:
            base = table.rows[rng.choice(interesting)]
            state = dict(base["state"])
            staged = base["staged"]
            for _ in range(rng.randint(1, 2)):
                name = rng.choice(fields)
                state[name] = rng.choice(pools[name])
        else:
            staged = rng.choice(stagings)
            state = {}
            width = rng.randint(1, max(1, min(len(fields), 12)))
            for name in rng.sample(fields, width):
                state[name] = rng.choice(pools[name])
        fresh = execute(state, staged)
        spent += 1
        if progress:
            progress("fuzz: random+mutate", spent, runs,
                     len(table.signatures), unit="signatures")
        if fresh:
            stall = 0
            interesting.append(len(table.rows) - 1)
            if len(interesting) > 512:
                interesting = interesting[-512:]
        else:
            stall += 1
    return table


# ---------------------------------------------------------------------------
# Stage 2 - the inverse model: post-state in, input choices out
# ---------------------------------------------------------------------------

class Inverse:
    """An MLP per input field, each choosing among that field's own
    observed values. Selection, never invention: the classifier's whole
    label space is values that occurred in verified runs, so nothing it
    can output violates the evidence rule."""

    def __init__(self, table: Table, seed: int, bridgeable,
                 hidden=(64,), iterations: int = 300,
                 fields: int = MODEL_FIELDS):
        self.ok = False
        self.why = ""
        self.numpy, mlp_cls = _learn_backend()
        if mlp_cls is None:
            self.why = "numpy/scikit-learn not installed (pip install " \
                       "frameladder[learn])"
            return
        rows = table.rows
        if len(rows) < 50:
            self.why = "only %d fuzz rows; need 50" % len(rows)
            return
        # Only the *bridgeable surface* is worth encoding: fields this
        # paragraph was observed to write that the next one's guards also
        # read. Encoding everything watched put ~12,000 columns in front of
        # one model per input field and the fit never returned - and the
        # extra columns were noise, since a query only ever constrains the
        # surface. Fields that never varied carry no information either.
        varying = {name for name in bridgeable
                   if len({str(row["post"].get(name, "")) for row in rows}) > 1}
        self.out_fields = sorted(varying)[:fields]
        if not self.out_fields:
            self.why = "no written field varied across the fuzz"
            return
        self.vocab = {}
        for name in self.out_fields:
            counts: dict = {}
            for row in rows:
                value = str(row["post"].get(name, ""))
                counts[value] = counts.get(value, 0) + 1
            ranked = sorted(counts, key=lambda v: -counts[v])
            self.vocab[name] = ranked[:VOCAB_CAP]
        matrix = self.numpy.array([self._encode(row["post"])
                                   for row in rows])
        self.models = {}
        self.labels = {}
        # Model the inputs that actually moved, most-varied first, and stop
        # at a cap: one fit per field is the cost, and a field the fuzz
        # barely touched cannot be predicted from anything anyway.
        counted = []
        for name in sorted({name for row in rows for name in row["state"]}):
            values = {str(row["state"].get(name, "")) for row in rows}
            if 2 <= len(values) <= 200:
                counted.append((len(values), name))
        counted.sort(reverse=True)
        for _size, name in counted[:fields]:
            column = [str(row["state"].get(name, "")) for row in rows]
            values = sorted(set(column))
            index_of = {value: i for i, value in enumerate(values)}
            target = self.numpy.array([index_of[value] for value in column])
            model = mlp_cls(hidden_layer_sizes=tuple(hidden),
                            max_iter=iterations, random_state=seed)
            try:
                import warnings
                with warnings.catch_warnings():
                    # an unconverged fit is still a usable ranking; every
                    # proposal is verified by a real run before it counts
                    warnings.simplefilter("ignore")
                    model.fit(matrix, target)
            except Exception:                             # noqa: BLE001
                continue
            self.models[name] = model
            self.labels[name] = values
        if not self.models:
            self.why = "no input field varied enough to learn"
            return
        self.ok = True

    def _encode(self, post: dict) -> list:
        """The post-state as numbers.

        Deliberately no direction bits. A query knows the post-state it
        wants but not which directions the producing run happened to fire,
        so those columns were ones in training and zeros in every query -
        a mismatch that moves the question outside the distribution the
        model was fitted on.
        """
        vector = []
        for name in self.out_fields:
            value = str(post.get(name, ""))
            stripped = value.strip()
            vector.append(1.0 if not stripped else 0.0)
            numeric = 0.0
            if stripped.lstrip("-").isdigit():
                try:
                    numeric = max(-1.0, min(1.0, int(stripped) / 1e9))
                except ValueError:
                    numeric = 0.0
            vector.append(numeric)
            slots = [0.0] * (VOCAB_CAP + 1)
            vocab = self.vocab[name]
            slots[vocab.index(value) if value in vocab else VOCAB_CAP] = 1.0
            vector.extend(slots)
        return vector

    def propose(self, desired: dict, table: Table, k: int = TOP_K) -> list:
        """Input states ranked by the model's confidence for ``desired``.

        Fields the goal does not constrain are encoded at their modal
        observed value, so the query sits inside the training
        distribution. The first proposal takes every field's best choice;
        the rest flip the least-confident fields to their runners-up, one
        more per proposal - a beam that needs no randomness."""
        if not self.ok:
            return []
        post = {name: self.vocab[name][0] if self.vocab[name] else ""
                for name in self.out_fields}
        post.update({str(name): str(value)
                     for name, value in desired.items()})
        matrix = self.numpy.array([self._encode(post)])
        best, second = {}, []
        for name, model in self.models.items():
            probabilities = model.predict_proba(matrix)[0]
            order = list(self.numpy.argsort(probabilities))[::-1]
            labels = self.labels[name]
            classes = list(model.classes_)
            best[name] = labels[classes[order[0]]]
            if len(order) > 1:
                second.append((probabilities[order[0]],
                               name, labels[classes[order[1]]]))
        proposals = [dict(best)]
        second.sort()                     # least confident first
        for count in range(1, min(k, len(second) + 1)):
            variant = dict(best)
            for _confidence, name, runner_up in second[:count]:
                variant[name] = runner_up
            proposals.append(variant)
        seen, unique = set(), []
        for proposal in proposals[:k]:
            key = tuple(sorted(proposal.items()))
            if key not in seen:
                seen.add(key)
                unique.append(proposal)
        return unique


# ---------------------------------------------------------------------------
# Stage 3 - bridge each missing direction of the next paragraph
# ---------------------------------------------------------------------------

def _trim(state: dict, keep) -> dict:
    """A fact donated to the chain, cut to the fields that matter."""
    keep = set(str(name).upper() for name in keep)
    chosen = {name: value for name, value in state.items()
              if str(name).upper() in keep}
    if len(chosen) < FACT_FIELDS:
        for name, value in state.items():
            if len(chosen) >= FACT_FIELDS:
                break
            if name not in chosen and str(value).strip():
                chosen[name] = value
    return chosen


def run_bridge(program, current: str, next_para: str, baseline=None,
               runs: int = DEFAULT_RUNS, seed: int = 7, budget: int = 8000,
               use_model: bool = True, base_state=None,
               table_path=None, progress=None,
               search_goals: int = SEARCH_GOALS,
               max_seconds: int = 0, seed_from_consumer: bool = False,
               model_hidden=(64,), model_iter: int = 300,
               model_fields: int = MODEL_FIELDS, proposals: int = TOP_K,
               verify_cap: int = VERIFY_CAP) -> dict:
    """The whole component: fuzz ``current``, learn it backward, and try
    everything - recorded outputs and model proposals alike - against every
    missing direction of ``next_para``. Nothing is believed unverified."""
    current, next_para = current.upper(), next_para.upper()
    started = time.time()
    # Two slices: the fuzz and sweep get the first, the per-goal search an
    # equal second one. Without its own bound the search stage is unbounded
    # in time however tight the fuzz budget is - one solve builds a whole
    # closure's attempt set - so a time-bounded run could still never end.
    deadline = (started + max_seconds) if max_seconds else None
    search_deadline = (started + 2 * max_seconds) if max_seconds else None
    index = _Index(program)
    _graph, prov = analyse(program)
    if current not in index.paragraphs or next_para not in index.paragraphs:
        missing = current if current not in index.paragraphs else next_para
        raise SystemExit("no paragraph named %s" % missing)

    if progress:
        progress("indexing closures", force=True)
    next_members = index.closure(next_para)
    next_sub = index.sub_program(next_members)
    next_evidence = _guard_evidence(index, next_members)
    watch = sorted(set(next_evidence)
                   | {str(name).upper() for member in next_members
                      for name in index.live_in(member)})

    table = fuzz(program, index, prov, current, watch, runs, seed,
                 base_state=base_state, progress=progress,
                 deadline=deadline,
                 downstream=next_evidence if seed_from_consumer else None)
    if table_path:
        table.dump(table_path)

    if progress:
        progress("training inverse model", witnessed=len(table.rows),
                 force=True, unit="fuzz rows")
    bridgeable = sorted(table.written & set(next_evidence))
    inverse = (Inverse(table, seed, bridgeable, hidden=model_hidden,
                       iterations=model_iter, fields=model_fields)
               if use_model else None)
    model_note = ("disabled" if not use_model
                  else "trained on %d rows, %d input fields, hidden %s"
                       % (len(table.rows), len(inverse.models),
                          "x".join(str(n) for n in model_hidden))
                  if inverse.ok else inverse.why)

    baseline = baseline or set()
    goals = []
    for branch in branches_of(program):
        if branch.paragraph in next_members:
            for direction in (True, False):
                key = (branch.paragraph, branch.ordinal, branch.kind,
                       direction)
                if key not in baseline:
                    goals.append(key)
    # A cap that drops goals without saying so reads, in the report, exactly
    # like a paragraph whose every direction was considered and refused.
    # The excess is named below instead.
    beyond_cap, goals = goals[MAX_GOALS:], goals[:MAX_GOALS]

    defaults = io_defaults(program, "populated")
    the_budget = _Budget(budget)
    sweep_cache: dict = {}
    facts = {current: [], next_para: []}
    bridged, refusals, results = [], {}, []

    def refuse(goal, reason):
        refusals[reason] = refusals.get(reason, 0) + 1
        results.append({"goal": list(goal), "outcome": reason})

    def verify(goal, sigma, staged, via):
        """One candidate: run current's closure, hand the whole post-state
        to the next closure, and believe only what fires."""
        merged = dict(base_state or {})
        merged.update(sigma)
        try:
            interp = Interpreter(index.sub_program(index.closure(current)),
                                 dict(merged), stubs=staged or None,
                                 defaults=defaults)
            interp.run(current)
            post_full = {name: interp.state[name] for name in interp.state}
            follow = Interpreter(next_sub, dict(post_full),
                                 stubs=staged or None, defaults=defaults)
            trace = follow.run(next_para)
        except Exception:                                 # noqa: BLE001
            return False
        if goal not in {_direction_key(g) for g in trace.guards}:
            return False
        bridged.append(goal)
        facts[current].append(_trim(merged, set(sigma)))
        facts[next_para].append(_trim(post_full, watch))
        results.append({"goal": list(goal), "outcome": "bridged",
                        "via": via, "state": merged,
                        "staged": staged or {}})
        return True

    # Stage 3a - the sweep. Every distinct thing the paragraph was seen to
    # produce, handed straight to the next paragraph. This is the cheap
    # half and the one that pays: one run per distinct post-state, no
    # per-goal solving, and a run credits every direction it takes rather
    # than the one it aimed at. Per-goal search (3b) then works only on
    # what this could not reach - the ordering matters, because solving a
    # goal the sweep answers for free costs hundreds of runs.
    wanted = set(goals)
    seen_posts: set = set()
    swept = 0
    timed_out = False
    # Two post-states that agree on everything live at the next paragraph's
    # entry drive it identically, so only one of them is worth a run.
    # Deduplicating on the *whole* post-state instead spent 5,115 runs -
    # the entire budget - on states that differed only in fields the next
    # paragraph never reads, and left nothing for the search that follows.
    deciding = sorted(set(index.live_in(next_para)) & set(watch)) or watch

    def project(post):
        return tuple((name, str(post.get(name, ""))) for name in deciding)

    for row in table.rows:
        if not wanted or the_budget.left() <= 0:
            break
        if deadline and time.time() > deadline:
            timed_out = True
            break
        signature = project(row["post"])
        if signature in seen_posts:
            continue
        seen_posts.add(signature)
        swept += 1
        if progress:
            progress("3a sweep: outputs -> next", swept, len(table.rows),
                     len(bridged), unit="bridged")
        state = dict(base_state or {})
        state.update(row["post"])
        the_budget.spend()
        try:
            follow = Interpreter(next_sub, state, stubs=row["staged"] or None,
                                 defaults=defaults)
            trace = follow.run(next_para)
        except Exception:                                    # noqa: BLE001
            continue
        took = {_direction_key(g) for g in trace.guards} & wanted
        if not took:
            continue
        for goal in took:
            bridged.append(goal)
            results.append({"goal": list(goal), "outcome": "bridged",
                            "via": "sweep", "state": row["state"],
                            "staged": row["staged"] or {}})
        wanted -= took
        facts[current].append(_trim(row["state"], set(row["state"])))
        facts[next_para].append(_trim(row["post"], watch))

    # Stage 3b - per-goal search for what the sweep did not reach. Capped:
    # one solve builds a whole closure's attempt set, which on a large
    # paragraph costs far more than the sweep did for every goal together.
    # What the cap drops is named below, never silently dropped.
    searched = sorted(wanted)
    skipped = searched[search_goals:] if search_goals >= 0 else []
    for position, goal in enumerate(searched[:search_goals]):
        if progress:
            progress("3b per-goal search", position,
                     min(len(searched), max(search_goals, 0)),
                     len(bridged), unit="bridged")
        if the_budget.left() <= 0:
            refuse(goal, "budget-exhausted")
            continue
        if search_deadline and time.time() > search_deadline:
            refuse(goal, "time-exhausted")
            continue
        found, _spent = local_solve(index, prov, goal, the_budget,
                                    sweep_cache)
        if the_budget.left() <= 0:
            refuse(goal, "budget-exhausted")
            continue
        if not found:
            refuse(goal, "next-local-unsolvable")
            continue
        required, staged_next, _full, _fired = found[0]
        desired = {name: value for name, value in required.items()
                   if str(name).upper() in table.written}
        passthrough = {name: value for name, value in required.items()
                       if str(name).upper() not in table.written}
        if not desired:
            refuse(goal, "independent-of-current")
            continue
        candidates = []
        for row in table.rows:
            if _satisfied(row["post"], desired):
                sigma = dict(row["state"])
                sigma.update(passthrough)
                candidates.append((sigma, row["staged"], "direct"))
        proposed = (inverse.propose(desired, table, k=proposals)
                    if inverse else [])
        stagings = ([row["staged"] for row in table.rows if row["staged"]]
                    or [{}])
        for proposal in proposed:
            sigma = dict(proposal)
            sigma.update(passthrough)
            candidates.append((sigma, stagings[0], "model"))
        if not candidates:
            refuse(goal, "no-output-satisfies")
            continue
        for sigma, staged, via in candidates[:verify_cap]:
            if verify(goal, sigma, staged, via):
                break
        else:
            refuse(goal, "candidates-refuted")

    for goal in skipped:
        refuse(goal, "not-searched (3b cap)")
    for goal in beyond_cap:
        refuse(goal, "not-worked (goal cap)")

    via = {"sweep": 0, "direct": 0, "model": 0}
    for row in results:
        if row["outcome"] == "bridged":
            via[row["via"]] = via.get(row["via"], 0) + 1
    return {"program": program.name, "current": current, "next": next_para,
            "fuzz_rows": len(table.rows), "fuzz_crashes": table.crashed,
            "fuzz_rows_dropped": table.dropped,
            "distinct_signatures": len(table.signatures),
            "written_fields": len(table.written),
            "bridgeable_fields": len(bridgeable), "model": model_note,
            "seeded_from_consumer": bool(seed_from_consumer),
            "goals": len(goals), "goals_beyond_cap": len(beyond_cap),
            "swept_states": swept,
            "seconds": round(time.time() - started, 1),
            "timed_out": timed_out or bool(deadline and time.time() > deadline),
            "searched_goals": min(len(searched), max(search_goals, 0)),
            "unsearched_goals": len(skipped),
            "bridged": len(bridged),
            "bridged_sweep": via["sweep"], "bridged_direct": via["direct"],
            "bridged_model": via["model"],
            "refusals": refusals, "results": results, "facts": facts}
