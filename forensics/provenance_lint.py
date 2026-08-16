#!/usr/bin/env python3
"""Contamination detector (W∞ §3). Catches the project's characteristic failure
— an input that is secretly an output — at PROPOSAL time, not autopsy time.

Blind classification of our eleven deaths (FAILURES.md) found the dominant axis
to be circularity: 5 of 11 were inputs turning out to be outputs. Circularity is
a graph property, so it is mechanically detectable.

  Rule 1 (CYCLE): flag any input whose ancestry passes through the target, its
                  dual, or the certificate class's own optimum.
  Rule 2 (SCALE): every input carries a validity range; flag consumption outside it.
  Rule 3 (QUALITY): inputs carry an error quality (none < log-power < power);
                    consumers carry a requirement. Flag any supplier weaker than
                    what its consumer needs. (#27, the gate, is exactly this.)

Run before building any table; print the report above it, like lemma1_guard.
"""

# Hypothesis depth, as a PARTIAL ORDER rather than a bit (night cycle 2).  A
# death consuming GRH is bridge material of a deeper kind than one consuming RH:
# it changes in strictly more worlds.  RH_CONDITIONAL is retained as the
# "depth >= 1" set, so every existing caller keeps its meaning and the T3(b)
# answer is unchanged by construction — which was the stated kill condition.
HYPOTHESIS_DEPTH = {"RH": 1, "GRH": 2}
DEPTH_NAME = {0: "unconditional", 1: "RH", 2: "GRH"}
RH_CONDITIONAL = set(HYPOTHESIS_DEPTH)

TARGET = "N*_bound"            # what our certificates bound
CLASS_OPTIMUM = {"EP1", "class_closure"}   # outputs of the certificate class itself

QUALITY = {"none": 0, "log-power": 1, "power": 2}

# name: (depends_on, validity range, note, error_quality supplied, quality required of its inputs)
NODES2 = {
    "MRT_corr":  ("log-power", "none"),
    "GM_bridge": ("none",      "power"),
    "sieve_twin":("none",      "none"),
    # The field's progress axis, as suppliers.  All three supply log-power: the
    # axis they advance on is REACH (the shift range theta), not QUALITY (the
    # error's shape).  quarry.py experiment A: the gate fails for every theta>0,
    # so these differ only in a coordinate the consumer does not bill for.
    "Mikawa_third": ("log-power", "none"),
    "BBMZ_theta":   ("log-power", "none"),
    "MRT_8_33":     ("log-power", "none"),
}

NODES = {
    # name:            (depends_on,                         validity: (lo, hi) in the scale the window uses, note)
    "explicit_formula": ([],                                 (0.0, 9.9), "Guinand-Weil"),
    "RH":               ([],                                 (0.0, 9.9), "hypothesis"),
    "positivity":       ([],                                 (0.0, 9.9), "trivial F >= 0"),
    "F_on_[0,1]":       (["explicit_formula"],                (0.0, 1.0), "BGST unconditional (weights retained); Montgomery's is the RH version"),
    "EP1":              (["F_on_[0,1]", "positivity"],        (0.0, 9.9), "the extremal problem; M-T/CGdL live here"),
    "class_closure":    (["F_on_[0,1]", "positivity"],        (0.0, 9.9), "LP closure of what we already hold"),
    "Lemma1_cap3":      (["class_closure", "RH"],             (1.0, 9.9), "Goldston survey Lemma 1; STATED under RH"),
    "CMR_1.3208":       (["EP1", "RH"],                       (3.0, 9.9), "averaged F upper bd; RH; needs LARGE averaging length"),
    "GGOS_floor":       (["EP1", "RH"],                       (1.0, 1.5), "F >= 3/2 - alpha"),
    "sieve_twin":       ([],                                  (0.0, 9.9), "unconditional arithmetic"),
    "MRT_corr":         (["sieve_twin"],                      (1.0, 9.9), "Vaughan + Kuznetsov; log-power saving only"),
    "GM_bridge":        (["RH"],                              (1.0, 2.0), "needs POWER-saving input (survey 6.3)"),
    "GRH":              ([],                                   (0.0, 9.9), "generalised RH — strictly deeper than RH"),
    "CGdL_68_45":       (["GRH", "EP1"],                        (0.0, 9.9), "CGdL GRH-tier proportion; RECALL not VERIFIED"),
    "Mikawa_third":     (["sieve_twin"],                        (1.0, 9.9), "theta = 1/3; log-power only"),
    "BBMZ_theta":       (["sieve_twin"],                        (1.0, 9.9), "later theta; RECALL; log-power only"),
    "MRT_8_33":         (["sieve_twin"],                        (1.0, 9.9), "theta = 8/33, the current wall; log-power only"),
    TARGET:             ([],                                  (0.0, 9.9), "the thing being bounded"),
    # SESSION 145: the two W19 suppliers, so Rule 4 has real nodes to weigh.
    "Selberg_1946":     ([],                                  (0.0, 9.9), "uncond. 2nd moment of S; error O(T sqrt(log log T))"),
    "Goldston_1987_RH": (["RH"],                              (0.0, 9.9), "2nd moment of S to second order; error o(T); RH"),
}

# ---------------------------------------------------------------------------
# Rule 4 (VACUITY), added SESSION 145.  Purchased by TWO surprises 118 sessions
# apart, both the same shape and neither caught by Rules 1-3:
#
#   S3  (026): Lemma 1 made my published thresholds RH-IMPOSSIBLE.
#   S44 (144): Goldston 1987 supplies the o(T) error term W19 needed — under RH,
#              and RH forces `hauntedCount = 0` (`Fiber.noHaunted_of_Noff_zero`).
#
# Rules 1-3 ask whether an input is CIRCULAR, out of SCALE, or too weak in
# QUALITY.  None of them asks the question these two deaths turn on: **does the
# hypothesis this input carries trivialise the very quantity it would bound?**
# An input can be impeccable on all three axes and still be worthless, because
# its own condition empties the target.
#
# The rule keys on a target's VACUITY DEPTH: the hypothesis depth at which the
# target becomes identically zero (or otherwise unreachable).  Flag whenever
# `depth(input) >= vacuity_depth(target)`.
#
# ⚠️ SCOPE, and this is the S39 discipline — say what the signature MISSES.
# Two species of vacuity appeared in the record and this rule catches ONE:
#
#   * TARGET-ZERO      — the hypothesis makes the bounded quantity identically
#                        zero.  S44.  **Caught.**
#   * THRESHOLD-UNREACHABLE — the hypothesis makes the required threshold
#                        impossible while the quantity stays live.  S3.  **NOT
#                        caught**: it needs per-route threshold data this table
#                        does not carry, and inventing that data to make the
#                        calibration look better is exactly what S39 refused.
#
# So the calibration below is honestly 1-of-2 on the purchasing surprises, plus
# two negative controls it must NOT fire on.
TARGET_VACUITY_DEPTH = {
    # target                depth at which it goes vacuous, and the witness
    "hauntedCount":  (1, "RH => Noff = 0 => NoHaunted; Fiber.noHaunted_of_Noff_zero"),
    "Noff":          (1, "RH puts every zero on the line"),
    "factMoment_3":  (1, "bounds hauntedCount and nothing else the ledger reads"),
    # negative controls: live at every hypothesis depth
    "N*_bound":      (99, "a star bound is not trivialised by RH or GRH"),
    "NscStd":        (99, "the literature's row; RH makes it N, not vacuous"),
}


def vacuity(target, input_name):
    """Rule 4: does this input's own hypothesis empty this target?"""
    d = depth(input_name)
    vd, why = TARGET_VACUITY_DEPTH.get(target, (99, "target not tabulated"))
    if d >= vd:
        return f"VACUOUS (target `{target}` is empty at depth {DEPTH_NAME.get(vd, vd)}: {why})"
    return None


def vacuity_calibration():
    """Run Rule 4 on the cases that bought it, and on cases it must not flag."""
    print("=== Rule 4 (VACUITY) calibration — the cases that purchased it ===")
    cases = [
        ("S44 / W19", "Goldston_1987_RH", "hauntedCount", True,
         "the o(T) identity exists only under RH"),
        ("S44 / W19", "Selberg_1946",     "hauntedCount", False,
         "unconditional supply: precision fails, but not vacuity"),
        ("negctl",    "Goldston_1987_RH", "N*_bound",     False,
         "RH does not empty a star bound"),
        ("negctl",    "CGdL_68_45",       "NscStd",       False,
         "GRH-tier proportion against a target RH does not empty"),
    ]
    hits = 0
    for tag, inp, tgt, expect, note in cases:
        got = vacuity(tgt, inp)
        ok = bool(got) == expect
        hits += ok
        print(f"  [{'ok ' if ok else 'MISS'}] {tag:10s} {inp:18s} -> {tgt:14s}"
              f" {'FLAG' if got else 'clean':6s}  ({note})")
    print(f"  {hits}/{len(cases)} as designed."
          "  S3 is NOT among them: it is the threshold-unreachable species,")
    print("  which this rule does not detect and which is recorded as a known miss.")
    return hits == len(cases)


def ancestry(name, seen=None):
    seen = seen or set()
    for d in NODES.get(name, ([],))[0]:
        if d not in seen:
            seen.add(d); ancestry(d, seen)
    return seen

def lint(inputs, window, target=TARGET):
    """inputs: [(node, scale_used)]; window: (lo, hi) the window actually consumes.

    `target` names what the chain is bounding, so Rule 4 (VACUITY) can ask
    whether an input's own hypothesis empties it.  Defaults to the historical
    `N*_bound` so every pre-`145` caller keeps its exact meaning.
    """
    print(f"provenance lint — window scale {window}, target {target}")
    ok = True
    for name, scale in inputs:
        anc = ancestry(name)
        circ = (anc & CLASS_OPTIMUM) or (TARGET in anc)
        lo, hi = NODES[name][1]
        bad_scale = not (lo - 1e-9 <= scale <= hi + 1e-9)
        flags = []
        if circ:      flags.append(f"CIRCULAR (ancestry hits {sorted(anc & (CLASS_OPTIMUM | {TARGET}))})")
        if bad_scale: flags.append(f"SCALE (valid on [{lo},{hi}], consumed at {scale})")
        vac = vacuity(target, name)
        if vac:       flags.append(vac)
        req = NODES2.get(name, (None, "none"))[1]
        if req != "none":
            for other, _ in inputs:
                sup = NODES2.get(other, ("none", None))[0]
                if other != name and QUALITY[sup] < QUALITY[req]:
                    flags.append(f"QUALITY ({name} needs {req}; {other} supplies {sup})")
        ok &= not flags
        print(f"  {name:16s} {'  '.join(flags) if flags else 'clean'}")
    print(f"  => {'PASS' if ok else 'BLOCKED — do not build the table'}")
    return ok

def depth(name):
    """Hypothesis depth of an input: 0 unconditional, 1 RH, 2 GRH."""
    return max((HYPOTHESIS_DEPTH.get(n, 0) for n in (ancestry(name) | {name})),
               default=0)


def rh_consuming(name):
    """Does this input's ancestry consume a hypothesis?  Mechanical T3(b)."""
    return depth(name) >= 1

# which inputs each census death actually consumed (FAILURES.md ids)
DEATHS = {
    1:  ("W16 phase entanglement",        ["explicit_formula"]),
    2:  ("W6 circularity",                []),
    3:  ("W7 vacuity",                    ["sieve_twin"]),
    4:  ("W8 TightMult degeneracy",       ["EP1"]),
    5:  ("W4 container-local kill",       []),
    6:  ("W11 ceiling = class capacity",  ["EP1"]),
    7:  ("W12 depth-blindness",           []),
    8:  ("A2 forced",                     []),
    9:  ("#24 CMR fed back",              ["CMR_1.3208"]),
    10: ("#25 LP collapse",               ["Lemma1_cap3"]),
    11: ("#27 the gate",                  ["MRT_corr", "GM_bridge"]),
}

def t3b_report():
    print("=== T3(b), answered mechanically: which deaths consume RH? ===")
    changers = []
    for i, (name, ins) in sorted(DEATHS.items()):
        hits = [x for x in ins if rh_consuming(x)]
        d = max((depth(x) for x in ins), default=0)
        verdict = (f"CHANGES at depth {DEPTH_NAME[d]} (via " + ", ".join(hits) + ")"
                   if hits else "survives")
        if hits: changers.append(i)
        print(f"  {i:2d}  {name:32s} {verdict}")
    print(f"\n  changers: {changers}  ({len(changers)}/11)")
    tiers = {}
    for i, (_, ins) in sorted(DEATHS.items()):
        tiers.setdefault(max((depth(x) for x in ins), default=0), []).append(i)
    for t in sorted(DEPTH_NAME):
        print(f"  tier {DEPTH_NAME[t]:14s}: {len(tiers.get(t, []))}/11  {tiers.get(t, [])}")
    return changers

# ---------------------------------------------------------------------------
# SESSION 148.  This block used to print its replays and exit 0 unconditionally —
# including the five times it printed "BLOCKED — do not build the table".  A
# guard whose whole purpose is to block cannot report success while blocking,
# and `S49` had just found the same defect in `claims_gate`.  The fix is not to
# exit 1 whenever something blocks: these replays are HISTORICAL, and they are
# *supposed* to block.  The check is that each replay still returns the verdict
# the record says it returned.  A replay that silently starts passing is the
# regression this file exists to catch.
REPLAYS = [
    ("day cycle 6 — CMR's averaged constant at window scale 0.3",
     [("CMR_1.3208", 0.3)], (1.0, 1.32), "N*_bound", False),
    ("day cycle 9 — class walls past support 1",
     [("Lemma1_cap3", 1.5)], (1.0, 2.0), "N*_bound", False),
    ("#27 — the gate: MRT's error quality does not cross the bridge",
     [("MRT_corr", 1.32), ("GM_bridge", 1.32)], (1.0, 1.32), "N*_bound", False),
    ("144 / W19 — the route that died of its own hypothesis",
     [("Selberg_1946", 1.0), ("Goldston_1987_RH", 1.0)], (0.0, 9.9),
     "hauntedCount", False),
    # The control.  Without a chain that must PASS, "everything blocks" would
    # itself pass this self-test, and the guard would be vacuous a second way.
    ("control — unconditional arithmetic, in scale, no quality demand",
     [("sieve_twin", 1.5)], (1.0, 2.0), "N*_bound", True),
]


def replay_selftest():
    print("=== replaying the recorded verdicts — a changed one is a regression ===")
    bad = 0
    for label, inputs, window, target, expected in REPLAYS:
        print(f"\n[{label}]")
        got = lint(inputs, window, target=target)
        if got != expected:
            bad += 1
            print(f"  ⚠️ REGRESSION: recorded {'PASS' if expected else 'BLOCKED'},"
                  f" got {'PASS' if got else 'BLOCKED'}")
    print(f"\n  {len(REPLAYS) - bad}/{len(REPLAYS)} replays match the record.")
    return bad


if __name__ == "__main__":
    t3b_report()
    print()
    _r4 = vacuity_calibration()
    print()
    _bad = replay_selftest()
    if not _r4:
        print("\n  ⚠️ Rule 4 calibration did not behave as designed.")
    raise SystemExit(1 if (_bad or not _r4) else 0)
