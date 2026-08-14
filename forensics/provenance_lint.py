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
}

def ancestry(name, seen=None):
    seen = seen or set()
    for d in NODES.get(name, ([],))[0]:
        if d not in seen:
            seen.add(d); ancestry(d, seen)
    return seen

def lint(inputs, window):
    """inputs: [(node, scale_used)]; window: (lo, hi) the window actually consumes."""
    print(f"provenance lint — window scale {window}")
    ok = True
    for name, scale in inputs:
        anc = ancestry(name)
        circ = (anc & CLASS_OPTIMUM) or (TARGET in anc)
        lo, hi = NODES[name][1]
        bad_scale = not (lo - 1e-9 <= scale <= hi + 1e-9)
        flags = []
        if circ:      flags.append(f"CIRCULAR (ancestry hits {sorted(anc & (CLASS_OPTIMUM | {TARGET}))})")
        if bad_scale: flags.append(f"SCALE (valid on [{lo},{hi}], consumed at {scale})")
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

if __name__ == "__main__":
    t3b_report()
    print()
    print("=== replaying the two corrections that cost headlines ===\n")
    print("[day cycle 6] feeding CMR's averaged constant at window scale 0.3:")
    lint([("CMR_1.3208", 0.3)], (1.0, 1.32))
    print("\n[day cycle 9] class walls past support 1:")
    lint([("Lemma1_cap3", 1.5)], (1.0, 2.0))
    print("\n[day cycle 10-11] the priced chain (arithmetic fuel):")
    lint([("MRT_corr", 1.32), ("GM_bridge", 1.32)], (1.0, 1.32))
    print("\n[#27] the same chain, with Rule 3 active — this is the gate:")
    lint([("MRT_corr", 1.32), ("GM_bridge", 1.32)], (1.0, 1.32))
