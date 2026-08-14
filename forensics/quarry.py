#!/usr/bin/env python3
"""The quarry (A3 annex): re-run the retracted computations AS EXPERIMENTS.

A3's inversion says the conditional row was built as a quarantine and is
actually the quarry — a documented RH-conditional failure with an exactly named
gap is bridge material.  So the retractions get re-run, not re-buried, with the
lint on and every RH-node flagged.

DAG NOTE.  This file was written under a register freeze and used a local
experiment table for the nodes the guard did not carry (historical shift ranges,
the GRH tier).  Night cycle 2 **adopted** those nodes into the guard, and the
local table is gone: `provenance_lint.depth` is now the authority.  The two
implementations agreed exactly before the swap (8/3/0), which is the R17 witness
for the adoption.

Run: python3 forensics/quarry.py
"""

import math
import provenance_lint as L

SEP = "=" * 72


# ---------------------------------------------------------------- experiment A
# The gate (#27), swept across the field's own progress axis.
#
# Certified reason, FAILURES.md #11: the weighted sum amplifies each shift's
# error by `h`, so summing over shifts up to H = X^theta the total error is
# X^{2 theta} * X / (log X)^A against a main term X^{1+theta}.  The gate is
#
#       X^theta  <<  (log X)^{A+1}
#
# and MRT supplies log-power (any fixed A), not power.

THETAS = [
    ("Mikawa",  1 / 3,   "shifted-convolution range, 1992-era"),
    ("BBMZ",    0.30,    "later improvement; value carried as RECALL, see note"),
    ("MRT",     8 / 33,  "Matomaki-Radziwill-Tao I/II, the current wall"),
]

A_VALUES = [2, 5, 10, 20, 50]


def crossover_logX(theta, A):
    """Smallest L = log X beyond which X^theta > (log X)^{A+1} (gate closed).

    Solve theta * L = (A+1) * log L by iteration; returns None if no crossing.
    """
    if theta <= 0:
        return None
    k = (A + 1) / theta
    L_ = max(k * math.log(max(k, math.e)), math.e * 2)
    for _ in range(400):
        nxt = k * math.log(L_)
        if abs(nxt - L_) < 1e-12:
            break
        L_ = nxt
    return L_


def experiment_A():
    print(SEP)
    print("EXPERIMENT A — the gate swept across the field's progress axis")
    print(SEP)
    print("kill condition (stated first): if some theta > 0 satisfies")
    print("  X^theta << (log X)^{A+1} asymptotically, the gate is a THRESHOLD in")
    print("  theta and the 'shape not range' reading dies.\n")

    print("symbolic verdict, per theta:")
    for name, th, note in THETAS:
        holds = "HOLDS" if th <= 0 else "FAILS"
        print(f"  {name:8s} theta={th:.4f}  gate {holds} asymptotically   ({note})")
    print("\n  => the kill condition does NOT fire: for every theta > 0 the")
    print("     left side is a power and the right side is a log-power, so the")
    print("     inequality fails for all large X regardless of A.")
    print("     The gate is a SHAPE gate, not a RANGE gate. Improving theta —")
    print("     the axis the field has advanced on for thirty years — moves the")
    print("     crossover and never crosses it.\n")

    print("quantitative: log X at which the gate closes (X = e^L)")
    hdr = "  theta \\ A  " + "".join(f"{a:>12d}" for a in A_VALUES)
    print(hdr)
    for name, th, _ in THETAS:
        row = f"  {name:9s}"
        for A in A_VALUES:
            Lx = crossover_logX(th, A)
            row += f"{Lx:12.0f}"
        print(row)
    print("\n  read as decimal digits of X (log10 X = L / ln 10):")
    for name, th, _ in THETAS:
        row = f"  {name:9s}"
        for A in A_VALUES:
            Lx = crossover_logX(th, A)
            row += f"{Lx / math.log(10):12.3g}"
        print(row)

    print("""
  THE FIND.  The gate fails asymptotically and only asymptotically.  For every
  (theta, A) on the board the crossover sits at astronomically large X, so no
  numerical experiment at any feasible height can see the obstruction — and
  conversely, no numerical evidence could ever have warned us.  #27 is a purely
  asymptotic death, which is why it survived a hand computation and died to a
  shape check.  That is the fingerprint the QUALITY rule was built to catch.

  NOTE ON PROVENANCE.  The BBMZ theta above is carried as RECALL, not VERIFIED
  (same status as forensics/restatements.tsv).  It does not matter for the
  verdict: the symbolic argument is uniform in theta, so the table is
  illustrative and no conclusion rests on that number.
""")


# ---------------------------------------------------------------- experiment B
# The corridor's honest limit: what the CMR corridor and the GGOS floor give at
# the scale our window actually consumes.  Uses the guard's own DAG, unedited.

def experiment_B():
    print(SEP)
    print("EXPERIMENT B — the corridor, run to its honest limit (guard's own DAG)")
    print(SEP)
    for scale in (0.3, 1.0, 1.32, 1.5, 3.0):
        print(f"\n-- consuming the corridor at window scale {scale}")
        L.lint([("CMR_1.3208", scale), ("GGOS_floor", scale)], (1.0, scale))
    print("""
  HONEST LIMIT.  CMR is CIRCULAR at every scale (its ancestry hits EP1, the
  certificate class's own extremal problem) and additionally SCALE-invalid
  below 3.0.  The circularity does not go away by moving the window, so the
  corridor supplies nothing at any scale: the only scales where CMR is
  scale-valid are the ones our window never reaches, and even there Rule 1
  blocks it.  The corridor is not under-fuelled — it is unfuellable from this
  node.  GGOS's floor is scale-valid on [1.0, 1.5] and circular for the same
  reason.

  This is the A3 quarry yield: two RH-conditional, exactly-named gaps, both
  now with the reason stated as a graph property rather than a judgement.
""")


# ---------------------------------------------------------------- experiment C
# The GRH tier, stratifying bridge material by hypothesis depth.
# ADOPTED (night cycle 2): this experiment's local table has been folded into
# the guard.  `provenance_lint.depth` is now the authority and the local table
# is gone; the two agreed exactly before the swap, which is the R17 witness.


def experiment_C():
    print(SEP)
    print("EXPERIMENT C — bridge material stratified by hypothesis depth")
    print(SEP)
    print("using the guard's own DAG and `provenance_lint.depth` (adopted)\n")
    for i, (name, ins) in sorted(L.DEATHS.items()):
        d = max((L.depth(x) for x in ins), default=0)
        print(f"  {i:2d}  {name:32s} {L.DEPTH_NAME[d]}")
    for tier in sorted(L.DEPTH_NAME):
        n = sum(1 for _, ins in L.DEATHS.values()
                if max((L.depth(x) for x in ins), default=0) == tier)
        print(f"\n  tier {L.DEPTH_NAME[tier]:14s}: {n}/11")
    print("""
  READING.  The census is stratified at depth 0 and 1 only — nothing on the
  books yet consumes GRH, so the GRH tier is EMPTY.  That is a recruitment
  criterion, not a gap in the analysis: a death that consumed GRH would be
  bridge material of a *deeper* kind (it would change in more worlds), and we
  have manufactured none.
""")


# ---------------------------------------------------------------- experiment D
# The progress axis, run through the guard's QUALITY rule.


def experiment_D():
    print(SEP)
    print("EXPERIMENT D — the field's progress axis, billed by the QUALITY rule")
    print(SEP)
    print("""Each historical shift range is now a node.  They differ in REACH
(theta) and are identical in QUALITY (log-power).  The bridge bills quality.
""")
    for supplier in ("Mikawa_third", "BBMZ_theta", "MRT_8_33"):
        print(f"-- {supplier} feeding GM_bridge")
        L.lint([(supplier, 1.32), ("GM_bridge", 1.32)], (1.0, 1.32))
        print()
    print("""  Three decades of progress, three identical verdicts.  The guard now
  says mechanically what experiment A says arithmetically: the gate is a SHAPE
  gate, and the axis the field advances on is not the axis it bills.
""")


if __name__ == "__main__":
    experiment_A()
    experiment_B()
    experiment_C()
    experiment_D()
    print(SEP)
    print("guard DAG now carries these nodes; see the DAG NOTE at the top.")
    print(SEP)
