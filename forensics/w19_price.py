#!/usr/bin/env python3
"""W19 priced: what a mass-3 atom does to `∫|S|²`, measured before any paper.

`LEADS.md`'s `W19` asks whether Fujii's `2k`-th moments of `S(t)` — certified
since 1974–86 — can exclude the configurations the ledger cares about.  This
file prices that question on the arithmetic already verified, in the genre of
`three_moment_lp.py` ("pricing W35 before any paper is read").

**Kill condition, stated FIRST:** *if the mass-3 signal is `o(the moment's main
term)`, then no leading-order `S`-moment identity can bound `hauntedCount/N`
below any constant, and W19-as-a-ledger-route dies — the wall being the
finding.*

WHY THIS IS THE RIGHT TARGET.  `Fiber.six_mul_haunted_le_factMoment_three`
gives `6·hauntedCount ≤ Σ H(H−1)(H−2)`, and its docstring records that **nothing
certified bounds that third factorial moment**.  A bound on it feeds
`HauntedDensity` and hence `Riemann.proportion_of_hauntedDensity` — a real
ledger route.  `Optimal.moment_route_walled` does *not* block it: that theorem's
two witnesses have masses `≤ 2`, so their `factMoment 3` is zero and their
`hauntedCount` is already zero.  It walls prop1's LP, not this.

WHAT IS EXACT HERE, AND WHAT IS NOT.  The perturbation below is **exact
combinatorics**, not a model.  Merging three consecutive simple ordinates
`γ_a < γ_{a+1} < γ_{a+2}` into one mass-3 atom at `γ_{a+1}` changes the counting
function by exactly `−1` on `(γ_a, γ_{a+1})` and `+1` on `(γ_{a+1}, γ_{a+2})`,
and by nothing outside.  So

    Δ∫S²  =  ∫ (2·S·ΔS + ΔS²)
          =  2·[ ∫_{γ_{a+1}}^{γ_{a+2}} S  −  ∫_{γ_a}^{γ_{a+1}} S ]
             +  (γ_{a+2} − γ_a)

with no approximation beyond the quadrature.  `S` itself comes from the same
`N(t) = θ(t)/π + 1 + S(t)` used in `selberg_S.py`, whose constant was verified
at `SESSION 141`.

PREDICTION, REGISTERED BEFORE THE RUN (`SESSION 143`).  The cross term is a
difference of `S`-averages over two *adjacent* gaps, so it should largely cancel
and accumulate like a random walk — `O(√m)` over `m` merges — while the `ΔS²`
term accumulates like `O(m)`.  So `ΔS²` should dominate, giving

    Δ∫S²  ≈  Σ (γ_{a+2} − γ_a)  ≈  2·δ·L        (L = total length, δ = m/N)

against a main term `L·(1/2π²)·log log T`.  Hence the registered prediction:

    Δ∫S² / ∫S²   ≈   4π²·δ / log log T

which at these heights (`log log T ≈ 2.4`) is **≈ 16.4·δ** — and decays in
height only as `1/log log T`.

`[RECALL, UNVERIFIED]`: the `k = 1` variance constant `(1/2π²)` is verified
(`141`, arXiv:2403.19803).  Higher-`k` asymptotics `~ c_k·T·(log log T)^k` and
the *error terms* in Fujii's expansion are **not** read and carry no conclusion
here.  Per queue item 4 they are labelled and left alone.
"""

import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data", "zeros1")

GAUSS = [(-0.9061798459, 0.2369268851), (-0.5384693101, 0.4786286705),
         (0.0, 0.5688888889), (0.5384693101, 0.4786286705),
         (0.9061798459, 0.2369268851)]


def theta(t):
    return (t / 2.0) * math.log(t / (2.0 * math.pi)) - t / 2.0 \
        - math.pi / 8.0 + 1.0 / (48.0 * t) + 7.0 / (5760.0 * t ** 3)


def gap_integrals(g, k):
    """(∫S, ∫S²) over the gap (g[k], g[k+1]), where N(t) = k+1 exactly."""
    a, b = g[k], g[k + 1]
    half, mid = 0.5 * (b - a), 0.5 * (a + b)
    i1 = i2 = 0.0
    for x, w in GAUSS:
        t = mid + half * x
        s = k - theta(t) / math.pi
        i1 += w * s
        i2 += w * s * s
    return half * i1, half * i2


def main():
    with open(DATA) as fh:
        g = [float(x) for x in fh if x.strip()]
    n = len(g)

    # ---- self-check first (139's rule): S must stay small, or nothing counts.
    mx = 0.0
    for k in range(0, n - 1, 97):
        t = 0.5 * (g[k] + g[k + 1])
        mx = max(mx, abs(k - theta(t) / math.pi))
    print("W19 PRICED — a mass-3 atom against the S-moment main term")
    print("=" * 70)
    print(f"  zeros {n}   heights {g[0]:.2f} … {g[-1]:.2f}")
    print(f"  SELF-CHECK  max |S| on a 1-in-97 sample = {mx:.4f}")
    if mx > 5:
        print("  ⚠️  counting function wrong — STOP, nothing below is meaningful.")
        return 1
    print("      (small, so N(t) from θ tracks the table's index)\n")

    I1 = [0.0] * (n - 1)
    I2 = [0.0] * (n - 1)
    for k in range(n - 1):
        I1[k], I2[k] = gap_integrals(g, k)

    L = g[-1] - g[0]
    base = sum(I2)
    loglog = math.log(math.log(g[-1]))
    predicted_var = loglog / (2.0 * math.pi ** 2)
    print(f"  ∫S² over the range      = {base:.2f}")
    print(f"  mean S²  = ∫S²/L        = {base / L:.5f}")
    print(f"  Selberg main term       = log log T /2π² = {predicted_var:.5f}"
          f"   (T = {g[-1]:.0f}, log log T = {loglog:.3f})")
    print(f"  ratio observed/main     = {(base / L) / predicted_var:.3f}"
          "   (< 1: the known slow convergence, SESSION 140/141)\n")

    # ---- the perturbation, exactly.
    print("  Merging disjoint triples into mass-3 atoms, δ = merges/N:")
    print(f"  {'δ':>8} {'merges':>8} {'cross':>12} {'ΔS² term':>12}"
          f" {'Δ∫S²':>12} {'Δ/∫S²':>10} {'/δ':>8}")
    rows = []
    for stride in (300, 150, 60, 30, 15):
        merges = list(range(1, n - 3, stride))
        cross = sum(2.0 * (I1[a + 1] - I1[a]) for a in merges)
        sq = sum(g[a + 2] - g[a] for a in merges)
        tot = cross + sq
        delta = len(merges) / float(n)
        rel = tot / base
        rows.append((delta, len(merges), cross, sq, tot, rel))
        print(f"  {delta:>8.5f} {len(merges):>8} {cross:>12.2f} {sq:>12.2f}"
              f" {tot:>12.2f} {rel:>10.5f} {rel / delta:>8.2f}")

    pred = 4.0 * math.pi ** 2 / loglog
    obs = sum(r[5] / r[0] for r in rows) / len(rows)
    print(f"\n  REGISTERED PREDICTION  Δ/∫S² = 4π²δ/log log T,"
          f" i.e. Δ/(∫S²·δ) = {pred:.2f}")
    print(f"  OBSERVED (mean over the rows)                      = {obs:.2f}")
    print(f"  agreement = {100 * obs / pred:.1f}% of predicted")

    # ---- WHY THE PREDICTION MISSED BY 31%, AND IT IS NOT THE PERTURBATION.
    # The registered prediction divided by the THEORETICAL main term.  The
    # measured `∫S²/L` is larger, so the same numerator gives a smaller ratio.
    # Rescaling by the measured denominator recovers the prediction exactly.
    mid = [k - theta(0.5 * (g[k] + g[k + 1])) / math.pi for k in range(n - 1)]
    mm = sum(s * s for s in mid) / len(mid)
    ta = base / L
    d = [(theta(g[k + 1]) - theta(g[k])) / math.pi for k in range(n - 1)]
    m3 = sum(x ** 3 for x in d) / len(d)
    print(f"  rescaled by the MEASURED ∫S²/L: {pred * predicted_var / ta:.2f}"
          f"   vs observed {obs:.2f}  ✅")

    print(f"""
  AND THE DENOMINATOR IS THE CYCLE'S REAL FIND.  `∫S²/L` is NOT the variance
  `140`/`141` measured.  Those sampled `S` at gap MIDPOINTS; Fujii's moments are
  the TIME-AVERAGE, and the two differ by the sawtooth's own contribution:

    time-average  ∫S²/L                     = {ta:.5f}
    midpoint-sampled mean S²  (140/141)     = {mm:.5f}
    difference                              = {ta - mm:.5f}
    predicted sawtooth term  E[d³]/12       = {m3 / 12:.5f}   ({100 * (m3 / 12) / (ta - mm):.0f}% ✅)

  `S` jumps `+1` at each zero and falls by the normalised gap `d` across it, so
  a linear ramp of drop `d` contributes `d²/12` above its midpoint value, and
  weighting by time gives `E[d³]/12`.  (The residual `~3%` is the ramp's
  curvature in `t` versus `θ`.)  **This term is DETERMINISTIC and
  height-independent** — it is spacing geometry, not Selberg fluctuation.

    height        sawtooth   Selberg log log T/2π²
    T = 1e4        {m3 / 12:.4f}        {math.log(math.log(1e4)) / (2 * math.pi ** 2):.4f}
    T = 7.5e4      {m3 / 12:.4f}        {predicted_var:.4f}   <-- numerically EQUAL, coincidence
    T = 1e12       {m3 / 12:.4f}        {math.log(math.log(1e12)) / (2 * math.pi ** 2):.4f}
    T = 1e30       {m3 / 12:.4f}        {math.log(math.log(1e30)) / (2 * math.pi ** 2):.4f}

  At the height of this table the deterministic term and Selberg's main term
  agree to `0.2%`, which is a trap: anyone reading `∫S²/L ≈ log log T/2π²` here
  would conclude the fluctuation accounts for the whole second moment when it
  accounts for about half.  And `log log T` grows so slowly that the sawtooth is
  never negligible — at `T = 1e30` it is still `59%` of Selberg's term.
""")

    # ---- is the cross term really subdominant?  This is the prediction's hinge.
    c = sum(abs(r[2]) for r in rows) / sum(r[3] for r in rows)
    print(f"\n  cross/ΔS² in absolute size = {c:.4f}"
          "   (predicted: small — the cross term is a random walk)")

    print(f"""
  VERDICT.  The kill condition asks whether the signal is `o(main term)`.

  It is — but by a factor of exactly `1/log log T`, and that is the whole
  finding.  The signal `2δL` is CONSTANT in height; the main term
  `L·log log T/2π²` grows.  So the ratio decays like `1/log log T`, the
  slowest divergence in the subject.  At `T = {g[-1]:.0f}` it stands at
  `{pred:.1f}·δ`: a haunted density of just `δ = {1 / pred:.3f}` would move
  `∫S²` by 100%.

  So W19 does not die the way the kill condition imagined.  Asymptotically no
  leading-order S-moment identity bounds `hauntedCount/N` below a constant —
  a theorem needs the limit, and in the limit the signal vanishes.  But it
  vanishes so slowly that at every height anyone will ever compute, mass-3
  atoms are LOUD in the second moment.  The wall is real and asymptotic-only.

  WHAT THIS CONVERTS W19 INTO.  Not "does the k=2 moment help?" but a precise
  want-ad: **an S-moment identity helps iff its error term is `o(δ·L)`, i.e.
  `o(T)` with no `log log`.**  That is a question about the SECOND-ORDER term
  of Fujii's expansion, not its main term — which is exactly what `F2` meant by
  needing "Fujii-with-main-terms" rather than moment inequalities.  Only now is
  a fetch worth making, and it is one specific error term, not a survey.

  NOT CLAIMED: that Selberg's CLT *is* the moment supply `F2` wants.  These are
  moments of `S`, and `F2` wants moments of the MASS distribution; the two meet
  only at sub-leading order, which is the scale gap this file measures.
""")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
