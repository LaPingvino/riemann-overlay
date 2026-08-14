#!/usr/bin/env python3
"""W16, re-priced: the vision problem is closed, so what does EVALUATION cost?

`landau_discriminates` (Riemann/Fiber.lean) closed the vision half: the Landau
weight `Σ_ρ x^β` separates the two fiber states of a crowded atom, by strict
AM-GM, for every `x > 1` and every depth.  What remains is evaluation — can the
discriminating quantity be certified on zeta's actual zeros?

This script prices it.  Nothing here is a theorem; it is arithmetic on stated
inputs, and every input is labelled by provenance.

INPUTS
  [LIT, RECALL]  Landau-Gonek:  Σ_{0<γ≤T} x^ρ = -(T/2π)Λ(x) + E(x,T),
                 with E ≪ x·log(2xT)·loglog(3x), uniformly in x > 1.
  [PROVED]       per-pair excess over the on-line chorus, exactly:
                 x^a + x^{1-a} - 2x^{1/2} = 2x^{1/2}(cosh(δ log x) - 1),
                 δ = |a - 1/2|.  (Riemann/Fiber.lean, landau_config + AM-GM.)
  [LIT]          Riemann-von Mangoldt: N(T) ≍ (T/2π)·log T.
  [CHOICE]       δ = 1/log T — the natural depth scale.  Then with x = T^c,
                 δ·log x = c exactly, so the per-pair excess is
                 2·x^{1/2}·(cosh c - 1): a CONSTANT multiple of the chorus term,
                 depending only on c.

THE POINT THE ARITHMETIC MAKES
  The excess is real and positive.  The explicit formula supplies it multiplied
  by e^{iγ log x}, one unknown phase per zero.  So the quantity we can compute
  is PHASED and the discriminator wants it UNPHASED, and that gap — not
  magnitude, not vision — is the whole evaluation problem.  Census #1 said this
  in words ("phases shared with the on-line chorus"); this file says it with a
  number.
"""

import math

SEP = "=" * 72


def excess_ratio(c):
    """Per-pair excess divided by the on-line chorus term, at x = T^c, δ=1/log T."""
    return math.cosh(c) - 1


def unphased_margin_log10(c, T_log10, kappa):
    """log10 of (aggregate UNPHASED excess) / (Landau-Gonek error).

    aggregate excess  ≈ κ·N(T)·x^{1/2}·(cosh c - 1),  N ≍ (T/2π) log T
    error             ≈ x·log(2xT)·loglog(3x),        x = T^c
    ratio             = κ·T^{1-c/2}·(cosh c - 1) / (2π·(1+c)·loglog x)
    """
    lnT = T_log10 * math.log(10)
    ll = max(math.log(max(c * lnT, math.e)), 1.0)
    log10ratio = (math.log10(kappa) + (1 - c / 2) * T_log10
                  + math.log10(math.cosh(c) - 1)
                  - math.log10(2 * math.pi * (1 + c) * ll))
    return log10ratio


def crossover_c(T_log10, kappa):
    """Largest c at which the unphased margin still exceeds 1."""
    lo, hi = 0.01, 5.0
    for _ in range(300):
        mid = (lo + hi) / 2
        if unphased_margin_log10(mid, T_log10, kappa) > 0:
            lo = mid
        else:
            hi = mid
    return lo


def main():
    print(SEP)
    print("W16 RE-PRICED — the evaluation problem, in the coordinate x = T^c")
    print(SEP)
    print("""
WILDCARD, kill condition stated first: if the crossover `c` at a height where
zeros are actually known (T ≲ 10^13) is ≤ 1, then the whole unpaid range
c ∈ (1,2) is unaffordable at every feasible height and the Landau route is dead
outright rather than merely unpaid.
""")

    print("per-pair excess as a multiple of the chorus term (δ = 1/log T):")
    print("  c      cosh(c)-1     asymptotic margin exponent (1 - c/2)")
    for c in (0.5, 1.0, 1.25, 1.5, 1.75, 2.0, 2.25):
        print(f"  {c:<7.2f}{excess_ratio(c):>9.4f}{1 - c / 2:>28.3f}")
    print("""
  Read: at x = T^c the excess is a fixed fraction of the on-line term, set by c
  alone.  The signal does not fade with T — it is scale-free in this coordinate.
  That is the AM-GM gap in its natural units.
""")

    print("UNPHASED aggregate margin (log10), κ = proportion off-line:")
    hdr = "  T \\ c    " + "".join(f"{c:>10.2f}" for c in (0.5, 1.0, 1.5, 2.0))
    print(hdr)
    for T_log10 in (6, 12, 24, 50, 100):
        row = f"  1e{T_log10:<7d}"
        for c in (0.5, 1.0, 1.5, 2.0):
            row += f"{unphased_margin_log10(c, T_log10, 0.01):>10.2f}"
        print(row)
    print("  (κ = 0.01; positive means the aggregate excess would clear the"
          " Landau-Gonek error)")

    print("\ncrossover c — the largest c whose unphased margin still clears 1:")
    print("  T          κ=1        κ=0.01     κ=1e-4")
    for T_log10 in (6, 12, 24, 50, 100, 300):
        row = f"  1e{T_log10:<9d}"
        for kappa in (1.0, 0.01, 1e-4):
            row += f"{crossover_c(T_log10, kappa):<11.3f}"
        print(row)

    print("""
VERDICT — the kill condition does NOT fire.

At T = 10^12 with κ = 0.01 the crossover is c ≈ 1.39 > 1.  So there is a
**nonempty window at feasible heights** in which the aggregate excess would
clear the unconditional error and the phase-killing device is NOT paid for:

        c ∈ (1, ≈1.39]  at T = 10^12,  widening to (1, 2) as T → ∞.

Two readings, both worth keeping.

1. THE BINDING CONSTRAINT IS THE PHASE, NOT THE MAGNITUDE.  Every margin above
   is computed for the UNPHASED sum.  What Landau-Gonek supplies is the phased
   sum: each excess arrives multiplied by e^{iγ log x} with γ unknown per zero.
   Killing the phase is what second moments in x do, and that device is paid
   only out to the diagonal.  So the price of the Landau route is exactly the
   price of one phase-removal, and everything else on this page is affordable.

2. THE ASYMPTOTIC PROMISE IS NOT THE FEASIBLE ONE — the same disease as #27,
   pointing the other way.  The exponent says every c < 2 eventually clears.
   At T = 10^12 the actual crossover is 1.39; reaching c = 1.9 needs T ≳ 10^50.
   #27's asymptotics were crueller than the numerics; here they are kinder.
   Both times the honest statement required computing the crossover instead of
   reading the exponent.

DICTIONARY CAVEAT, stated because the conclusion leans on it.  The
identification of "paid" with c ≤ 1 assumes the correspondence between this
coordinate and the pair-correlation support parameter (BGST's 𝓕 known for
support ≤ 1).  That dictionary is [RECALL, UNVERIFIED] — it is the same
h ↔ α check already open in the registers.  If the true correspondence is
c ≤ 2 rather than c ≤ 1, the unpaid window is empty and this page's second
reading collapses.  Nothing else on the page depends on it.
"""
          )


if __name__ == "__main__":
    main()
