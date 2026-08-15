#!/usr/bin/env python3
"""The three-moment LP — pricing W35 before any paper is read.

`Optimal.prop1_LP_optimal` proves the two-moment world is exhausted: under a
star bound `C`, no linear bound in `(N, N⊛)` beats `2 − C`.  W35 proposes
supplying a third moment `Σ m³`.  Before fetching that literature, the question
that decides whether it is worth fetching:

    given `N⊛ ≤ C·N` AND `Σm³ ≤ C₃·N`, what proportion can a linear bound in
    three moments certify?

**Kill condition, stated first:** *if the three-moment optimum is still `2 − C`,
the third moment buys nothing and W35 dies cheaply.*

WHAT HAPPENED.  claude.ai registered a hand derivation before this ran.  Its
algebra is **exactly right** (verified below in rationals) — and following it
through produces a certified proportion **above 1**, which is impossible.  So
the finding is not a price.  It is that the program as posed is **unbounded**,
and unboundedness localises the defect.

THE FAMILY (claude.ai's, verified).  `(a, b, c) = (2 − 2s, 3s − 1, −s)`:

    a + m·b + m²·c  =  (2 − m) − s(m − 1)(m − 2)

which is `1` at `m = 1`, `0` at `m = 2`, and `≤ 0` for every `m ≥ 2, s ≥ 0`.
So the family is feasible against every single-atom test, for all `s ≥ 0`, and

    value(s)  =  (2 − C) + s·(3C − 2 − C₃).

THE DEFECT.  `(−2, 3, −1)` is a recession direction of the single-atom
constraint set, so whenever `3C − 2 > C₃` the value grows without bound.  At
`C = 3/2`, `C₃ = C² = 9/4`, `s = 5` it certifies `7/4` — 175% of the zeros
simple, from a feasible point.  A valid bound cannot do that, so a hypothesis is
wrong, and it is not the algebra.

WHERE IT IS WRONG.  `C₃ ≥ C²` (Cauchy–Schwarz) is a *necessary* realizability
condition and nowhere near sufficient for **integer** atom masses.  Equality
`C₃ = C²` forces every atom to have the same mass `C`; `C = 3/2` is therefore
not realizable at all, and the LP was being asked to price an input pair no
configuration can present.

So the honest verdict is neither "the third moment helps" nor "it does not":
**the question is not yet well-posed**, and what is missing is the realizable
region of `(C, C₃)` for integer masses — which is a `W7`-shaped problem
(realizability), the genre this project has hit before.
"""

from fractions import Fraction as F

SEP = "=" * 74


def constraint(s, m):
    """a + m·b + m²·c for the family, as an exact rational."""
    a, b, c = 2 - 2 * s, 3 * s - 1, -s
    return a + m * b + m * m * c


def value(s, C, C3):
    a, b, c = 2 - 2 * s, 3 * s - 1, -s
    return a + b * C + c * C3


def main():
    print(SEP)
    print("THREE-MOMENT LP — claude.ai's family, verified, and what it exposes")
    print(SEP)

    print("\n1. The family is feasible against every single-atom test, all s >= 0")
    print("   identity  a + m b + m^2 c = (2 - m) - s(m-1)(m-2)")
    ok = True
    for s in (F(0), F(1, 2), F(1), F(5), F(100)):
        for m in range(1, 40):
            lhs = constraint(s, m)
            rhs = (2 - m) - s * (m - 1) * (m - 2)
            ok &= lhs == rhs
            ok &= (lhs <= 1) if m == 1 else (lhs <= 0)
    print(f"   identity and feasibility hold on every tested (s, m): {ok}")

    print("\n2. The objective is (2 - C) + s(3C - 2 - C3), exactly")
    for C, C3 in ((F(3, 2), F(9, 4)), (F(3, 2), F(5, 2))):
        for s in (F(0), F(1), F(5)):
            v, pred = value(s, C, C3), (2 - C) + s * (3 * C - 2 - C3)
            assert v == pred
            print(f"   C={C}  C3={C3}  s={s:>3}  ->  {v}"
                  f"{'   <-- exceeds 1, impossible' if v > 1 else ''}")

    print("""
3. VERDICT — the kill condition neither fired nor was answered.

   `(-2, 3, -1)` is a recession direction of the single-atom constraint set, so
   the program is UNBOUNDED whenever `3C - 2 > C3`, and it certifies impossible
   proportions from feasible points.  A valid bound cannot exceed 1, so a
   hypothesis is wrong — and the algebra was checked above in exact rationals,
   so it is not the algebra.

   The wrong hypothesis is the realizable region.  `C3 >= C^2` is necessary and
   far from sufficient over INTEGER atom masses: equality forces all atoms to
   share one mass `C`, so `C = 3/2` is not realizable by any configuration at
   all.  The LP was pricing input pairs no configuration can present.

   So W35 is neither alive nor dead.  What it needs first is the realizable
   region of `(C, C3)` for integer masses — a W7-shaped realizability problem,
   and this project's own genre.
""")


if __name__ == "__main__":
    main()
