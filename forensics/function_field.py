#!/usr/bin/env python3
"""W36, started: the ledger's quantities computed on real arithmetic.

**Why this runs when the rest of the data column cannot.**  `133` escalated that
the VPS holds no zero tables and reaches only `github.com`.  Function fields need
**no downloaded data**: Frobenius eigenvalues are computed by counting points.
This is the project's first contact with arithmetic reality, and it is exact —
integer point counts, exact rational polynomial gcd, no floating point anywhere.

⚠️ **First run had an off-by-one and it changed the answer.**  I added *two*
points at infinity; `y² = f(x)` with `deg f = 5` (odd) has exactly **one**.  The
uncorrected run reported a repeated eigenvalue for `y² = x⁵+5` over `F_11` that
is not there.  Recorded rather than quietly fixed: the point count is the entire
input, and an arithmetic slip in it is indistinguishable from a finding.

**The setting.**  For a genus-2 hyperelliptic curve `y² = f(x)` over `F_p`, the
zeta numerator is

    P(T) = 1 - e1·T + e2·T² - p·e1·T³ + p²·T⁴,

with `e1, e2` from the point counts `N1 = #C(F_p)`, `N2 = #C(F_p²)` via Newton's
identities on `s_k = p^k + 1 - N_k`.  Weil's theorem — RH for curves — puts every
root on `|α| = √p`.  **So `offAt ≡ 0` by theorem**, and `hauntedCount = 0`
identically: the function-field world is one where the project's central quantity
vanishes for a reason, which makes it the control.

**What is genuinely variable there is multiplicity.**  A repeated Frobenius
eigenvalue is an ordinate of mass `≥ 2` — our `H`.  `P` has a repeated root iff
`gcd(P, P') ≠ 1`, checked here in exact rational arithmetic.

So this measures, on real curves: `N`, `atomCount`, and the multiplicity profile —
three of the ledger's quantities, with ground truth attached.

**Hand-verified witness.**  `y² = x⁵ + 2x` over `F_7`: the affine count is `7`,
plus one point at infinity gives `N1 = 8`, so `s1 = 0` and `e1 = 0`.  With
`N2 = 78`, `s2 = -28` and `e2 = 14`, so

    P(T) = 1 + 14·T² + 49·T⁴ = (1 + 7·T²)²  —  a perfect square.

The Frobenius eigenvalue pair is **doubled**: an ordinate of mass `2`, in a world
where Weil's theorem puts every root on the critical line.  Checked by hand
against the script, because the point count is the entire input.
"""

from fractions import Fraction
import itertools


def poly_gcd(a, b):
    """Monic gcd of two polynomials over Q, coefficients low-degree-first."""
    def trim(p):
        while p and p[-1] == 0:
            p.pop()
        return p
    a, b = trim([Fraction(c) for c in a]), trim([Fraction(c) for c in b])
    while b:
        # a mod b
        r = a[:]
        while len(r) >= len(b) and r:
            coeff = r[-1] / b[-1]
            shift = len(r) - len(b)
            for i, bc in enumerate(b):
                r[i + shift] -= coeff * bc
            trim(r)
        a, b = b, r
    if a:
        lead = a[-1]
        a = [c / lead for c in a]
    return a


def count_points(f_coeffs, p, k):
    """#C(F_{p^k}) for y² = f(x), smooth model, counted in F_p^k via brute force.

    Only k = 1, 2 are needed for genus 2, and F_{p²} is built as F_p[i]/(i²-n)
    for a non-residue n — exact arithmetic in a quadratic extension.
    """
    if k == 1:
        squares = {(y * y) % p for y in range(p)}
        sq_count = {}
        for y in range(p):
            sq_count[(y * y) % p] = sq_count.get((y * y) % p, 0) + 1
        total = 0
        for x in range(p):
            v = 0
            for i, c in enumerate(f_coeffs):
                v = (v + c * pow(x, i, p)) % p
            total += sq_count.get(v, 0)
        return total + 1          # deg f = 5 is ODD: exactly ONE point at infinity
    # k = 2: elements a + b·w with w² = n, n a non-residue
    n = next(t for t in range(2, p) if pow(t, (p - 1) // 2, p) == p - 1)

    def mul(u, v):
        return ((u[0] * v[0] + n * u[1] * v[1]) % p, (u[0] * v[1] + u[1] * v[0]) % p)

    els = [(a, b) for a in range(p) for b in range(p)]
    sq_count = {}
    for y in els:
        s = mul(y, y)
        sq_count[s] = sq_count.get(s, 0) + 1
    total = 0
    for x in els:
        v = (0, 0)
        xp = (1, 0)
        for c in f_coeffs:
            v = ((v[0] + c * xp[0]) % p, (v[1] + c * xp[1]) % p)
            xp = mul(xp, x)
        total += sq_count.get(v, 0)
    return total + 1          # same, over the quadratic extension


def numerator(f_coeffs, p):
    """P(T) coefficients, low-degree-first, exact integers."""
    n1 = count_points(f_coeffs, p, 1)
    n2 = count_points(f_coeffs, p, 2)
    s1 = p + 1 - n1
    s2 = p * p + 1 - n2
    e1 = s1
    e2 = (e1 * s1 - s2) // 2
    return [1, -e1, e2, -p * e1, p * p], n1, n2


def main():
    print("W36 — Frobenius multiplicity on genus-2 curves, exact arithmetic")
    print("=" * 70)
    print("Weil: every root has |α| = √p, so off-line mass is ZERO by theorem.")
    print("The variable quantity is multiplicity: a repeated eigenvalue is an")
    print("ordinate of mass ≥ 2.  Repeated root  ⟺  gcd(P, P') ≠ 1, exact.\n")
    print(f"  {'p':>3} {'curve y²=f(x)':<26} {'N1':>4} {'N2':>5} "
          f"{'repeated?':>10}")
    total = rep = 0
    for p in (5, 7, 11):
        for c0, c1 in itertools.product(range(p), repeat=2):
            f = [c0, c1, 0, 0, 0, 1]          # y² = x⁵ + c1·x + c0
            P, n1, n2 = numerator(f, p)
            dP = [i * P[i] for i in range(1, len(P))]
            g = poly_gcd(P, dP)
            has_rep = len(g) > 1
            total += 1
            rep += has_rep
            if has_rep:
                print(f"  {p:>3} x⁵ + {c1}x + {c0:<18} {n1:>4} {n2:>5} "
                      f"{'YES':>10}")
    print(f"\n  curves examined: {total}")
    print(f"  with a repeated Frobenius eigenvalue: {rep}"
          f"   ({100*rep/total:.1f}%)")
    print("\n  Every one of these is an ordinate of mass ≥ 2 in a world where")
    print("  off-line mass is zero by theorem — i.e. crowding without haunting,")
    print("  which is exactly the configuration `NoHaunted` permits and RH-in-")
    print("  window forbids.  The function-field world is a witness that the two")
    print("  hypotheses are genuinely different, drawn from real arithmetic.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
