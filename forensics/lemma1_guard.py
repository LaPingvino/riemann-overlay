#!/usr/bin/env python3
"""S-witness for container arithmetic (Goldston, arXiv:math/0412313, Lemma 1).

Under RH:  int_B^{B+1} F(alpha) d(alpha) <= 3,  uniformly for ANY B >= 1.

Any model of the form factor past support 1 must satisfy this. Run every
candidate input through `check` BEFORE building a table; a model that violates
it is not merely unsound, it is RH-impossible, and every number derived from it
is decoration. (This guard, applied retroactively, killed the c >= 4 rows of
day cycle 5-6 and with them the published break-even thresholds.)
"""
def check(D, lam, name="model", grid=2000):
    """D: callable on [1, lam]. Returns (ok, worst_B, worst_mass)."""
    worst = (0.0, None)
    B = 1.0
    while B + 1.0 <= max(lam, 2.0) + 1e-9:
        n = 400; h = 1.0 / n
        mass = sum(D(B + (i + 0.5) * h) * h for i in range(n))
        if mass > worst[0]:
            worst = (mass, B)
        B += 1.0 / grid
    ok = worst[0] <= 3.0 + 1e-9
    print(f"  {name:28s} worst unit-window mass {worst[0]:7.4f} at B={worst[1]:.3f}"
          f"   {'OK' if ok else 'VIOLATES RH (Lemma 1)'}")
    return ok, worst[1], worst[0]

if __name__ == "__main__":
    print("guard self-test:")
    for c in (1.0, 2.0, 3.0, 4.0):
        check(lambda u, c=c: c, 2.5, f"constant D = {c}")
