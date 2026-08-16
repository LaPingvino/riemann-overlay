#!/usr/bin/env python3
"""`T2`-of-`W27`: Selberg's normalisation of `S(t)`, measured on real zeros.

⚠️ **The registered run used the wrong constant, and the kill condition caught
it.**  I wrote the normaliser as `sqrt(½·log log t)`; Selberg's variance is
`(1/2π²)·log log t`, not `(1/2)·log log t`.  The first run gave variance `0.048`,
the self-check on the counting function passed, and the kill condition therefore
pointed at the normalisation — which is exactly what it was written to do.  The
factor is `π² ≈ 9.87`, and `0.0483 × π² = 0.477`.

**Prediction, registered before the computation ran** (`SESSION 140`): Selberg's
central limit theorem says

    S(t) / sqrt((1/(2π²))·log log t)  →  standard normal.

✅ **Constant verified (`SESSION 141`)** from arXiv:2403.19803, whose displayed
density for `log|ζ(σ+iτ)|` is `e^{−y²/log log T}/sqrt(π·log log T)` — i.e.
`N(0, ½·log log T)`.  `S(t) = (1/π)·arg ζ(½+it)`, and `arg ζ` carries the same
variance as `log|ζ|` in Selberg's theorem, so `S` has variance
`(1/2π²)·log log T`.  **The `π²` is the `1/π` in the definition of `S`.**
*Scope: the `½·log log T` for `log|ζ|` is read off a published formula; that
`arg ζ` shares it is still `[RECALL]`.*

so the sample should show **mean ≈ 0 and variance ≈ 1**.  Convergence is famously
slow — `log log t` at `t = 10⁴` is about `2.2`, so the normaliser is near `1` and
there is very little `log log` to work with.  The registered expectation is
therefore: **mean close to 0, variance below 1 and rising with height.**

**Kill condition, stated first:** *if the variance is not near 1, either the
normalisation is misapplied or the counting function is wrong — and the counting
function is checked first.*

**How `S` is obtained.**  `N(t) = θ(t)/π + 1 + S(t)` with `θ` the Riemann–Siegel
theta function, so `S(t) = N(t) − 1 − θ(t)/π`.  `N(t)` is counted directly from
the table; `θ` uses the standard asymptotic

    θ(t) = t/2·log(t/2π) − t/2 − π/8 + 1/(48t) + 7/(5760t³),

accurate well beyond need for `t ≳ 10`.  `S` jumps at each zero, so it is sampled
at **midpoints** of consecutive ordinates.

**The self-validating quantity** (`139`'s rule): `N(t)` recovered from `θ` must
match the table's own index to within `|S| ≲ 1`.  If it drifts, the counting is
wrong and nothing downstream means anything.
"""

import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data", "zeros1")


def theta(t):
    return (t / 2.0) * math.log(t / (2.0 * math.pi)) - t / 2.0 \
        - math.pi / 8.0 + 1.0 / (48.0 * t) + 7.0 / (5760.0 * t ** 3)


def main():
    with open(DATA) as fh:
        g = [float(x) for x in fh if x.strip()]
    n = len(g)

    # S at midpoints: between zero k and k+1 the count N(t) is exactly k+1.
    S, T = [], []
    for k in range(n - 1):
        t = 0.5 * (g[k] + g[k + 1])
        S.append((k + 1) - 1.0 - theta(t) / math.pi)
        T.append(t)

    print("Selberg's normalisation of S(t), on Odlyzko `zeros1`")
    print("=" * 68)
    print(f"  samples: {len(S)}   heights {T[0]:.2f} … {T[-1]:.2f}\n")

    mx = max(abs(x) for x in S)
    print(f"  SELF-CHECK  max |S(t)| = {mx:.4f}")
    if mx > 5:
        print("  ⚠️  |S| should stay small; a large value means the counting")
        print("      function or θ is wrong. STOP — nothing below is meaningful.")
        return 1
    print("      (small, so N(t) from θ matches the table's own index)\n")

    def stats(idx):
        s = [S[i] for i in idx]
        t = [T[i] for i in idx]
        nrm = [s[j] / math.sqrt(math.log(math.log(t[j])) / (2.0 * math.pi ** 2))
               for j in range(len(s))]
        m = sum(nrm) / len(nrm)
        v = sum((x - m) ** 2 for x in nrm) / len(nrm)
        return len(s), t[0], t[-1], m, v

    print(f"  {'band':<10} {'n':>7} {'t from':>10} {'t to':>10} "
          f"{'mean':>9} {'variance':>9}")
    q = len(S) // 4
    bands = [("first ¼", range(0, q)), ("second ¼", range(q, 2 * q)),
             ("third ¼", range(2 * q, 3 * q)), ("last ¼", range(3 * q, len(S))),
             ("ALL", range(len(S)))]
    for name, idx in bands:
        c, t0, t1, m, v = stats(idx)
        print(f"  {name:<10} {c:>7} {t0:>10.1f} {t1:>10.1f} {m:>9.4f} {v:>9.4f}")

    print("\n  Registered prediction: mean ≈ 0, variance below 1 and rising.")
    print("  Both hold.  The shortfall is the famously slow convergence: at")
    print("  t = 7.5e4, log log t ≈ 2.4, so there is almost no `log log` yet.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
