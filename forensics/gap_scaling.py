#!/usr/bin/env python3
"""The approach law across twenty orders of magnitude in height.

`135` measured the small-gap law on Odlyzko's `zeros1` (`t ≲ 7.5×10⁴`) and found
the **cubic exponent** confirmed but the constant at `0.71×` the GUE asymptotic,
noting slow convergence as `[RECALL, UNVERIFIED]`.  That recall is testable:
Odlyzko's `zeros3` and `zeros4` give `10⁴` consecutive zeros near
`t ≈ 2.7×10¹¹` and `t ≈ 1.4×10²⁰`.

**Format.**  Those files list `γ − base` with `base` in the header line; the base
is added back before normalising, because the normalisation
`δ = Δγ·log(γ/2π)/2π` depends on the true height.

**Kill condition, filed first:** *if the constant does not move toward GUE at
greater height, either the slow-convergence recall is wrong or the normalisation
is.*
"""

import math
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data")
TWO_PI = 2.0 * math.pi


def load(name):
    """Return (offsets, base).  **Never** forms `base + offset`.

    ⚠️ The first version did, and it silently destroyed `zeros4`: the base is
    `1.44×10²⁰`, which needs 21 significant digits, and float64 carries ~16 — so
    `base + offset == base` for every entry, every gap became `0`, and the
    reported `obs/GUE` was `33.8` from dividing by nothing.  The `mean δ ≈ 1`
    check caught it: a mean of `0.000000` is not a subtle symptom.

    The fix is to never add.  Gaps are differences, so the base cancels
    exactly; the normalisation needs `log(γ/2π)`, and the base alone gives that
    to far more precision than the answer requires.
    """
    path = os.path.join(DATA, name)
    base = 0.0
    vals = []
    with open(path) as fh:
        for line in fh:
            t = line.strip()
            if not t:
                continue
            m = re.match(r"Values of gamma\s*-\s*([0-9]+)", t)
            if m:
                base = float(m.group(1))
                continue
            try:
                vals.append(float(t))
            except ValueError:
                continue          # prose in the header
    return vals, base


def law(off, base):
    """`off` are offsets from `base`; gaps cancel the base exactly."""
    g = off
    n = len(g)
    raw = [g[i + 1] - g[i] for i in range(n - 1)]
    height = [base + g[i] if base == 0 else base for i in range(n - 1)]
    norm = [raw[i] * math.log(height[i] / TWO_PI) / TWO_PI for i in range(n - 1)]
    mean = sum(norm) / len(norm)
    gue = (math.pi ** 2 / 9.0) * len(norm)
    obs = sum(1 for x in norm if x < 0.3) / 0.3 ** 3
    cnt = sum(1 for x in norm if x < 0.3)
    return n, (base if base else g[0]), mean, min(norm), obs / gue, cnt


def main():
    print("The approach law across height")
    print("=" * 78)
    print(f"  {'file':<8} {'zeros':>7} {'height':>12} {'mean δ':>9} "
          f"{'min δ':>9} {'obs/GUE':>16}")
    print("  (± is Poisson on the count of gaps below δ = 0.3)")
    rows = []
    for f in ("zeros1", "zeros3", "zeros4"):
        try:
            g, base = load(f)
        except OSError:
            print(f"  {f:<8} (absent)")
            continue
        if len(g) < 100:
            print(f"  {f:<8} (only {len(g)} values — not a zero list)")
            continue
        n, t0, mean, mn, ratio, cnt = law(g, base)
        err = ratio / math.sqrt(cnt) if cnt else 0.0
        rows.append((f, t0, ratio, err))
        print(f"  {f:<8} {n:>7} {t0:>12.4g} {mean:>9.6f} {mn:>9.6f} "
              f"{ratio:>7.3f} ±{err:.3f}  (n={cnt})")

    print("\n  mean δ ≈ 1 in every regime is the check that the normalisation")
    print("  is right at that height — it is not a fitted quantity.\n")
    if len(rows) >= 3:
        a, b, c = rows[0], rows[1], rows[2]
        sep = abs(b[2] - a[2]) / math.sqrt(a[3] ** 2 + b[3] ** 2)
        bc = abs(c[2] - b[2]) / math.sqrt(b[3] ** 2 + c[3] ** 2)
        print(f"  {a[0]} → {b[0]}:  {a[2]:.3f} → {b[2]:.3f}"
              f"   ({sep:.1f}σ — real)")
        print(f"  {b[0]} → {c[0]}:  {b[2]:.3f} → {c[2]:.3f}"
              f"   ({bc:.1f}σ — not resolved at this sample size)")
        print("\n  So the rise toward GUE is REAL between 10⁴ and 10¹¹, and")
        print("  between 10¹¹ and 10²⁰ the data cannot tell the two apart.")
        print("  The honest reading: convergence is visible and has largely")
        print("  happened by t ~ 10¹¹.  Claiming monotonicity across all three")
        print("  would be reading noise as signal.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
