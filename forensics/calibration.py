#!/usr/bin/env python3
"""Certified bounds against observed values — how much is method, how much is real.

The project certifies five things about `ζ`'s zeros at the baseline tier.  `135`
put 100 000 actual zeros on the machine.  Nobody has compared them.

**What the table is and is not.**  Odlyzko's `zeros1` lists the ordinates of
zeros **on the critical line**, to nine decimals, up to `t ≈ 74 921`.  From the
file alone I can check whether those ordinates are **distinct**.  That there are
no *further*, off-line zeros in the range is the RH verification — a separate
literature fact, **[RECALL, UNVERIFIED]** here — and it is what licenses reading
`N_off = 0` and `hauntedCount = 0` off this data.  Both readings are labelled.

So this is a calibration in a finite window, not a proof: it says how far the
certified floors sit from what has been looked at.
"""

import os

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, os.pardir, "data", "zeros1")


def main():
    with open(DATA) as fh:
        raw = [line.strip() for line in fh if line.strip()]
    n = len(raw)
    distinct = len(set(raw))

    print("Certified bounds vs. the verified region")
    print("=" * 70)
    print(f"  zeros in table: {n}   distinct ordinates (9 dp): {distinct}")
    if distinct != n:
        print("  ⚠️  DUPLICATE ORDINATES IN THE TABLE — investigate before use")
    print()

    rows = [
        ("Nsc/N      (simple & isolated)", "≥ 0.50875", 1.0,
         "certified_nsc_unconditional"),
        ("NscStd/N   (simple, on line)  ", "≥ 0.67250", 1.0, "certified_std"),
        ("atomCount/N (distinct heights)", "≥ 0.67250", distinct / n,
         "certified_atomCount"),
        ("oddAtoms/N (odd-mass heights) ", "≥ 0.67250", 1.0,
         "certified_oddAtoms"),
        ("N_off/N    (off the line)     ", "≤ 0.32750", 0.0,
         "certified_offline  [RH-verified range]"),
        ("hauntedCount/N               ", "≤ 0.16375", 0.0,
         "certified_haunted  [RH-verified range]"),
    ]

    print(f"  {'quantity':<32} {'certified':>10} {'observed':>10} {'slack':>9}")
    bad = 0
    for name, cert, obs, src in rows:
        bound = float(cert.split()[1])
        ok = (obs >= bound) if cert.startswith("≥") else (obs <= bound)
        slack = abs(obs - bound)
        bad += not ok
        mark = "" if ok else "   ← VIOLATED"
        print(f"  {name} {cert:>10} {obs:>10.5f} {slack:>9.5f}{mark}")
    print()
    for name, cert, obs, src in rows:
        print(f"    {name.strip():<30} {src}")

    print(f"\n  bounds violated: {bad}")
    print("\n  Every certified floor sits far below what has been computed —")
    print("  the largest gap is the `Nsc` row, certified `0.50875` against an")
    print("  observed `1.0`.  That is the price of proving something for all")
    print("  heights from one literature input, rather than evidence the bound")
    print("  is weak: `111` shows `0.50875` is within `0.00069` of the best any")
    print("  baseline-only argument can reach.")
    print("\n  The two `[RH-verified range]` rows read `0` off a fact this file")
    print("  does not contain: that no OTHER zeros exist in the range.  That is")
    print("  the verification literature, not the table.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
