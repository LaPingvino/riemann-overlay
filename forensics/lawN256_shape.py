#!/usr/bin/env python3
"""What the vendored `LawN256` enclosure table actually contains.

**Why this exists.**  Rung 0 is blocked on `cert_N256_blk_b128m.json`, which
`265` showed is not published: it appears once at the pinned commit, as a
filename and `sha256` in `LawN256.lean`'s header, and nowhere else.  `266` asked
the next question — could the certificate be *regenerated* from what is on disk?
— and the answer needs the table looked at rather than assumed.

**What the table is.**  `Zeta23/PairCeiling/LawN256.lean` carries `256`
enclosures `(lo_j, hi_j)` of `K·S(j)` at scale `K = 2^140`, where `S` is the form
factor of a `256`-periodic law.  Every interval has width exactly `1`, so each
pins `S(j)` to one unit in the last place at `2^-140`.

**And 255 of the 256 are a closed form.**  For `1 ≤ j ≤ 255`,
`(lo_j, hi_j)` is `(j·2^132 − 1, j·2^132)` or `(j·2^132, j·2^132 + 1)` — that is,
`S(j) = j/256` to one ulp, which is exactly what `RowCert.lean`'s
`|256·S(j) − j| ≤ 3/10^40` already asserts.  Those entries carry no information
the row certificate does not.

**The `j = 256` entry is the one that carries the law.**  It encloses
`S(256) ≈ 211.432009142486` and is not of that form; it is the periodic value the
row certificate says nothing about.

**Why that matters to the ruling.**  Regenerating the certificate needs the law —
the weights `w_c`, positions `x_{c,i}` and marks `m_{c,i}` — and the law is in
the missing JSON, not in the vendored source.  So supplier 2 ("redo the interval
arithmetic") is blocked for the same reason as supplier 1: the artifact holds the
*input*, and only the outputs were published.  What this script establishes is
how small the missing thing is, and therefore how small a request to the authors
would have to be.

Exit: 0 the table has the shape described · 1 it does not · 5 harness failure.

Run:  python3 forensics/lawN256_shape.py
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
SRC = os.path.join(ROOT, "vendor", "zeta23", "Zeta23", "PairCeiling", "LawN256.lean")


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the table.  Exit 5.")
    sys.exit(5)


def main():
    try:
        with open(SRC, encoding="utf-8") as fh:
            src = fh.read()
    except OSError as exc:
        die_harness(f"cannot read LawN256.lean: {exc}")

    mk = re.search(r"K := (\d+)", src)
    me = re.search(r"encl := \[(.*?)\]\s*\n", src, re.S)
    if not mk or not me:
        die_harness("LawN256.lean has no `K :=` or no `encl := [...]`")

    K = int(mk.group(1))
    pairs = [(int(a), int(b))
             for a, b in re.findall(r"\((\d+),\s*(\d+)\)", me.group(1))]

    print("=== vendored LawN256 enclosure table ===")
    bad = 0

    if K != 2 ** 140:
        print(f"  [FAIL] scale      K = {K}, expected 2^140")
        bad += 1
    else:
        print("  [ok ] scale      K = 2^140")

    if len(pairs) != 256:
        print(f"  [FAIL] count      {len(pairs)} enclosures, expected 256")
        return 1
    print(f"  [ok ] count      {len(pairs)} enclosures")

    widths = {hi - lo for lo, hi in pairs}
    if widths != {1}:
        print(f"  [FAIL] width      widths present: {sorted(widths)}, expected {{1}}")
        bad += 1
    else:
        print("  [ok ] width      every interval is exactly 1 ulp wide")

    base = 2 ** 132
    off = []
    for j, (lo, hi) in enumerate(pairs[:255], start=1):
        if not (abs(lo - j * base) <= 1 and abs(hi - j * base) <= 1):
            off.append(j)
    if off:
        print(f"  [FAIL] closed form {len(off)} of j=1..255 not at j·2^132 ± 1: {off[:8]}")
        bad += 1
    else:
        print("  [ok ] closed form j = 1..255 all sit at j·2^132 ± 1  (S(j) = j/256)")

    lo, hi = pairs[255]
    if abs(lo - 256 * base) <= 1:
        print("  [FAIL] j = 256     follows the linear pattern; the table would then")
        print("         carry nothing the row certificate does not, and this")
        print("         script's whole reading of the ruling is wrong")
        bad += 1
    else:
        print(f"  [ok ] j = 256     off-pattern, S(256) ≈ {lo / K:.12f} — the entry")
        print("                    that depends on the law rather than on the row")

    print()
    if bad:
        print("The table is not the shape `266` recorded.  Re-read it before citing")
        print("`PRICES.md`'s rung-0 entry, which rests on this shape.")
        return 1
    print("255 of 256 entries are implied by RowCert's |256·S(j) − j| ≤ 3/10^40.")
    print("The missing JSON holds the law — the input — not these outputs.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
