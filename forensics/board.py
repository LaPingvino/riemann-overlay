#!/usr/bin/env python3
"""The board — every ζ-level `Proportion` result, extracted rather than recalled.

**Why this exists, and it was bought twice.**  `S67` (`163`): I built a menu of
conditional routes over six cycles and it was missing its cheapest row, which had
been in `Proportion.lean` the whole time.  `S69` (`164`): the sweep that found it
listed 28 declarations, I read the one that surprised me and stopped, and *two
more* rows were missing — including `conjectural_full`, which is the
`conjectural: 100.00% (OPEN D)` field printed on every line of `PROPORTION.log`.

Both failures are the same shape: **a board assembled by hand loses rows
silently.**  So the board is assembled here instead, and this file fails if the
extracted set stops matching the recorded one.

What it does NOT do: judge, price, or rank.  It reports which declarations
conclude in a `zetaFamily` proportion and what constant each carries.  Axiom
cones are quoted from `EXPECTED` and re-checked by `audit/Declarations.lean` and
`tools/proportion.go`, not recomputed here — running `lake` from a linter would
make the cheap check expensive and it would stop being run.

Run:  python3 forensics/board.py
Exit 1 if the extracted board differs from `EXPECTED`.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, os.pardir)
SRC = os.path.join(ROOT, "Riemann")

# Declarations concluding in a `zetaFamily` proportion, with the constant as
# written.  `None` marks a bound stated existentially rather than as a numeral.
EXPECTED = {
    "certified_nsc":                        "0",
    "certified_nsc_unconditional":          "0.50875",
    "certified_nsc_via_offline":            "0.50875",
    "certified_nsc_via_haunted":            "0.50875",
    "certified_nsc_via_noSmallHaunted":     "0.590625",
    "certified_nsc_via_xiPrime":            "0.60169",
    "certified_nsc_via_noSmallHaunted_seven": "0.6179166",
    "proportion_of_mult_le_two":            "0.6725",
    "proportion_of_noHaunted_zeta":         "0.6725",
    "conjectural_routeIII":                 "2/3 - ε",
    "conjectural_routeI":                   "∃ κ, 0.6725 < κ",
    "conjectural_full":                     "1 - ε",
    "routeI_closePairs_zeta":               "∃ κ > 0",
}

# NOT on the board, and the first run of this file is why the distinction is
# written down: `nsc_row_opens` states its conclusion as the *unfolded*
# inequality `(κ − ε)·Nz ≤ Nsc` rather than as `Proportion`, so it does not
# appear here.  I had put it in `EXPECTED` by hand from a half-remembered grep,
# and the extractor removed it on its first run — which is the direction of
# correction this file was built for.

DECL = re.compile(r"^(?:theorem|lemma)\s+(\S+)((?:.|\n)*?):=", re.M)


def extract():
    out = {}
    for fn in sorted(os.listdir(SRC)):
        if not fn.endswith(".lean"):
            continue
        src = open(os.path.join(SRC, fn), encoding="utf-8").read()
        for m in DECL.finditer(src):
            head = m.group(0).split(":=")[0]
            concl = " ".join(head.rsplit(":", 1)[-1].split())
            if "zetaFamily" in concl and "Proportion" in concl \
                    and "ProportionStd" not in concl:
                out[m.group(1)] = concl
    return out


def main():
    got = extract()
    print("=== the board: ζ-level `Proportion` declarations, extracted ===")
    for name in sorted(got):
        mark = "ok " if name in EXPECTED else "NEW"
        print(f"  [{mark}] {name:42} {got[name][:58]}")
    missing = sorted(set(EXPECTED) - set(got))
    new = sorted(set(got) - set(EXPECTED))
    for n in missing:
        print(f"  [GONE] {n:42} (in EXPECTED, not found in sources)")
    print(f"\n  extracted {len(got)}, expected {len(EXPECTED)}, "
          f"new {len(new)}, gone {len(missing)}")
    if new or missing:
        print("\n  ⚠️ the board has changed.  Re-price it in `PRICES.md` and "
              "update EXPECTED — a row appearing or vanishing unnoticed is the "
              "defect this file exists for (S67, S69).")
        return 1
    print("  board unchanged.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
