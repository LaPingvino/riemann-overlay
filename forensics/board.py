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

# SESSION 166: the same guard, extended to the rest of the transfer layer.
# `162` recorded "every `OffLineImport` carries β = 1 − κ" as a table in
# `PRICES.md`, hand-assembled from a grep — the identical construction that
# `163`–`165` showed loses rows silently.  A producer added later would make that
# claim stale with nothing to notice.  These sets are the enumerations the
# registers rely on; the point is not their content but that they are checked.
TRANSFER = {
    "OffLineImport": {
        "offLineImport_of_proportionStd", "offLineImport_of_derivative",
        "certified_offline", "offline_via_xiPrime",
    },
    # SESSION 171: `170` claimed the StarBound channel is unwalled because its
    # producers do not consume a proportion.  Classifying by input confirmed it —
    # four of eight take no proportion — so the enumeration is guarded here too.
    "StarBound": {
        "starBound_of_multiplicity_le", "starBound_of_multiplicity_and_proportion",
        "starBound_of_mult_le_two", "routeIII_with_narrowBox", "routeIII_via_A''",
        "starBound_of_multiplicity_two", "starBound_of_mult_le_two_zeta",
        "starBound_of_mult_le_three",
    },
    "HauntedDensity": {
        "hauntedDensity_of_offLineImport", "hauntedDensity_of_starBound",
        "hauntedDensity_of_distinctZeros", "certified_haunted",
        "certified_haunted_via_distinctZeros",
    },
}

DECL = re.compile(r"^(?:theorem|lemma|axiom)\s+(\S+)((?:.|\n)*?):=", re.M)


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


def extract_concluding(pred):
    """Declarations whose stated conclusion mentions `pred` (and not a longer
    predicate containing it)."""
    out = set()
    for fn in sorted(os.listdir(SRC)):
        if not fn.endswith(".lean"):
            continue
        src = open(os.path.join(SRC, fn), encoding="utf-8").read()
        for m in DECL.finditer(src):
            head = m.group(0).split(":=")[0]
            concl = " ".join(head.rsplit(":", 1)[-1].split())
            if re.search(r"\b" + pred + r"\b", concl):
                out.add(m.group(1))
    return out


def check_transfer():
    """The enumerations `162` recorded by hand, re-derived."""
    bad = 0
    for pred, expected in TRANSFER.items():
        got = extract_concluding(pred)
        new, gone = sorted(got - expected), sorted(expected - got)
        status = "unchanged" if not (new or gone) else "CHANGED"
        print(f"\n  {pred}: {len(got)} declarations — {status}")
        for n in sorted(got):
            print(f"      {'ok ' if n in expected else 'NEW'} {n}")
        for n in gone:
            print(f"      GONE {n}")
        bad += bool(new or gone)
    return bad


# SESSION 172.  `S77`: `166` classified producers by the hypotheses in their
# *statements*, and `171` found that unsound — `starBound_of_multiplicity_two`
# takes no proportion in its statement and passes `certified_nsc_unconditional`
# inside its proof.  The cone is the measure.
#
# `165` deliberately kept this file build-free ("a linter that needs a build
# stops being run"), so cone-checking is **opt-in**: `--cones` emits a Lean file
# of `#print axioms`, runs it, and compares against `CONE_EXPECTED`.  The default
# run stays cheap and the expensive check stays reproducible.
CONE_EXPECTED = {
    # axiom-free — genuinely independent of the ledger's rows
    "Blindness.offLine_bound_attained": set(),
    "Blindness.offLine_count_not_bounded_by_proximity": set(),
    "Blindness.Nstar_bound_attained": set(),
    "Blindness.atomCount_le_distinctZeros": set(),
    "Blindness.distinctZeros_le_atomCount_add_Noff": set(),
    "starBound_of_multiplicity_le": set(),
    "routeIII_with_narrowBox": set(),
    "offline_roundtrip_loses": set(),
    "NoSmallHaunted.mono": set(),
    "noHaunted_iff_forall_noSmallHaunted": set(),
    "noSmallHaunted_strict": set(),
    # one axiom
    "conjectural_routeIII": {"zetaNonempty"},
    "conjectural_routeI": {"zetaNonempty"},
    "conjectural_full": {"zetaNonempty"},
    # two — the certified tier
    "certified_nsc_unconditional": {"baseline_zeta23", "zetaNonempty"},
    "certified_nsc_via_noSmallHaunted": {"baseline_zeta23", "zetaNonempty"},
    "certified_nsc_via_noSmallHaunted_seven": {"baseline_zeta23", "zetaNonempty"},
    "starBound_of_multiplicity_two": {"baseline_zeta23", "zetaNonempty"},
    "starBound_of_mult_le_two_zeta": {"baseline_zeta23", "zetaNonempty"},
    # four — Route II
    "certified_nsc_via_xiPrime": {"baseline_zeta23", "xiPrimeFamily",
                                  "zeta23_xiPrime", "zetaNonempty"},
    "offline_via_xiPrime": {"xiPrimeFamily", "zeta23_xiPrime", "zetaNonempty"},
}

LEAN_AX = re.compile(r"'Riemann\.([^']+)' depends on axioms: \[([^\]]*)\]", re.S)


def check_cones():
    """Opt-in: ask the kernel what each producer actually consumes."""
    import subprocess
    import tempfile
    names = sorted(CONE_EXPECTED)
    src = "import Riemann\n" + "".join(
        f"#print axioms Riemann.{n}\n" for n in names)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
        fh.write(src)
        path = fh.name
    # SESSION 172: `subprocess.run` RAISES when the executable is missing rather
    # than returning nonzero, so the graceful branch below never fired and a
    # traceback exited 1 — indistinguishable from a cone mismatch.  That is `S40`
    # exactly (`proportion.go` reporting a verdict for a check it could not run),
    # committed in the same cycle that cites it.  Exit 5 for harness failure,
    # matching `proportion.go`'s convention.
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True)
    except OSError as e:
        print(f"  ⚠️ could not RUN `lake env lean` ({e}) — cone check NOT "
              "performed. This is a harness failure, NOT a verdict on any "
              "cone (S40). Is `lake` on PATH?")
        raise SystemExit(5)
    if r.returncode != 0:
        print("  ⚠️ `lake env lean` exited nonzero — cone check NOT performed.")
        print(r.stderr[:400])
        raise SystemExit(5)
    got = {}
    for m in LEAN_AX.finditer(r.stdout):
        ax = {a.strip().replace("Riemann.", "")
              for a in m.group(2).split(",")}
        got[m.group(1)] = {a for a in ax
                           if a not in {"propext", "Classical.choice",
                                        "Quot.sound"}}
    bad = 0
    print("\n=== cone check (the kernel, not the regex) ===")
    for n in names:
        if n not in got:
            print(f"  [MISS] {n:46} not reported")
            bad += 1
            continue
        ok = got[n] == CONE_EXPECTED[n]
        bad += not ok
        print(f"  [{'ok ' if ok else 'WRONG'}] {n:46} "
              f"{sorted(got[n]) if got[n] else 'axiom-free'}")
        if not ok:
            print(f"          recorded: {sorted(CONE_EXPECTED[n]) or 'axiom-free'}")
    print(f"  {len(names) - bad}/{len(names)} cones as recorded.")
    return bad


def main():
    if "--cones" in sys.argv:
        raise SystemExit(1 if check_cones() else 0)
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
    print("\n=== transfer-layer enumerations (the tables `162` recorded) ===")
    bad = check_transfer()
    if bad:
        print("\n  ⚠️ a transfer enumeration changed.  `PRICES.md`'s claim that "
              "every `OffLineImport` carries `β = 1 − κ` is only as good as this "
              "list.")
        return 1
    print("\n  transfer enumerations unchanged.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
