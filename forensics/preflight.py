#!/usr/bin/env python3
"""Before proving it, ask whether we already have it.

**Why this exists.**  Four rediscoveries in this arc, every one caught by a
guard *after* the proof was written:

* `412` rewrote `098`'s `Riemann.starBound_of_mult_le` — `forensics/board.py`'s
  parser was hiding it from the enumeration `412` consulted.
* `416` rewrote `Blindness.add_ordinates`, twenty lines below the definition it
  is about.
* `425` **deferred a theorem** for want of `Blindness.Nsc_eq_sum_mass_one_nat`,
  which was on disk; `429` wrote the conversion inline; `430` wrote the lemma
  again.

`forensics/duplication_floor.py` matches conclusions **exactly** and so catches
only the last of those, and only after the fact.  This one is asked *first*, and
matches loosely on purpose.

**How it matches.**  Two scores, both on the statement column of
`forensics/statement_index.tsv`:

* **shape** — the conclusion with names, numerals and whitespace stripped, so
  `A ≤ B + C` collides with `X ≤ Y + Z`.  Cheap and blunt.
* **tokens** — identifier overlap, the metric `410` found catches the invention
  shape that edit distance misses (`configAt_offAt` against
  `offAt_configAt_self`).

**Prospective only, and `432` measured why.**  Run backwards over the tree as a
redundancy detector, the same two scores flag `62` pairs at similarity `1.0` —
and the ones checked by hand are legitimately distinct: `two_le_card_of_two_mem`
against `three_le_card_of_three_mem`, `certified_offline` against
`offline_via_derivative_family`.  The token score strips numerals, and this
project deliberately states families at several constants, so *same shape, same
identifiers* is its normal condition rather than a defect.  Ask this tool about a
statement you are **about to write**; do not ask it which of two existing
declarations is redundant.

**Calibrated on the three rediscoveries above**, which run on every invocation:
if the original does not surface for each, the tool has no discriminating power
and says so rather than printing a ranking nobody should trust.

Exit: 0 report printed · 5 harness failure (calibration lost).

Run:  python3 forensics/preflight.py 'D.Nsc = ∑ γ ∈ D.ordinates.toFinset, …'
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INDEX = os.path.join(ROOT, "forensics", "statement_index.tsv")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the tree.  Exit 5.")
    sys.exit(5)


def rows():
    try:
        out = []
        for line in open(INDEX, encoding="utf-8").read().split("\n")[1:]:
            if not line:
                continue
            r = line.split("\t")
            if len(r) >= 5 and r[0] == "ours":
                out.append((r[3], r[1], r[4]))
        return out
    except OSError as exc:
        die_harness(f"cannot read the statement index: {exc}")


def conclusion(stmt):
    """Everything after the first top-level `:` — `412`'s depth-counted split."""
    depth = 0
    for i, ch in enumerate(stmt):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and stmt[i:i + 2] != ":=":
            return stmt[i + 1:]
    return stmt


def shape(s):
    return re.sub(r"[\s]", "", TOKEN.sub("_", re.sub(r"\d+", "0", s)))


def pieces(s):
    out = set()
    for t in TOKEN.findall(s):
        for part in re.split(r"[_.]", t):
            for w in re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z0-9]+", part):
                out.add(w.lower())
    return out


def search(candidate, n=5):
    cand_c = conclusion(candidate)
    cs, cp = shape(cand_c), pieces(cand_c)
    scored = []
    for name, mod, stmt in rows():
        c = conclusion(stmt)
        s = shape(c)
        same_shape = 1.0 if s == cs else 0.0
        p = pieces(c)
        jac = len(cp & p) / len(cp | p) if (cp | p) else 0.0
        scored.append((same_shape + jac, same_shape, round(jac, 2), name, mod))
    scored.sort(reverse=True)
    return scored[:n]


CALIBRATION = [
    ("starBound_of_mult_le",
     "{F : Family} {M : ℕ} (hM1 : 1 ≤ M) {κ : ℝ} : "
     "F.toCounts.StarBound ((M : ℝ) - ((M : ℝ) - 1) * κ)",
     "`412` rewrote this"),
    ("add_ordinates",
     "(D D' : ZeroData) : (superpose D D').ordinates = D.ordinates + D'.ordinates",
     "`416` rewrote this"),
    ("Nsc_eq_sum_mass_one_nat",
     "(D : ZeroData) : D.Nsc = ∑ γ ∈ D.ordinates.toFinset, (if D.H γ = 1 then 1 else 0)",
     "`425` deferred a theorem for it, `430` rewrote it"),
]


def main():
    ok = 0
    for want, stmt, why in CALIBRATION:
        hits = [h[3] for h in search(stmt)]
        good = want in hits
        ok += good
        print(f"  [{'ok ' if good else 'FAIL'}] {want:34s} "
              f"{'found' if good else 'MISSED'} — {why}")
    if ok != len(CALIBRATION):
        die_harness("a known rediscovery no longer surfaces; the ranking is "
                    "not to be trusted")
    print(f"  calibration {ok}/{len(CALIBRATION)} as designed.")
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not argv:
        print()
        print("  Give a candidate statement to search for, quoted.")
        return 0
    print()
    print("=== closest declarations on disk ===")
    for score, sh, jac, name, mod in search(argv[0], n=8):
        tag = "  SAME SHAPE" if sh else ""
        print(f"  {jac:>4} {mod}.{name}{tag}")
    print()
    print("  A high score is a prompt to read, not a verdict.  `430`: the lemma "
          "that cost three cycles was an exact match nobody looked for.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
