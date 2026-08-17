#!/usr/bin/env python3
"""Numbers that live in Lean docstrings and nowhere in Lean code.

**Why this exists.**  `299` found `certified_nsc_via_noSmallHaunted_seven`'s
docstring recording the `m = 7` rung's shortfall as `1/1500000` when the kernel
says `1/15000000` — ten times too large, wrong since `153`, and load-bearing
prose in the file that carries the board's best conditional row.

That cycle's closing sentence was a hypothesis: *a number that appears once and
is not needed twice is where this project's prose goes wrong, because everything
cited more than once gets a theorem behind it sooner or later.*  This is the
instrument that makes the hypothesis testable instead of quotable.

**What it does.**  Splits every `Riemann/*.lean` into docstring spans and code
spans, extracts numerals from each, and lists the ones that appear in a
docstring and in no code anywhere in the tree.  A numeral that also appears in
code has a theorem, a `norm_num`, or a definition standing behind it; one that
does not is asserted by a human and checked by nobody.

**What it is not.**  Not a guard.  It exits `0` always, like
`dependency_profile.py`, because most of its output is legitimate: session
numbers, line counts, citation years.  `S50` is the reason that matters — a
script that cannot return a failing exit code should not pretend to be in the
roster, and one that could return a failing code on this corpus would be red
forever.

**Its false-positive shapes, measured on the first run (`300`).**  Of `189`
numerals absent from code, `121` are bare integers in the session-number range
and `6` are large integers (line counts, `44,441` and friends).  The
discriminating set is the `62` decimals and rationals.  Even there the screen
misreads: `Fujii 1974/81` is a citation, not a rational, and `1974/1981` on the
next line is the same artefact.  So the output is a **reading list**, and the
triage is the work.

**The first triage, for calibration (`300`).**  Fourteen of the `62` were read
against their contexts and checked: the `1000 : 321` witness accounting in
`Fiber.lean:4617` (`642 + 1321 = 1963`, `2·321 + 1321 = 1963`,
`642/1963 ≈ 0.32705` with `0.00045` to spare under `0.3275`), the ladder's
`δ = (1 − κ)/(m − 1)` readings in `Gaps.lean:1165` (`0.3275/2 = 0.16375`,
`0.3275/4 = 0.081875`, `0.6725 − 0.081875 = 0.590625`), and the exchange
crossover at `Gaps.lean:814` (`0.607 + (1.393 − 4/3)/6 ≈ 0.61694`).  All sound.
`299`'s slip was not representative of the corpus, and saying so is the point of
running this rather than repeating the sentence.

Run:  python3 forensics/prose_numerals.py
      python3 forensics/prose_numerals.py --all   (include the integers)
"""

import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
SRC = os.path.join(ROOT, "Riemann")

DOC = re.compile(r"/--(.*?)-/", re.S)
NUM = re.compile(r"(?<![\w.])(\d+(?:\.\d+)?(?:/\d+)?)(?![\w])")

# This project's session numbers run in the low hundreds, so a bare integer in
# this range is far more likely a citation than a quantity.  Deliberately not
# tightened: `S39` warns against fitting a filter to the measurement that
# informs it, and the triage above is that measurement.
SESSION_MAX = 320


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the prose.  Exit 5.")
    sys.exit(5)


def kind(n):
    if re.fullmatch(r"\d+", n):
        return "session-or-small-int" if int(n) <= SESSION_MAX else "large-int"
    return "decimal-or-rational"


def scan():
    doc_nums = collections.Counter()
    code_nums = collections.Counter()
    where = collections.defaultdict(list)
    if not os.path.isdir(SRC):
        die_harness(f"missing tree: {SRC}")
    for d, dirs, fs in os.walk(SRC):
        dirs[:] = [x for x in dirs if not x.startswith(".")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(d, f)
            try:
                with open(p, encoding="utf-8") as fh:
                    s = fh.read()
            except OSError as exc:
                die_harness(f"cannot read {p}: {exc}")
            rel = os.path.relpath(p, ROOT)
            for m in DOC.finditer(s):
                line = s[:m.start()].count("\n") + 1
                for n in NUM.findall(m.group(1)):
                    doc_nums[n] += 1
                    where[n].append(f"{rel}:{line}")
            for n in NUM.findall(DOC.sub(" ", s)):
                code_nums[n] += 1
    return doc_nums, code_nums, where


def main():
    show_all = "--all" in sys.argv
    doc_nums, code_nums, where = scan()
    only = {n: c for n, c in doc_nums.items() if n not in code_nums}
    by = collections.Counter(kind(n) for n in only)

    print("=== numerals in docstrings, absent from all Lean code ===")
    print(f"  distinct in docstrings : {len(doc_nums)}")
    print(f"  absent from code       : {len(only)}")
    for k in ("decimal-or-rational", "session-or-small-int", "large-int"):
        print(f"    {k:22s} {by.get(k, 0)}")
    print()
    print("  The decimals and rationals are the reading list; the integers are")
    print("  mostly session references.  Nothing here is a defect until it is")
    print("  read against its context (R17).")
    print()

    rows = [(n, c) for n, c in only.items()
            if show_all or kind(n) == "decimal-or-rational"]
    for n, c in sorted(rows, key=lambda x: (-x[1], x[0])):
        print(f"  {n:22s} x{c}   {where[n][0]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
