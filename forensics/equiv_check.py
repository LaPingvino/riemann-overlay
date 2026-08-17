#!/usr/bin/env python3
"""Which of our `ZeroData` inequalities are the same inequality.

**Why this exists.**  `316` found by hand that `315`'s `mass_charges_every_class`
is `two_mul_atomCount_add_oddAtoms_le` after substituting `314`'s partitions —
different variables, different arity, one fact.  `duplication_floor` cannot see
that: it matches **conclusions**, and these two conclusions share no term.

**What it does.**  Collects the hypothesis-free `ℕ`-linear facts about a single
`ZeroData` from `statement_index.tsv`, then asks `omega`, for each ordered pair,
whether `A` plus the four ordinate partitions proves `B`.  Mutual implication is
equivalence modulo the partitions.

**The trap this file exists to avoid, and it cost `317` most of a cycle.**  The
first run put all `272` pairs in one `.lean`.  Lean **stopped reporting errors**
partway — `1908` source lines, last reported error at line `864` — so every pair
below that point read as a success and the tool reported one giant equivalence
class of twelve.  It was caught only because one member (`3·haunted ≤ N` implying
`2·offLineOnly ≤ N_off`, which share no variable) was implausible enough to check
by hand.  `S49`'s family: a check that scanned less than its output implied.

So this file **chunks**, and appends to each chunk a sentinel that cannot be
proved.  If the sentinel's error is missing, Lean stopped reporting and the chunk
is a harness failure rather than a result.  A line-count heuristic was tried
first and gave a false alarm, because a chunk may legitimately end in successes.

**What it is not.**  Not a guard: it shells out to `lake env lean` and takes
minutes.  Run it when the inventory of inequalities changes.

Exit: 0 report printed · 5 harness failure (including truncation).

Run:  python3 forensics/equiv_check.py
"""

import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
INDEX = os.path.join(HERE, "statement_index.tsv")

PARTITIONS = [
    "NscStd_eq_Nsc_add_haunted",
    "oddAtoms_eq_NscStd_add_oddAbove",
    "onLineOrdinates_eq_oddAtoms_add_evenOnAt",
    "onLineOrdinates_add_offLineOnly",
]

# Facts that are not ℕ-linear in the ordinate counts, or that name objects the
# substitution cannot see through.
EXCLUDE = ("ℝ", "ℤ", "∀", "∃", "↔", "∧", "Even", "filter", "Multiset", "Finset",
           "distinctZeros", "NscAny", "Nstar", "profile", "factMoment",
           "hauntedSet", "refl", "simpleOffLine")

CHUNK = 30

# A positive control appended to every generated file: unprovable, so its error
# must appear.  `317`: without it a truncated run reads as a page of successes,
# and a line-count heuristic gives false alarms because a chunk may legitimately
# end in successes.
SENTINEL = ("-- SENTINEL\n"
            "example (D : Riemann.ZeroData) : D.N + 1 ≤ D.N := by\n  omega\n")
DECL = re.compile(r"^\(D : ZeroData\) : (.+)$")


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the inequalities.  Exit 5.")
    sys.exit(5)


def facts():
    try:
        rows = [l.split("\t") for l in open(INDEX, encoding="utf-8").read()
                .split("\n")[1:] if l]
    except OSError as exc:
        die_harness(f"cannot read the statement index: {exc}")
    seen, out = set(), []
    for r in rows:
        if len(r) < 5 or r[0] != "ours":
            continue
        m = DECL.match(r[4].strip())
        if not m:
            continue
        s = m.group(1)
        if "≤" not in s or any(b in s for b in EXCLUDE):
            continue
        if s in seen:            # identical conclusions: `duplication_floor`'s job
            continue
        seen.add(s)
        out.append((r[3], s))
    return out


def run(src, tag):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     dir=os.environ.get("TMPDIR", "/tmp"),
                                     encoding="utf-8") as fh:
        fh.write(src)
        path = fh.name
    try:
        p = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True, timeout=1800)
    except OSError as exc:
        die_harness(f"cannot run `lake env lean` ({exc}); is lake on PATH?")
    except subprocess.TimeoutExpired:
        die_harness(f"chunk {tag} timed out")
    base = os.path.basename(path)
    errs = {int(m.group(1)) for m in
            re.finditer(re.escape(base) + r":(\d+):\d+: error", p.stdout)}
    lines = src.split("\n")
    sentinel = max(i for i, l in enumerate(lines, 1) if l.startswith("-- SENTINEL"))
    if (sentinel + 2) not in errs:
        die_harness(f"chunk {tag}: the sentinel at line {sentinel + 2} did not "
                    f"report, so Lean stopped emitting errors and the successes "
                    f"in this chunk are not results (`317`)")
    return errs, src.split("\n")


def block(a, b, sa, sb):
    return (f"-- P {a} {b}\n"
            f"example (D : Riemann.ZeroData) (hA : {sa}) : {sb} := by\n"
            + "".join(f"  have p{i} := {n} D\n"
                      for i, n in enumerate(PARTITIONS))
            + "  omega\n")


def main():
    F = facts()
    n = len(F)
    print(f"=== {n} hypothesis-free ℕ-linear `ZeroData` inequalities ===")

    # 1. which are consequences of the partitions alone?
    src = "import Riemann\nopen Riemann.Blindness\n"
    for i, (nm, s) in enumerate(F):
        src += (f"-- F {i}\nexample (D : Riemann.ZeroData) : {s} := by\n"
                + "".join(f"  have p{k} := {p} D\n"
                          for k, p in enumerate(PARTITIONS)) + "  omega\n")
    src += SENTINEL
    errs, lines = run(src, "free")
    free = set()
    for ln, l in enumerate(lines, 1):
        if l.startswith("-- F "):
            i = int(l.split()[2])
            if (ln + 6) not in errs:
                free.add(i)
    print(f"\n  {len(free)} follow from the four partitions alone:")
    for i in sorted(free):
        print(f"    {F[i][0]}")

    G = [i for i in range(n) if i not in free]
    pairs = [(a, b) for a in G for b in G if a != b]
    res = {}
    print(f"\n  {len(pairs)} ordered pairs among the {len(G)} that carry content")
    for c in range(0, len(pairs), CHUNK):
        src = "import Riemann\nopen Riemann.Blindness\n"
        for a, b in pairs[c:c + CHUNK]:
            src += block(a, b, F[a][1], F[b][1])
        src += SENTINEL
        errs, lines = run(src, c // CHUNK)
        for ln, l in enumerate(lines, 1):
            if l.startswith("-- P "):
                _, _, a, b = l.split()
                res[(int(a), int(b))] = (ln + 6) not in errs

    parent = {i: i for i in G}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a in G:
        for b in G:
            if a < b and res[(a, b)] and res[(b, a)]:
                parent[find(a)] = find(b)
    cls = {}
    for i in G:
        cls.setdefault(find(i), []).append(i)
    big = [v for v in cls.values() if len(v) > 1]
    print(f"\n  {len(cls)} classes; {len(big)} with more than one member:")
    for v in big:
        print("    — one inequality under several names:")
        for i in v:
            print(f"        {F[i][0]}")
    print("\n  A class with more than one member is `256`'s grading question")
    print("  asked in the partitions' coordinates rather than syntactically.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
