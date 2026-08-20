#!/usr/bin/env python3
"""Is this inequality a consequence of the ones we already have?

**Why this exists.**  `423` filed it: the three-term sweep's residue reduces to
about thirty primitives, and *every one of them* looked like a non-negative
combination of `Blindness.mass_charges_every_class` and positivity.  Looked
like.  Deciding it is a small linear program per candidate, and `423`'s kill
condition said not to fake that with another heuristic.

**The question, exactly.**  Write each fact `0 ≤ f` as a vector in the partition
basis `N, N_off, N⊛, Nsc, hauntedCount, oddAbove, evenOnAt, offLineOnly`.  A
candidate `0 ≤ d` follows from the facts together with positivity of the basis
**iff** `d` lies in the cone they generate — iff `A x = d` has a solution
`x ≥ 0`, where `A`'s columns are the facts and the eight unit vectors.

**Exact, not floating point.**  Phase-I simplex over `Fraction`, with Bland's
rule so it cannot cycle.  A floating-point LP would answer a question about
rounding rather than about the cone; `S49`'s family.

**Calibrated.**  Three cases whose answers are known by hand run on every
invocation, and a disagreement is a harness failure, not a result.

Exit: 0 report printed · 5 harness failure.

Run:  python3 forensics/farkas.py
"""

import os
import re
import sys
from fractions import Fraction as F


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the inequalities.  Exit 5.")
    sys.exit(5)


def in_cone(cols, d):
    """Solve `A x = d, x ≥ 0` exactly.  Phase-I simplex, Bland's rule."""
    m = len(d)
    n = len(cols)
    # make the right-hand side non-negative
    rows = [[F(c[i]) for c in cols] for i in range(m)]
    rhs = [F(v) for v in d]
    for i in range(m):
        if rhs[i] < 0:
            rows[i] = [-v for v in rows[i]]
            rhs[i] = -rhs[i]
    # tableau with artificial variables
    T = [rows[i] + [F(1) if j == i else F(0) for j in range(m)] + [rhs[i]]
         for i in range(m)]
    basis = [n + i for i in range(m)]
    width = n + m
    # objective: minimise the sum of artificials
    # Objective row for minimising the artificials, expressed over the
    # structural columns only: the artificial columns are basic, so their
    # reduced cost is `0` by construction.  Subtracting over *all* columns was
    # the first version's bug, and the calibration caught it.
    cost = [F(0)] * (width + 1)
    for i in range(m):
        for j in list(range(n)) + [width]:
            cost[j] -= T[i][j]
    for it in range(20000):
        piv = -1
        for j in range(width):          # Bland: first improving column
            if cost[j] < 0:
                piv = j
                break
        if piv < 0:
            break
        best, brow = None, -1
        for i in range(m):
            if T[i][piv] > 0:
                r = T[i][width] / T[i][piv]
                if best is None or r < best or (r == best and basis[i] < basis[brow]):
                    best, brow = r, i
        if brow < 0:
            die_harness("unbounded phase-I; the tableau is malformed")
        p = T[brow][piv]
        T[brow] = [v / p for v in T[brow]]
        for i in range(m):
            if i != brow and T[i][piv] != 0:
                f = T[i][piv]
                T[i] = [a - f * b for a, b in zip(T[i], T[brow])]
        if cost[piv] != 0:
            f = cost[piv]
            cost = [a - f * b for a, b in zip(cost, T[brow])]
        basis[brow] = piv
    else:
        die_harness("phase-I did not terminate in 20000 pivots")
    return -cost[width] == 0


BASIS = ["N", "Noff", "Nstar", "thirdMoment", "fourthMoment", "Nsc",
         "hauntedCount", "oddAbove", "evenOnAt", "offLineOnly"]


def unit_cols():
    return [[1 if k == i else 0 for k in range(len(BASIS))]
            for i in range(len(BASIS))]


def derived(v):
    """A full count-dictionary from a basis vector, using the four partitions —
    the same substitution `423` used, so a fact's vector is well defined."""
    d = dict(zip(BASIS, v))
    d["NscStd"] = d["Nsc"] + d["hauntedCount"]
    d["oddAtoms"] = d["NscStd"] + d["oddAbove"]
    d["onLineOrdinates"] = d["oddAtoms"] + d["evenOnAt"]
    d["onLinePoints"] = d["onLineOrdinates"]
    d["atomCount"] = d["onLineOrdinates"] + d["offLineOnly"]
    # `427`: the moment aliases, so an instantiated `momentK D j` resolves.
    d["momentK_1"] = d["N"]
    d["momentK_2"] = d["Nstar"]
    d["momentK_3"] = d["thirdMoment"]
    d["momentK_4"] = d["fourthMoment"]
    return d


QUANT = re.compile(
    r"^\(D : (?:Riemann\.)?ZeroData\) \{k : ℕ\} \(hk : (\d) ≤ k\) : (.+)$")
# `429`: and the same statement with the order **explicit and unconstrained** —
# `(D : ZeroData) (k : ℕ) : …`.  Missing this shape cost `429` its own find, the
# third cycle running that the reader could not read the newest theorem.
QUANT_FREE = re.compile(
    r"^\(D : (?:Riemann\.)?ZeroData\) \(k : ℕ\) : (.+)$")
ORDERS = (1, 2, 3, 4)

# `429`: the guard `428`'s might-mean asked for.  Each entry is a declaration a
# recent cycle proved and that this reader must be able to instantiate.  A cycle
# that proves a parameterised theorem adds its name here; if the reader stops
# seeing it, the run fails instead of quietly shrinking the cone.
READS = (
    "momentK_add_Noff_le_momentK_succ",            # 426
    "momentK_add_pow_mul_Noff_le_momentK_succ",    # 428
    "momentK_add_pow_mul_atomCount_le",            # 429
)


def quantified():
    """Theorems quantified over the moment order, instantiated at small `k`.

    `426` filed this: `equiv_check.facts()` matches `(D : ZeroData) : …`, so
    every theorem with a numeric parameter was invisible to the whole
    apparatus — including `426`'s own find.  Each instantiation is **verified on
    the box** before it is used; a false one is a harness failure, which is what
    makes the textual substitution safe.
    """
    import re as _re
    rows = [l.split("\t") for l in open(
        os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                     "forensics", "statement_index.tsv"),
        encoding="utf-8").read().split("\n")[1:] if l]
    out = []
    for r in rows:
        if len(r) < 5 or r[0] != "ours":
            continue
        m = QUANT.match(r[4].strip())
        mf = None if m else QUANT_FREE.match(r[4].strip())
        if not m and not mf:
            continue
        lo, body = (int(m.group(1)), m.group(2)) if m else (0, mf.group(1))
        if "≤" not in body:
            continue
        for k in ORDERS:
            if k < lo:
                continue
            if k + 1 > max(ORDERS):
                s0 = body
            else:
                s0 = body.replace("momentK D (k + 1)", f"momentK_{k + 1}")
            s = s0.replace("momentK D k", f"momentK_{k}")
            s = _re.sub(r"\bk\b", str(k), s)
            # constant-fold `a ^ b` so the evaluator never meets `^`
            # `428`: fold `A ^ (a - b)` as well as `A ^ a` — the sharpened
            # ladder's coefficient is `2 ^ (k - 1)`, and folding only the bare
            # form left it carrying a `^` and therefore skipped.
            s = _re.sub(r"(\d+) \^ \((\d+) - (\d+)\)",
                        lambda mm: str(int(mm.group(1)) ** (int(mm.group(2)) - int(mm.group(3)))), s)
            s = _re.sub(r"(\d+) \^ (\d+)", lambda mm: str(int(mm.group(1)) ** int(mm.group(2))), s)
            # `427`: the guard is that no *un-instantiated* `momentK D` is
            # left, not that the string is free of the word — the first version
            # checked the latter and silently dropped every statement naming two
            # different orders, which is exactly the ladder this cycle wanted.
            if "^" in s or "momentK D" in s:
                continue
            out.append((f"{r[3]}@k={k}", s))
    return out


def inventory():
    """Every `ℕ`-linear fact `equiv_check` collects, as a vector `0 ≤ f`.

    `424`: seeding the cone by hand with four facts was the first
    version's error — *"not in this cone"* then meant *"not implied by the four
    I happened to name"*, and the simplest survivor turned out to be
    `Blindness.N_add_Noff_le_Nstar`, on disk since long before.  The seed is now
    the whole inventory.
    """
    import re
    import equiv_check as eq
    import tightness as ti
    out, skipped = {}, []
    for name, stmt in list(eq.facts()) + quantified():
        if "≤" not in stmt:
            continue
        lhs, rhs = stmt.split("≤", 1)
        el, er = ti.to_expr(lhs), ti.to_expr(rhs)
        if el is None or er is None:
            skipped.append(name)
            continue
        vec = []
        try:
            for i in range(len(BASIS)):
                e = derived([1 if k == i else 0 for k in range(len(BASIS))])
                vec.append(eval(er, {"__builtins__": {}}, e)
                           - eval(el, {"__builtins__": {}}, e))
        except Exception:
            skipped.append(name)
            continue
        out[name] = vec
    return out, skipped


# Four facts kept by name for the calibration below; the live cone uses
# `inventory()`.
KNOWN = {
    "mass_charges_every_class":
        [1, 0, 0, 0, 0, -1, -3, -3, -2, -2],
    "two_mul_haunted_add_two_mul_offLineOnly_le_Noff":
        [0, 1, 0, 0, 0, 0, -2, 0, 0, -2],
    "Noff_le_N":
        [1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    "two_mul_N_le_Nstar_add_Nsc":
        [-2, 0, 1, 0, 0, 1, 0, 0, 0, 0],
}

CALIBRATION = [
    ("a known fact is in its own cone", KNOWN["mass_charges_every_class"], True),
    ("positivity is in the cone", [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], True),
    ("`0 ≤ −N` is not", [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0], False),
]


def main():
    cols = list(KNOWN.values()) + unit_cols()
    ok = 0
    for why, d, want in CALIBRATION:
        got = in_cone(cols, d)
        good = got == want
        ok += good
        print(f"  [{'ok ' if good else 'FAIL'}] want={want!s:5s} got={got!s:5s} {why}")
    if ok != len(CALIBRATION):
        die_harness("the calibration no longer holds; the simplex changed")
    print(f"  calibration {ok}/{len(CALIBRATION)} as designed.")
    print()
    inv, skipped = inventory()
    print("=== the cone ===")
    print(f"  generated by {len(inv)} facts from equiv_check's inventory and "
          f"the {len(BASIS)} unit vectors")
    print(f"  {len(skipped)} facts skipped, named: {', '.join(sorted(set(skipped))) or 'none'}")
    # `427`: every generator — instantiated ones especially — is checked on the
    # box before it is trusted.  A textual substitution that produced a false
    # statement would otherwise poison every later answer.
    import tightness as ti
    box = list(ti.profiles(6, 4))
    for n, v in inv.items():
        for prof in box:
            c = ti.counts(prof)
            c = {**c, "momentK_1": c["N"], "momentK_2": c["Nstar"],
                 "momentK_3": c["thirdMoment"], "momentK_4": c["fourthMoment"]}
            if sum(k * c[b] for b, k in zip(BASIS, v)) < 0:
                die_harness(f"generator {n} is false at profile {prof}")
    print(f"  all {len(inv)} generators verified on {len(box)} profiles.")
    missing = [n for n in READS
               if not any(g == n or g.startswith(n + "@") for g in inv)]
    if missing:
        die_harness(f"the reader cannot see {missing} — see READS")
    print(f"  reader sees all {len(READS)} declarations it is required to.")
    bad = [n for n, v in inv.items() if not in_cone(list(inv.values()) + unit_cols(), v)]
    if bad:
        die_harness(f"a fact is not in the cone it generates: {bad}")
    print("  every generator is in its own cone, as it must be.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
