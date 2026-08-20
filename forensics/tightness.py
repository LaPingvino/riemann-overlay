#!/usr/bin/env python3
"""Which of our `ZeroData` inequalities are attained, and by which profile.

**Why this exists.**  `419` proved `Blindness.mass_charges_every_class`'s weights
maximal by exhibiting a profile attaining it with every class occupied.  That
argument is mechanical and it generalises: `417`'s
`Blindness.profile_realisable` says a multiset of `(mass, off-line mass)` pairs
is some `ZeroData`'s profile **exactly** when every entry has mass `≥ 1`,
off-line mass `≤` mass and off-line mass even.  So an admissible profile making
an inequality tight is a *proof* that its coefficients cannot be improved, and
one making it slack everywhere in the box is evidence — not proof — that they
can.

`317`'s `forensics/equiv_check.py` asked which of these inequalities are the same
one.  This asks which are sharp.

**What it does.**  Takes the same hypothesis-free `ℕ`-linear facts
`equiv_check` collects, evaluates both sides on every admissible profile in a
search box, and reports for each: the smallest attaining profile, or `slack`
with the smallest gap found.

**What it is not.**  Not a guard, and `slack` is not a theorem — it is *"no
witness in this box"*, which `R17` says is not the same as *"no witness"*.  The
box is printed with every run.

**Honest skips.**  A statement this file cannot parse is **counted and named**,
never dropped silently — `S49`'s family, and the reason `equiv_check` carries a
sentinel.

Exit: 0 report printed · 5 harness failure.

Run:  python3 forensics/tightness.py [--max-mass N] [--max-atoms K]
"""

import itertools
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import equiv_check as eq  # noqa: E402  — the fact list is shared, not forked


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the inequalities.  Exit 5.")
    sys.exit(5)


def counts(profile):
    """Every ordinate functional, read off a profile of `(mass, offline)` pairs."""
    on = [h - o for h, o in profile]
    return {
        "N": sum(h for h, _ in profile),
        "Nstar": sum(h * h for h, _ in profile),
        # `426`: the moment functionals are sums over the profile like the
        # rest, so they belong here.  `offLinePoints` does **not** — it counts
        # distinct off-line *points*, and a profile entry `(h, o)` records the
        # off-line mass `o` without saying across how many distinct `β` it is
        # spread.  It stays out for the same reason `distinctZeros` is excluded
        # from `equiv_check`: it is not a functional of the profile.
        "thirdMoment": sum(h ** 3 for h, _ in profile),
        "fourthMoment": sum(h ** 4 for h, _ in profile),
        # `427`: `momentK D j` for the small `j` the box uses, so that theorems
        # quantified over the order can be instantiated and read.
        "momentK_1": sum(h for h, _ in profile),
        "momentK_2": sum(h ** 2 for h, _ in profile),
        "momentK_3": sum(h ** 3 for h, _ in profile),
        "momentK_4": sum(h ** 4 for h, _ in profile),
        "Noff": sum(o for _, o in profile),
        "Nsc": sum(1 for h, _ in profile if h == 1),
        "NscStd": sum(1 for (h, o) in profile if h - o == 1),
        "atomCount": len(profile),
        "oddAtoms": sum(1 for h, _ in profile if h % 2 == 1),
        "oddAbove": sum(1 for (h, o) in profile if (h - o) % 2 == 1 and h - o != 1),
        "evenOnAt": sum(1 for (h, o) in profile if (h - o) % 2 == 0 and h - o != 0),
        "offLineOnly": sum(1 for (h, o) in profile if h == o),
        "hauntedCount": sum(1 for (h, o) in profile if h - o == 1 and h != 1),
        "onLineOrdinates": sum(1 for x in on if x % 2 == 1)
                           + sum(1 for x in on if x % 2 == 0 and x != 0),
        "onLinePoints": sum(1 for x in on if x != 0),
    }


NAMES = set(counts([(1, 0)]).keys())
TOKEN = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")


def to_expr(side):
    """Lean's `2 * hauntedCount D` to Python's `2 * hauntedCount`, or None."""
    s = side.replace("D.", " ").replace("(", " ( ").replace(")", " ) ")
    out = []
    for tok in s.split():
        if tok == "D":
            continue
        if TOKEN.fullmatch(tok):
            if tok not in NAMES:
                return None
            out.append(tok)
        elif tok in {"+", "*", "-", "(", ")"} or tok.isdigit():
            out.append(tok)
        else:
            return None
    return " ".join(out)


def profiles(max_mass, max_atoms):
    entries = [(h, o) for h in range(1, max_mass + 1)
               for o in range(0, h + 1) if o % 2 == 0]
    for k in range(1, max_atoms + 1):
        for combo in itertools.combinations_with_replacement(entries, k):
            yield list(combo)


FRONTIER_DOC = """`421`: the box does more than check known bounds.

Because every profile in it is realised (`417`), a shape that **fails** on the box
is refuted outright, and the extremal coefficient found on the box is an upper
bound for the true one.  A shape that *holds* on the box is a **conjecture** —
`R17` — and is printed as one.
"""


def frontier(box, lhs, rhs_const, rhs_var, hi=8):
    """Largest integer `a` with `a·lhs ≤ rhs_const + b·rhs_var` on the box,
    for each `b`.  Returns {b: a}."""
    out = {}
    for b in range(0, 5):
        best = hi
        for p in box:
            c = counts(p)
            L, R0, R1 = c[lhs], c[rhs_const], c[rhs_var]
            if L == 0:
                continue
            best = min(best, (R0 + b * R1) // L)
            if best == 0:
                break
        out[b] = best
    return out


def ratio_table(box, hi=9):
    """For each ordered pair, the least integer `c` with `X ≤ c·Y` on the box."""
    names = sorted(NAMES)
    rows = []
    for x in names:
        for y in names:
            if x == y:
                continue
            need = 0
            ok = True
            for p in box:
                c = counts(p)
                if c[y] == 0:
                    if c[x] > 0:
                        ok = False
                        break
                    continue
                need = max(need, -(-c[x] // c[y]))
                if need > hi:
                    ok = False
                    break
            if ok:
                rows.append((x, y, need))
    return rows


def main():
    argv = sys.argv[1:]
    def opt(flag, default):
        return int(argv[argv.index(flag) + 1]) if flag in argv else default
    max_mass, max_atoms = opt("--max-mass", 6), opt("--max-atoms", 4)

    facts = eq.facts()
    if not facts:
        die_harness("equiv_check.facts() returned nothing")
    box = list(profiles(max_mass, max_atoms))

    print("=== which ZeroData inequalities are attained ===")
    print(f"  box: masses 1..{max_mass}, up to {max_atoms} ordinates, "
          f"{len(box)} admissible profiles (`417`: every one of them is a profile)")
    print(f"  facts from equiv_check: {len(facts)}")

    tight, slack, skipped = [], [], []
    for name, stmt in facts:
        if "≤" not in stmt:
            continue
        lhs, rhs = stmt.split("≤", 1)
        el, er = to_expr(lhs), to_expr(rhs)
        if el is None or er is None:
            skipped.append(name)
            continue
        best = None
        for p in box:
            c = counts(p)
            try:
                gap = eval(er, {"__builtins__": {}}, c) - eval(el, {"__builtins__": {}}, c)
            except Exception:
                skipped.append(name)
                best = "ERR"
                break
            if best == "ERR":
                break
            if gap < 0:
                die_harness(f"{name} is FALSE at profile {p} — the statement "
                            f"index and the evaluator disagree")
            if best is None or gap < best[0]:
                best = (gap, p)
        if best == "ERR":
            continue
        if best[0] == 0:
            tight.append((name, best[1]))
        else:
            slack.append((name, best[0], best[1]))

    print()
    print(f"  [tight] {len(tight)} — attained in the box, so the coefficients "
          f"cannot be improved")
    for name, p in sorted(tight):
        print(f"          {name:52s} {p}")
    print()
    print(f"  [slack] {len(slack)} — no witness IN THIS BOX; `R17`: that is not "
          f"a proof of slack")
    for name, gap, p in sorted(slack):
        print(f"          {name:52s} min gap {gap} at {p}")
    print()
    print(f"  [skipped] {len(skipped)} — not parseable by this evaluator, named "
          f"rather than dropped")
    for name in sorted(set(skipped)):
        print(f"          {name}")

    if "--frontier" in argv:
        print()
        print("=== the bridge frontier, searched ===")
        print(FRONTIER_DOC)
        fr = frontier(box, "NscStd", "N", "Nsc")
        for b, a_ in sorted(fr.items()):
            print(f"  largest a with a·NscStd ≤ N + {b}·Nsc on the box: {a_}")
        print()
        print("=== least c with X ≤ c·Y on the box (c ≤ 9) ===")
        print("  a CONJECTURE per row (`R17`); a missing pair is refuted by the box")
        for x, y, c_ in ratio_table(box):
            # `421`: a coefficient equal to the box's largest mass is an
            # ARTEFACT of the box, not a conjecture — `N ≤ 6·atomCount` says
            # only that no ordinate here has mass above `6`.  Flagged, not
            # printed as a finding.
            tag = "  [BOX ARTEFACT]" if c_ >= max_mass else ""
            print(f"  {x:18s} ≤ {c_} * {y}{tag}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
