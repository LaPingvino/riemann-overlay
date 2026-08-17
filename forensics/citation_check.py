#!/usr/bin/env python3
"""Every declaration name a Lean docstring cites, resolved against the sources.

**Why this exists.**  `300` closed on *"the risk in this project is not
arithmetic but the citations threaded through prose that no instrument can
follow."*  Half of that sentence was wrong, and this file is the half.

`301` ran the screen it implies.  `Riemann/Zeta.lean`'s `zetaZeroData_N`
docstring said the proof finishes with `finsum_mem_finset`.  That name does not
resolve under this project's imports.  `270` had tried it, recorded at
`SESSION.md:12645` that it does not exist, used
`finsum_mem_eq_finite_toFinset_sum` on the proof's last line — and left the dead
name in the prose describing the fixed proof.  A wrong name from a failed
attempt fossilised in the docstring of the attempt that succeeded.

**What it does.**  Pulls backtick-quoted, identifier-shaped tokens out of every
`/-- … -/` in `Riemann/`, and resolves each against declarations in `Riemann/`
(theorem, lemma, def, abbrev, structure, axiom, instance, inductive), structure
field names, and the vendored dependency's declarations and module paths.
Namespace prefixes are tolerated on the way in — the project writes
`Basic.foo` and `Gaps.NarrowBox` meaning *"in that file"*, which is not a Lean
name, and treating those as dangling would drown the signal.

**Fail-closed, deliberately.**  Anything unresolved that is not in `ALLOW`
fails.  A new Mathlib citation therefore turns this red until someone checks the
name against the kernel and adds it — which is precisely the step `270` skipped.
The red is the mechanism, not a maintenance cost.

**`ALLOW` is a table of reasons, not a mute list.**  Each entry says why the
token resolves to nothing, and the categories are: notation the prose uses for a
quantity, a tactic, a field access spelled as a path, a forensics script, a
dependency module, a deliberate reference to something deleted, and Mathlib
names that resolve under `import Riemann` and were kernel-checked at `301`.

Exit: 0 every citation resolves or is allowed · 1 a citation dangles ·
5 harness failure.

Run:  python3 forensics/citation_check.py
      python3 forensics/citation_check.py --list   (every resolved citation)
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
SRC = os.path.join(ROOT, "Riemann")
DEP = os.path.join(ROOT, "vendor", "zeta23")

DOC = re.compile(r"/--(.*?)-/", re.S)
TICK = re.compile(r"`([^`\n]+)`")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'₀-₉]*)*$")
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|axiom|instance|inductive)\s+"
    r"([A-Za-z_][\w'.₀-₉]*)", re.M)

ALLOW = {
    # notation the prose uses for a quantity, with no declaration of that name
    "N_sc": "notation", "N_off": "notation", "N_d": "notation", "C_k": "notation",
    # tactics
    "filter_upwards": "tactic", "norm_num": "tactic",
    # a field access written as a path
    "Z.toFinset": "field access", "ordinates.toFinset": "field access",
    "ordinates.count": "field access", "hauntedSet.card": "field access",
    "_from_profile": "name suffix, quoted as a family",
    # this repo's own tooling
    "provenance_lint": "forensics script",
    "claims_gate": "forensics script",
    # dependency modules, named as modules rather than declarations
    "RiemannVonMangoldt.main": "zeta-23 module",
    "Zeta23.RiemannVonMangoldt.main": "zeta-23 module",
    # deleted on a ruling, and the sentence citing it says so
    "baseline_przz": "deleted at 233; the citation is historical",
    # Mathlib — each resolves under `import Riemann`, kernel-checked at 301
    "Complex.cos_bound": "mathlib", "Complex.exp_bound": "mathlib",
    "cos_bound": "mathlib, short form of Complex.cos_bound",
    "Finset.sum": "mathlib", "Finset.sum_image": "mathlib",
    "Finset.card_lt_card": "mathlib",
    "Finset.sum_multiset_map_count": "mathlib",
    "Multiset.filter": "mathlib", "Multiset.count_filter": "mathlib",
    "le_refl": "mathlib", "sub_div": "mathlib",
    "le_trans": "mathlib", "sub_mul": "mathlib",
    "finsum_mem_eq_finite_toFinset_sum": "mathlib",
    # `301`: the dead name, quoted by the correction that replaced it.  Its
    # one appearance is inside that correction at `Zeta.lean:58`.  Allowing it
    # costs the guard the ability to catch a *new* use of the same dead name,
    # which is the price of letting a correction quote what it corrects.
    "finsum_mem_finset": "dead name, quoted by its own correction",
}

# `S60`: a guard that has never demonstrated it can flag is unproven.  These run
# in-process on every invocation.  `S89`: no real defect sits in here — a
# calibration row that is a live defect leaves the guard permanently red.
CALIBRATION = [
    ("finsum_mem_finset_XXX", "flag", "a name resolving to nothing, not allowed"),
    ("zetaZeroData_N", "clear", "a declaration in Riemann/Zeta.lean"),
    ("Zeta23.Ncount", "clear", "a declaration in the vendored dependency"),
    ("N_sc", "clear", "notation, in ALLOW"),
]


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the citations.  Exit 5.")
    sys.exit(5)


def declarations(root):
    names, fields, modules = set(), set(), set()
    if not os.path.isdir(root):
        die_harness(f"missing tree: {root}")
    for d, dirs, fs in os.walk(root):
        dirs[:] = [x for x in dirs if x != ".lake" and not x.startswith(".")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(d, f)
            try:
                with open(p, encoding="utf-8") as fh:
                    s = fh.read()
            except OSError as exc:
                die_harness(f"cannot read {p}: {exc}")
            names |= set(DECL.findall(s))
            for m in re.finditer(r"^structure\s+\S+.*?$(.*?)(?=^\S)", s, re.M | re.S):
                fields |= set(re.findall(r"^\s{2}([a-zA-Z_][\w']*)\s*:",
                                         m.group(1), re.M))
            modules.add(os.path.relpath(p, root)[:-5].replace(os.sep, "."))
    return names, fields, modules


def resolves(tok, known, dep_names, dep_modules):
    last = tok.split(".")[-1]
    if tok in known or last in known:
        return True
    if tok in dep_names or last in dep_names:
        return True
    if tok in dep_modules or any(m.endswith(tok) for m in dep_modules):
        return True
    return False


def citations():
    out = {}
    for d, dirs, fs in os.walk(SRC):
        dirs[:] = [x for x in dirs if not x.startswith(".")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(d, f)
            with open(p, encoding="utf-8") as fh:
                s = fh.read()
            for m in DOC.finditer(s):
                line = s[:m.start()].count("\n") + 1
                for t in TICK.findall(m.group(1)):
                    t = t.strip()
                    if not IDENT.match(t):
                        continue
                    if "_" not in t and "." not in t:
                        continue           # single words are prose
                    if t.endswith(".md") or t.endswith(".lean"):
                        continue           # file names
                    out.setdefault(t, f"{os.path.relpath(p, ROOT)}:{line}")
    return out


def main():
    ours, fields, _ = declarations(SRC)
    dep_names, _, dep_modules = declarations(DEP)
    known = ours | fields
    cites = citations()

    bad = []
    for t, loc in sorted(cites.items()):
        if resolves(t, known, dep_names, dep_modules) or t in ALLOW:
            continue
        bad.append((t, loc))

    if "--list" in sys.argv:
        for t, loc in sorted(cites.items()):
            tag = "ALLOW" if t in ALLOW else ("ok   " if (t, loc) not in bad
                                              else "DANGL")
            print(f"  [{tag}] {t:44s} {loc}")

    print("=== declaration names cited in Lean docstrings ===")
    print(f"  cited          {len(cites)}")
    print(f"  allowed        {sum(1 for t in cites if t in ALLOW)}")
    print(f"  unresolved     {len(bad)}")

    cal = 0
    for tok, want, why in CALIBRATION:
        got = "clear" if (resolves(tok, known, dep_names, dep_modules)
                          or tok in ALLOW) else "flag"
        ok = got == want
        cal += ok
        print(f"  [{'ok ' if ok else 'FAIL'}] want={want:5s} got={got:5s} "
              f"{tok} — {why}")
    print(f"  calibration {cal}/{len(CALIBRATION)} as designed.")
    if cal != len(CALIBRATION):
        die_harness("the calibration no longer holds; the resolver changed")

    if bad:
        print()
        for t, loc in bad:
            print(f"  [DANGLING] {t:44s} {loc}")
        print()
        print("  A docstring names something that resolves to nothing.  Check it")
        print("  against the kernel; if it is a real Mathlib name, add it to ALLOW")
        print("  with that reason.  `301`: the step this replaces is the one that")
        print("  left `finsum_mem_finset` in the prose of the proof that fixed it.")
        return 1
    print("  every citation resolves or is allowed with a reason.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
