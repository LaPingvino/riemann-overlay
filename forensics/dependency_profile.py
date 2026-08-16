#!/usr/bin/env python3
"""Measure this overlay against the dependency it is built on.

**Why this exists.**  `267` was asked whether the two codebases differ as
"narrow and deep" against "wide and shallow".  That is a testable claim and it
turned out to be **backwards**, so the answer needed measuring rather than
asserting, and the measurement needs to be re-runnable rather than a paragraph
that ages.

**What it measures, and what each number is a proxy for.**

* *size* — files, lines, declarations.  No interpretation; just scale.
* *texture* — theorems per definition, lines per theorem, median proof length.
  These say how the code is written locally.  If they match, the two projects
  write Lean the same way and any difference is in what they write **about**.
* *depth signature* — proofs over 50 lines, and integer literals above `10^12`.
  Certified interval arithmetic shows up as enormous rationals and long
  computational proofs; nothing else in a Lean file looks like that.
* *breadth signature* — subject directories and top-level namespaces.  How many
  distinct things the project is about.
* *consumption* — what fraction of the dependency our build actually reaches.
  This is the number that decides whether "get more out of the dependency" is
  even available as a strategy.

**The one methodological trap, recorded because `267` fell into it.**  The
reachability walk must start from `Riemann.lean`, the *root* module, and not
from `Riemann/*.lean`.  The root imports `Zeta23.PairCeiling.CeilingLaw256` and
nothing in the directory does; starting from the directory alone reports `2.1%`
where the truth is `5.2%`, and reports `PairCeiling` unreachable when
`#check @Zeta23.PairCeiling.ceiling_law256` resolves under `import Riemann`.
A reachability figure that disagrees with the kernel is wrong, and the kernel is
the check.

Exit: always 0 — this is an instrument, not a guard.  It asserts nothing about
whether the numbers are good.

Run:  python3 forensics/dependency_profile.py
"""

import collections
import os
import re
import statistics as st
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
DEP = os.path.join(ROOT, "vendor", "zeta23")
OURS = os.path.join(ROOT, "Riemann")
OURS_ROOT = os.path.join(ROOT, "Riemann.lean")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|structure)\s+([A-Za-z_][\w'\.]*)", re.M)
NEXT = re.compile(
    r"^(?:@\[|/--|private |protected |noncomputable |theorem |lemma |def |"
    r"abbrev |structure |end |namespace )", re.M)


def modules(root):
    out = {}
    for d, dirs, fs in os.walk(root):
        dirs[:] = [x for x in dirs if x != ".lake" and not x.startswith(".")]
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                mod = os.path.relpath(p, root)[:-5].replace(os.sep, ".")
                with open(p, encoding="utf-8") as fh:
                    out[mod] = fh.read()
    return out


def profile(src_map, label):
    text = "\n".join(src_map.values())
    body = re.sub(r"/-.*?-/", "", text, flags=re.S)
    decls = []
    for m in DECL.finditer(body):
        nxt = NEXT.search(body[m.end():])
        seg = body[m.end(): m.end() + (nxt.start() if nxt else 400)]
        decls.append((m.group(1), seg.count("\n") + 1))
    thm = [n for k, n in decls if k in ("theorem", "lemma")]
    dfn = [1 for k, _ in decls if k in ("def", "structure", "abbrev")]
    nums = [int(x) for x in re.findall(r"(?<![\w.])(\d{4,})(?![\w.])", body)]
    dirs = {os.path.dirname(m.replace(".", os.sep)) for m in src_map}
    return {
        "label": label,
        "files": len(src_map),
        "lines": sum(s.count("\n") for s in src_map.values()),
        "theorems": len(thm),
        "defs": len(dfn),
        "per_def": len(thm) / max(len(dfn), 1),
        "lines_per_thm": sum(s.count("\n") for s in src_map.values()) / max(len(thm), 1),
        "median_proof": st.median(thm) if thm else 0,
        "long_proofs": sum(1 for n in thm if n > 50),
        "max_proof": max(thm) if thm else 0,
        "big_literals": sum(1 for n in nums if n > 10 ** 12),
        "max_digits": max((len(str(n)) for n in nums), default=0),
        "namespaces": len(set(re.findall(r"^namespace\s+([\w.]+)", body, re.M))),
        "subject_dirs": len({d for d in dirs if d}),
    }


def reachable(dep, ours_text):
    imports = {m: set(re.findall(r"^import\s+([\w.]+)", s, re.M))
               for m, s in dep.items()}
    roots = set(re.findall(r"^import\s+(Zeta23[\w.]*)", ours_text, re.M))
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(x for x in imports.get(m, ()) if x in dep)
    return roots, seen


def main():
    dep = modules(DEP)
    ours = modules(OURS)
    if not dep or not ours:
        print("nothing to measure; is vendor/zeta23 present?")
        return 0

    A = profile(dep, "zeta-23 (dependency)")
    B = profile(ours, "riemann overlay (ours)")

    print(f"{'':32s} {'zeta-23':>14s} {'overlay':>12s}   {'ratio':>7s}")
    print("  " + "-" * 66)

    def row(k, key, fmt="{:,.0f}"):
        a, b = A[key], B[key]
        r = f"{a / b:.1f}x" if b else "—"
        print(f"  {k:30s} {fmt.format(a):>14s} {fmt.format(b):>12s}   {r:>7s}")

    print("  SIZE")
    row("Lean files", "files")
    row("lines", "lines")
    row("theorems + lemmas", "theorems")
    row("definitions", "defs")
    print("  TEXTURE  (how the Lean is written)")
    row("theorems per definition", "per_def", "{:.2f}")
    row("lines per theorem", "lines_per_thm", "{:.1f}")
    row("median proof length", "median_proof", "{:.0f}")
    print("  DEPTH SIGNATURE  (certified numerics)")
    row("proofs over 50 lines", "long_proofs")
    row("longest proof", "max_proof")
    row("integer literals > 10^12", "big_literals")
    row("digits in largest literal", "max_digits")
    print("  BREADTH SIGNATURE  (how many subjects)")
    row("subject directories", "subject_dirs")
    row("namespaces", "namespaces")

    # Reachability — from the ROOT module, see the docstring's trap.
    text = ""
    for p in [OURS_ROOT] + [os.path.join(OURS, f) for f in sorted(os.listdir(OURS))]:
        if p.endswith(".lean") and os.path.exists(p):
            with open(p, encoding="utf-8") as fh:
                text += fh.read()
    roots, seen = reachable(dep, text)

    def count(mods):
        t = l = 0
        for m in mods:
            b = re.sub(r"/-.*?-/", "", dep.get(m, ""), flags=re.S)
            t += len(DECL.findall(b))
            l += dep.get(m, "").count("\n")
        return t, l

    tr, lr = count(seen)
    ta, la = count(dep)
    print()
    print("  CONSUMPTION  (how much of the dependency our build reaches)")
    print(f"    entry points        : {', '.join(sorted(roots))}")
    print(f"    modules reachable   : {len(seen):>5} of {len(dep):<6} {100*len(seen)/len(dep):5.1f}%")
    print(f"    declarations        : {tr:>5} of {ta:<6} {100*tr/max(ta,1):5.1f}%")
    print(f"    lines               : {lr:>5,} of {la:,} {100*lr/max(la,1):5.1f}%")

    un = collections.Counter()
    for m, s in dep.items():
        if m not in seen:
            un[m.split(".")[1] if m.count(".") >= 1 else m] += s.count("\n")
    print("    largest unreached areas, by lines:")
    for d, n in un.most_common(6):
        print(f"      {d:26s} {n:>7,}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
