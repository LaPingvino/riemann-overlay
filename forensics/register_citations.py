#!/usr/bin/env python3
"""Every declaration name the *registers* cite, resolved against the sources.

**Why this exists.**  `371`'s might-mean, unadopted for thirty-eight cycles:

> what the registers need is not more linting of their reasoning but a re-run of
> every mechanical enumeration they contain.

`forensics/citation_check.py` follows the names in `Riemann/`'s docstrings and in
`MAP.md`.  Nothing followed the names in the other eighteen registers, and those
are where the project states what it currently believes.  `406` and `407` both
shipped with a stale register row that a human caught — `board`'s `StarBound`
roster and `MAP.md`'s supplier table.

**The resolver is shared, not forked.**  `declarations`, `resolves` and `ALLOW`
are imported from `citation_check`; a fix to name resolution lands in one place.
What is new here is the *surface* and the live/historical split.

**Live vs historical.**  `CLAIMS.md`, `ISSUES.md`, `LEADS.md`, `PRICES.md`,
`RULING.md`, `STATEMENTS.md` and `README.md` describe what is true **now**: a
name that resolves to nothing is a defect.  `SESSION.md`, `SURPRISES.md`,
`FAILURES.md`, `E.md`, `A.md`, `S.md`, `NIGHT.md` are **logs**: a name that was
correct when it was written is not a defect, and renaming a declaration does not
retroactively falsify the entry that used the old name.  Both are reported; only
the live set is scored.

**A report, not a guard.**  It is deliberately not in `session_gate`'s roster.
`373` found that a green light nobody has seen go red is a tally; this one has
not been observed failing, and adding a seventeenth roster entry is a change to
the process every cycle runs.  Rostering it is a ruling, not a script's decision.
"""

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import citation_check as cc  # noqa: E402

ROOT = cc.ROOT

LIVE = ("CLAIMS.md", "ISSUES.md", "LEADS.md", "PRICES.md", "RULING.md",
        "STATEMENTS.md", "README.md", "METHOD.md", "VERIFYING.md")
HISTORICAL = ("SESSION.md", "SURPRISES.md", "FAILURES.md", "E.md", "A.md",
              "S.md", "NIGHT.md", "LOOP.md", "FRAMING.md", "F.md")

# Registers backtick far more than declarations.  These shapes are prose
# furniture, filtered before the resolver sees them so the dangling list stays
# readable — the failure mode `342` named, a report nobody can finish reading.
NOISE = re.compile(r"""
      ^[RSWLE]?\d+[a-z]?$          # session numbers, R-rules, S-rows, W-items
    | ^v\d                         # base tags
    | [/\s+*^−<>=%]                # paths, math, ledger fragments
    | \.(md|py|lean|go|json|tsv|log|txt)$
""", re.VERBOSE)


# Three shapes resolve to nothing and are not defects, so they are bucketed
# rather than reported.  `SCRIPTS` are this directory's own tools, which the
# registers name constantly.  `MATHLIB` is any dotted name under a namespace the
# project does not own — the resolver knows our tree and the vendored one, and a
# Mathlib citation in a register is a citation, not a dangling name.  `SHORT` is
# subscript-shaped mathematics (`a_m`, `F_q`, `M_main`) that happens to be
# identifier-shaped.
SCRIPTS = {f[:-3] for f in os.listdir(os.path.dirname(os.path.abspath(__file__)))
           if f.endswith(".py")}
MATHLIB_ROOTS = ("Finset", "Nat", "Int", "Real", "Complex", "Classical", "Quot",
                 "Multiset", "Filter", "Function", "Set", "List", "Polynomial",
                 "Metric", "MeasureTheory", "Topology", "Order", "Decidable",
                 "Mathlib", "Std", "Lean", "Sum", "Prod", "Option", "Subtype")


HOST = re.compile(r"\.(org|com|ai|uk|io|net|dev)$")
TACTICS = {"simp_all", "norm_num", "push_cast", "field_simp", "exact_mod_cast",
           "simp_only", "nlinarith", "linear_combination", "omega", "positivity"}
MODULES = {"Riemann." + f[:-5] for f in os.listdir(os.path.join(ROOT, "Riemann"))
           if f.endswith(".lean")} if os.path.isdir(os.path.join(ROOT, "Riemann")) else set()


# `409`, the first cycle this script ran: correcting a dangling citation **in
# place** — which the project's corrections rule requires — leaves the wrong name
# on the page, inside the retraction that names it.  So the report would keep
# flagging a defect that has been fixed.  These are the names the registers
# deliberately still carry as retracted text, each with the entry that retracted
# it.  Adding one here is only honest next to a correction that names it.
RETRACTED = {
    "configAt_offAt": "409 — LEADS.md and CLAIMS.md (twice), never existed; "
                      "the real names are offAt_configAt_self / "
                      "offAt_configAt_other",
    "Blindness.configAt_offAt": "409 — CLAIMS.md, qualified form of the same "
                                "phantom",
    "proportion_of_noHaunted_three": "409 — CLAIMS.md, never existed; the "
                                     "general-m statement is "
                                     "proportion_of_noSmallHaunted",
}


# `410`: `STATEMENTS.md` carries the project's own rename table — three axioms
# that became hypotheses at `ISSUES #8`.  Those names are *deliberately* kept in
# the live registers, so they are witnessed history, not dangling citations.  The
# bucket is sourced from that table rather than guessed, and each entry names
# what replaced it.  Without this, `410`'s suggester would rank `farmer_ki`
# against `FarmerKiTransfer` and report a kept name as a probable invention.
FORMER = {
    "fujii_with_closePairs": "ClosePairBookkeeping (STATEMENTS.md, ISSUES #8)",
    "farmer_ki": "FarmerKiTransfer (STATEMENTS.md, ISSUES #8)",
    "narrowBox_starBound": "BGSTNarrowBox (STATEMENTS.md, ISSUES #8)",
    "baseline_przz": "deleted at SESSION 233 on Joop's ruling "
                     "(Riemann/Assumptions.lean:207)",
    "Assumptions.baseline_przz": "deleted at SESSION 233 (qualified form)",
}


# `410`: the residue after triage.  Each of these was checked by hand and is a
# citation of something real that is simply not a declaration of ours — a bare
# Mathlib lemma, a ledger field, a `forensics/` internal, or a label from the
# provenance graph.  The entry is the reason; an unreasoned addition here would
# turn the report back into a count.
PROSE = {
    "toFinset_add": "Mathlib, Multiset.toFinset_add — cited bare in LEADS.md",
    "toFinset_replicate": "Mathlib, Multiset.toFinset_replicate — cited bare",
    "base.version": "ledger field written by tools/proportion.go",
    "base.hash": "ledger field written by tools/proportion.go",
    "CONE_EXPECTED": "forensics/board.py internal",
    "provenance_lint.NODES": "forensics/provenance_lint.py internal",
    "str.replace": "Python, in METHOD.md's description of a script",
    "Namespace.lemma": "a template placeholder in CLAIMS.md, not a name",
    # `VERIFYING.md:291` lists provenance_lint's graph node labels; they are
    # data in that script, not Lean declarations.
    "class_closure": "provenance_lint node label (VERIFYING.md:291)",
    "Lemma1_cap3": "provenance_lint node label (VERIFYING.md:291)",
    "GGOS_floor": "provenance_lint node label (VERIFYING.md:291)",
    "sieve_twin": "provenance_lint node label (VERIFYING.md:291)",
    "MRT_corr": "provenance_lint node label (VERIFYING.md:291)",
    "explicit_formula": "provenance_lint node label (VERIFYING.md)",
    "residue_class": "paper-side term in LEADS.md, not a declaration",
    "residue_source": "paper-side term in LEADS.md, not a declaration",
    "exp_bound": "paper-side term in PRICES.md, not a declaration",
    "sin_bound": "paper-side term in PRICES.md, not a declaration",
}


def bucket(t):
    if t in PROSE:
        return "prose-checked"
    if t in RETRACTED:
        return "retracted"
    if t in FORMER:
        return "former"
    if t in SCRIPTS:
        return "script"
    if HOST.search(t) or t in TACTICS:
        return "prose"
    if t in MODULES or t.endswith(".toml") or t.endswith(".yml"):
        return "prose"
    if t.split(".")[0] in MATHLIB_ROOTS:
        return "mathlib"
    head = t.split("_")[0]
    if "." not in t and len(head) <= 2:
        return "short"
    if t.startswith("_"):
        return "short"
    return "dangling"


def tokens(path):
    with open(os.path.join(ROOT, path), encoding="utf-8") as fh:
        s = fh.read()
    seen, filtered = {}, 0
    for t in cc.TICK.findall(s):
        t = t.strip()
        if not t:
            continue
        if NOISE.search(t) or not cc.IDENT.match(t):
            filtered += 1
            continue
        if "_" not in t and "." not in t:
            filtered += 1           # single words are prose
            continue
        seen.setdefault(t, path)
    return seen, filtered


def pieces(name):
    """Tokens of a declaration name, lowercased.  `410`.

    Names are split on `_` and `.` and on camelCase boundaries, because the
    invention shape `409` found is a *permutation* of real tokens —
    `configAt_offAt` against `offAt_configAt_self` — which edit distance ranks
    nowhere and token overlap ranks first.
    """
    parts = re.split(r"[_.]", name)
    out = []
    for p in parts:
        out += [w.lower() for w in re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z0-9]+", p)]
    return set(w for w in out if w)


def nearest(tok, known, n=3):
    """The known names sharing the most tokens with `tok`.  An aid, not a verdict."""
    want = pieces(tok)
    if not want:
        return []
    scored = []
    for k in known:
        have = pieces(k)
        inter = len(want & have)
        if inter < 2:
            continue
        scored.append((inter / len(want | have), inter, k))
    scored.sort(reverse=True)
    return [(round(s, 2), k) for s, _, k in scored[:n]]


def main():
    ours, fields, _ = cc.declarations(cc.SRC)
    dep_names, dep_fields, dep_modules = cc.declarations(cc.DEP)
    # `410`: the dependency's **structure fields** were being discarded here, so
    # `FamilyHyps.lam_const` — a real field of a real vendored structure,
    # `vendor/zeta23/Zeta23/XiPrime/ExplicitFormula.lean:147` — was reported
    # dangling.  The first defect this script found was its own.
    dep_names = dep_names | dep_fields
    known = ours | fields

    def dangling(path):
        toks, filtered = tokens(path)
        unres = [t for t in sorted(toks)
                 if not cc.resolves(t, known, dep_names, dep_modules)
                 and t not in cc.ALLOW]
        bad = [t for t in unres if bucket(t) == "dangling"]
        return toks, filtered + (len(unres) - len(bad)), bad

    print("=== declaration names cited in the registers ===")
    print(f"  resolver shared with citation_check; {len(known)} of our names, "
          f"{len(dep_names)} vendored")

    totals = {}
    for tag, group in (("live", LIVE), ("log ", HISTORICAL)):
        gt = gf = 0
        rows = []
        for path in group:
            if not os.path.exists(os.path.join(ROOT, path)):
                continue
            toks, filtered, bad = dangling(path)
            gt += len(toks)
            gf += filtered
            rows.append((path, len(toks), filtered, bad))
        totals[tag] = rows
        print()
        print(f"  [{tag}] {'register':18s} {'cited':>6s} {'filtered':>9s} "
              f"{'dangling':>9s}")
        for path, n, filtered, bad in rows:
            print(f"         {path:18s} {n:6d} {filtered:9d} {len(bad):9d}")
        print(f"         {'— total —':18s} {gt:6d} {gf:9d} "
              f"{sum(len(b) for _, _, _, b in rows):9d}")

    live_bad = [(p, t) for p, _, _, bad in totals["live"] for t in bad]
    log_bad = [(p, t) for p, _, _, bad in totals["log "] for t in bad]

    show = live_bad + log_bad if "--list" in sys.argv else live_bad
    for p, tok in show:
        near = nearest(tok, known) if "--near" in sys.argv else []
        tag = "DANGLING" if "--list" in sys.argv else "LIVE DANGLING"
        print(f"  [{tag}] {tok:44s} {p}")
        for score, k in near:
            print(f"      ~{score:>4} {k}")

    print()
    print(f"  prose-checked {len(PROSE)} — checked by hand at `410`; real "
          f"things that are not declarations of ours, each with its reason.")
    print(f"  former        {len(FORMER)} — names the project renamed or "
          f"deleted on the record, kept deliberately (STATEMENTS.md).")
    print(f"  retracted     {len(RETRACTED)} — names the registers keep on the "
          f"page inside the correction that retracts them.")
    print(f"  live dangling {len(live_bad)} — these are findings: a register "
          f"that describes current state named something that resolves to "
          f"nothing.")
    print(f"  log  dangling {len(log_bad)} — these are context, NOT findings. "
          f"A log entry may name a declaration that has since been renamed; "
          f"`R17` cuts both ways and a count here is not a defect rate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
