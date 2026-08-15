#!/usr/bin/env python3
"""The scope gate — ATTEMPTED AND FAILED ITS CALIBRATION.  Do not rebuild this.

⚠️ **This instrument does not work, and the reason is worth keeping.**  Built in
`SESSION 113` to catch `SURPRISES` S37/S38 (prose one quantifier ahead of its
theorem).  Calibration: **0 of 2** — it fires on neither of the two sentences it
was designed for, and its single live flag is a false positive.

**Why it cannot work as designed.**  The gate looks for a universal sentence
*citing* an existential theorem.  But both S37 and S38 drift precisely by
**dropping the citation**: the offending sentence generalises away from the
theorem and stops naming it, leaving the name in an adjacent paragraph.  Widening
the match to paragraph or section scope over-fires immediately, because every
session entry contains both universal prose and existential witnesses by design.

**The residue.**  The defect class may not be lintable at all; the control
remains re-reading the previous cycle before starting the next, which is what
caught S37 and S38 both.  Kept, unregistered as a guard, so a future cycle
recognises the idea and its cost rather than paying it again.

--- original intent, preserved ---

Catching prose that is one quantifier ahead of its theorem.

**Why this exists.**  `SURPRISES` S37 and S38 are the same defect, twice, four
cycles apart, and no instrument caught either.  Both were found by re-reading the
previous cycle by hand, which is not a guard.

Both have one mechanical signature:

    a sentence making a UNIVERSAL claim, citing a theorem whose statement is
    EXISTENTIAL.

* `S37` — "every positive proportion theorem is structurally incapable", citing
  `no_starBound_from_goodness`, whose statement is `∃ D, …` at the single
  proportion `3/4`.
* `S38` — "no argument using only `ProportionStd 0.6725` can certify above
  `0.50943`", citing `row_essentially_optimal`, whose statement is `∃ D, …` for
  one configuration while the claim ranges over families.

An existential theorem exhibits *one* object.  A universal sentence quantifies
over *all* of them.  The step between is exactly where both errors lived, and it
is never justified by the cited declaration alone.

**What this does NOT claim.**  A universal sentence citing an existential theorem
is not automatically wrong — a witness can refute a universal, which is the
honest form (`baseline_cap_witness` does this correctly, by being stated over
families itself).  The gate flags the *shape* and asks for the step to be shown.

Run:  python3 forensics/scope_gate.py FILE...
Requires the Lean declaration types; falls back to a cached list if `lake` is
unavailable, and says so rather than silently passing.
"""

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, os.pardir)

# Universal markers: the sentence ranges over a class, not an instance.
UNIVERSAL = [
    r"\bno (?:argument|theorem|statement|bound|proof|route|statistic)\b",
    r"\bevery\b", r"\bany\b", r"\ball\b",
    r"\bcannot be\b", r"\bnone\b", r"\bnothing\b",
    r"\bstructurally incapable\b", r"\bat any\b", r"\bwhatever\b",
]

# A citation looks like a Lean name; filenames are excluded as in claims_gate.
_EXT = r"(?:md|lean|py|toml|json|jsonl|go|txt|sh|yml|yaml)\b"
CITE = re.compile(r"\b([A-Z][A-Za-z0-9]*(?:\.(?!" + _EXT + r")[A-Za-z_][A-Za-z0-9_']*)+)")


def declaration_types():
    """name -> statement, from audit/Declarations.lean.  Empty on failure."""
    try:
        out = subprocess.run(
            ["lake", "env", "lean", "audit/Declarations.lean"],
            cwd=ROOT, capture_output=True, text=True, timeout=1800).stdout
    except Exception:
        return {}
    text = re.sub(r"\n\s+", " ", out)
    types = {}
    for line in text.splitlines():
        if " : " in line:
            name, _, stmt = line.partition(" : ")
            types[name.strip()] = stmt.strip()
    return types


def existential(stmt):
    """The statement exhibits an object rather than constraining all of them."""
    return "∃" in stmt


def sentences(text):
    for para in text.split("\n\n"):
        flat = " ".join(para.split())
        for s in re.split(r"(?<=[.!?])\s+", flat):
            s = s.strip()
            if s:
                yield s


def scan(text, label, types):
    hits = []
    for s in sentences(text):
        if not any(re.search(p, s, re.I) for p in UNIVERSAL):
            continue
        for m in CITE.finditer(s):
            name = m.group(1)
            for full, stmt in types.items():
                if full == name or full.endswith("." + name):
                    if existential(stmt):
                        hits.append((s, full))
                    break
    if hits:
        print(f"\n=== {label} ===")
        for s, name in hits:
            print(f"  [UNIVERSAL prose, EXISTENTIAL witness: {name}]")
            print(f"    {s[:150]}")
    return len(hits)


def main(argv):
    types = declaration_types()
    if not types:
        print("scope_gate: could not read declaration types "
              "(lake unavailable?) — NOT a pass, a non-run.", file=sys.stderr)
        return 2
    total = sum(scan(open(f, encoding="utf-8").read(), f, types)
                for f in argv[1:])
    print(f"\n{total} sentence(s) whose scope exceeds the cited witness.")
    if total:
        print("Per the gate: show the step from the witness to the class, or "
              "restate the sentence at the witness's own level.")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
