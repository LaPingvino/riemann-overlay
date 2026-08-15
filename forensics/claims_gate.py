#!/usr/bin/env python3
"""The overclaim gate — a linter that patrols PROSE, not mathematics.

**Why this exists.**  After seventeen night cycles the surprise register read
`tooling 9 / self 11`, with every new entry self-caught and none caught by an
instrument.  The guards were not failing; they were **saturated**.  Circularity,
scale and error-quality stopped occurring *because* `provenance_lint.py` exists,
and the error mass migrated to the one surface with no guard on it: the
exactness of our own sentences.

Two entries in a row were that shape:

* `S26` — "`(μ_T, offAt)` is **the exact** residue, nothing else at all."  True
  forward (`ledger_determined`), unwitnessed backward.  Retracted one cycle
  later when `offAt_not_minimal` showed the residue is an upper bound.
* `S27` — "the window computation is **not in the repo** and its repair needs
  the source paper."  A *negative* exactness claim about our own record, filed
  without searching for a specification.  The spec was three lines above the
  table.

Both are the same defect: a claim of exactness or completeness with only one
direction witnessed.

**The rule.**  Any sentence using exactness / uniqueness / completeness
language must cite a kernel-certified declaration in **both** slots —
`forward` (what is established) and `converse` (what rules out more).  An empty
converse slot does not block the text; it **rewrites** it to the certified
direction: "exact" becomes "sufficient", "the" becomes "a", "cannot" becomes
"is not known to".

Run over a file or stdin:  `python3 forensics/claims_gate.py FILE...`
Exit 1 if any flagged sentence lacks a converse witness.
"""

import re
import sys

# Positive exactness: claims that nothing more is needed / nothing else works.
POSITIVE = [
    r"\bexactly the\b", r"\bthe exact\b", r"\bexact\b",
    r"\bminimal\b", r"\bthe unique\b", r"\bthe only\b",
    r"\bnothing else\b", r"\bnothing more\b", r"\bnothing beyond\b",
    r"\bif and only if\b", r"\biff\b",
    r"\bcomplete(?:ly)? characteris", r"\bthe whole residue\b",
    r"\bnecessary and sufficient\b",
]

# Negative exactness — the S27 shape: impossibility claims about our own record.
NEGATIVE = [
    r"\bcannot be\b", r"\bis not in the repo\b", r"\bno code\b",
    r"\bnever\b", r"\bimpossible\b", r"\bunreproducible\b",
    r"\bhas no\b", r"\bdoes not exist\b", r"\blost\b",
]

# A converse witness looks like a Lean name: Namespace.lemma_name, or an
# explicit admission that the converse is open.
WITNESS = re.compile(r"[A-Z][A-Za-z0-9]*\.[A-Za-z_][A-Za-z0-9_']*"
                     r"|\bminimality open\b|\bconverse open\b"
                     r"|\bnot known to be minimal\b|\bupper bound\b")

DOWNGRADE = [
    ("the exact", "a sufficient"), ("exactly the", "a"),
    ("nothing else", "possibly more"), ("nothing more", "possibly more"),
    ("minimal", "sufficient"), ("the unique", "a"), ("the only", "a"),
    ("if and only if", "if"), ("cannot be", "is not known to be"),
]


# Sentences that are NOT claims by construction, and must not be flagged:
# markdown headings (they label, they do not assert) and kill conditions (they
# are deliberately counterfactual — stating one is the discipline, not a claim).
EXEMPT = re.compile(r"^\s*#|kill condition|^\s*\||superseded|RETRACTED|"
                    r"original note", re.I)

# Triage of the first live run (2026-08-15) found 3 true / 3 false out of six on
# CLAIMS.md.  Every false positive was one of two mechanical shapes, both
# excludable without touching the wordlist:
#
#   DIRECTIVE  — an instruction, not a claim: "Never cite as one.",
#                "**Never as a bound.**", "do not cite one as such".
#   DENIED     — the trigger appears inside a phrase being *denied*:
#                "grade C means not yet defined, not *that the class cannot be
#                defined*".
#
# Keeping these out is what turns a 50% signal into a usable one.
DIRECTIVE = re.compile(r"^\W*(never|do not|don't|always|cite|use|run|prefer)\b"
                       r"|\bnever cite\b|\bdo not cite\b|\bnever as a\b", re.I)
DENIED = re.compile(r"\bnot\s+\*?that\b|\bnot\s+\*[^*]*(cannot|never|"
                    r"impossible)", re.I)


def sentences(text):
    for para in text.split("\n\n"):
        if EXEMPT.match(para.strip()):
            continue
        flat = " ".join(para.split())
        for s in re.split(r"(?<=[.!?])\s+", flat):
            s = s.strip()
            if s and not EXEMPT.search(s) and not DIRECTIVE.match(s) \
                    and not DENIED.search(s):
                yield s


def downgrade(s):
    out = s
    for a, b in DOWNGRADE:
        out = re.sub(re.escape(a), b, out, flags=re.I)
    return out


def scan(text, label):
    flagged, failures = [], 0
    for s in sentences(text):
        pos = [p for p in POSITIVE if re.search(p, s, re.I)]
        neg = [p for p in NEGATIVE if re.search(p, s, re.I)]
        if not (pos or neg):
            continue
        has_witness = bool(WITNESS.search(s))
        flagged.append((s, pos + neg, has_witness))
        if not has_witness:
            failures += 1
    if flagged:
        print(f"\n=== {label} ===")
        for s, pats, ok in flagged:
            mark = "witnessed" if ok else "NO CONVERSE WITNESS"
            print(f"  [{mark}] {s[:110]}")
            if not ok:
                print(f"      downgrade -> {downgrade(s)[:110]}")
    return failures


def main(argv):
    if len(argv) > 1:
        total = sum(scan(open(f, encoding="utf-8").read(), f) for f in argv[1:])
    else:
        total = scan(sys.stdin.read(), "<stdin>")
    print(f"\n{total} flagged sentence(s) without a converse witness.")
    if total:
        print("Per the gate: ship the downgraded form, or supply the converse "
              "declaration. Do not ship the exact form unwitnessed.")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
