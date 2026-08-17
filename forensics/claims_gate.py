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

**What this instrument is not.**  It is lexical, so a phrase satisfies it.
`253` measured the exposure directly: appending *"and it is not a theorem"* to
*"this is the only route that survives"* clears the flag.  That was already true
of the older markers (`upper bound`, `converse open`) and is not a regression —
it is what a wordlist is.  The gate catches prose written without thinking about
its own warrant; it cannot catch prose written to get past the gate, and the
author it guards is the same author who could type the phrase.  Its value is
that the cheapest way past it is usually to say the true thing.
"""

import re
import sys

# Positive exactness: claims that nothing more is needed / nothing else works.
POSITIVE = [
    r"\bexactly the\b", r"\bthe exact\b", r"\bexact\b",
    r"\bminimal\b", r"\bthe unique\b", r"\bthe only\b",
    r"\bnothing else\b", r"\bnothing more\b", r"\bnothing beyond\b",
    r"\bif and only if\b", r"\biff\b",
    # `304`: `302` wrote "the cap is reached **exactly when** every ordinate is
    # a triple" — a set equality, wrong, and unflagged.  `\bexact\b` does not
    # match "exactly", and `\bexactly the\b` wants a noun after it.  This is
    # `iff` spelled as an adverb.
    #
    # **Narrowed after measuring, same cycle.**  The first attempt also carried
    # `exactly where`, `precisely where`, `exactly those`, `precisely those`.
    # Triage of what those added: `E.md`'s *"the plane appears precisely where
    # arithmetic enters"*, `LOOP.md`'s *"improvements to the trusted base are
    # precisely where vigilance relaxes"* (quoted again in `METHOD.md`), and
    # `RULING.md`'s *"leaves the project exactly where it is"* — four idioms,
    # no claims.  `where` and `those` are ordinary English; `when` and `if` are
    # where the biconditional lives.  `S39`: the filter is fitted to a triage,
    # and the triage is written down here.
    r"\bexactly when\b", r"\bexactly if\b", r"\bprecisely when\b",
    r"\bcomplete(?:ly)? characteris", r"\bthe whole residue\b",
    r"\bnecessary and sufficient\b",
]

# Identity assertions — the S30 shape: "X and Y are the same object".  Purchased
# by exactly one failure: "the /6 census result and the third-moment obstruction
# are two readings of one polynomial", which was false (sum m(m-1) vs
# sum m(m-1)(m-2), agreeing only at m = 3).  An identity claim is an exactness
# claim wearing the costume of an insight, and neither the wordlist above nor
# the lint nor the kernel was checking for it.
IDENTITY = [
    r"\bare the same\b", r"\bis the same\b", r"\bthe same (?:fact|object|theorem|thing|polynomial|statement)\b",
    r"\btwo readings of one\b", r"\bturn(?:s|ed)? out to be the\b",
    r"\bare one\b", r"\bis identically\b", r"\bare identical\b",
    r"\bis exactly the\b", r"\bare exactly the\b",
    r"\bnot a coincidence\b", r"\bsame (?:disease|shape|move) (?:as|seen)\b",
]

# Negative exactness — the S27 shape: impossibility claims about our own record.
NEGATIVE = [
    r"\bcannot be\b", r"\bis not in the repo\b", r"\bno code\b",
    r"\bnever\b", r"\bimpossible\b", r"\bunreproducible\b",
    r"\bhas no\b", r"\bdoes not exist\b", r"\blost\b",
]

# A converse witness looks like a Lean name — but NOT a filename.  Triage of the
# 2026-08-15 run found that `FAILURES.md`, `LEADS.md`, `S.md` and `Gauge.lean`
# all satisfied the old pattern, so **three of the four passing sentences passed
# on a filename alone**.  That is a false-NEGATIVE generator, and the more
# serious of the two defects the triage found: it silently exempts any sentence
# that happens to mention a file.  Extensions are excluded explicitly.
#
# A reproducible script IS a converse witness in this project (`window_opt.py`
# is what resolved `ISSUES` #29), so `forensics/*.py` is admitted by name.
_EXT = r"(?:md|lean|py|toml|json|jsonl|go|txt|sh|yml|yaml)\b"
WITNESS = re.compile(r"forensics/[a-z_0-9]+\.py"
                     r"|[A-Z][A-Za-z0-9]*\.(?!" + _EXT + r")[A-Za-z_][A-Za-z0-9_']*"
                     r"|\bminimality open\b|\bconverse open\b"
                     r"|\bnot known to be minimal\b|\bupper bound\b"
                     # `253`: a sentence that names its own lack of a witness IS
                     # supplying the converse — that is what the downgraded form
                     # the gate asks for looks like.  Before this, the gate
                     # flagged its own repairs: `253` rewrote five true
                     # positives into explicitly-scoped form and the count did
                     # not move, because "no declaration witnesses this" reads
                     # as an unwitnessed absolute.  A register's flag count
                     # could then only fall by deleting the discussion, never by
                     # correcting it.  The markers are deliberately specific —
                     # `S27`'s "not in the repo and cannot be repaired" is an
                     # unwitnessed absence and must keep flagging.
                     r"|\bnot a theorem\b|\bnot proved here\b"
                     r"|\bas a reading\b|\bis a reading\b"
                     r"|\bno theorem\b|\bnot certified\b"
                     r"|\bnot formalised\b|\bnot a survey\b")

# Quoted material is not the author's claim.  Two of the three unwitnessed flags
# in the 2026-08-15 triage triggered on text the sentence was *quoting to
# retract* (`S30`'s false identity) or *listing as vocabulary* (this file's own
# IDENTITY wordlist, quoted in CLAIMS.md).  Strip italic-quoted and
# backtick-quoted spans before matching; a trigger surviving outside them is the
# author speaking.
QUOTED = re.compile(r'\*"[^"]*"\*|"[^"]{0,200}"|`[^`]*`')

# `exact` has two senses and this gate hunts only one of them.  `S26`/`S27` are
# about EXACTNESS OF A RESIDUE — "the exact residue, nothing else at all".  But
# "in exact rationals", "the exact value is 7415/12000" and "exactly 3" are
# statements about ARITHMETIC PRECISION, and carry no claim that nothing more is
# needed.  `SESSION 153` triaged four flags on one entry and all four were this
# shape — the first homogeneous false-positive class the gate has produced.
#
# Deliberately narrow: the word is exempted only when it sits directly against
# arithmetic vocabulary or a numeral.  "the exact residue" and "the exact
# characterisation" are untouched, which is what the calibration below checks.
ARITHMETIC_EXACT = re.compile(
    r"\bexact(?:ly)?\s+(?:\S{1,12}\s+){0,4}"
    r"(?:rationals?|decimals?|fractions?|arithmetic|integers?|values?|numerals?)"
    r"|\bexact(?:ly)?\s+\d", re.I)


def unquoted(s):
    return ARITHMETIC_EXACT.sub(" ", QUOTED.sub(" ", s))


# Calibration.  The two entries that bought this gate must still flag, and the
# `153` triage must clear.  Run as part of the self-test; a change that breaks
# either direction is over-fitting.
CALIBRATION = [
    # (sentence, must_flag)
    ("`(mu_T, offAt)` is the exact residue, nothing else at all.", True),
    ("The window computation is not in the repo and cannot be repaired.", True),
    ("A complete characterisation of the class is the only thing that would do.",
     True),
    ("In exact rationals, no floating point.", False),
    # `304`: the shape `302` shipped a wrong sentence in.  Historical — the
    # sentence was corrected at `303`, so this is not a live defect (`S89`).
    ("The cap is reached exactly when every ordinate is a triple.", True),
    ("The exact m = 7 ladder value is 7415/12000, a repeating decimal.", False),
    ("Anything needing the exact value should use the ladder directly.", False),
]


def calibrate():
    print("=== claims_gate calibration (S26/S27 must flag; 153's shape must clear) ===")
    bad = 0
    for s, want in CALIBRATION:
        bare = unquoted(s)
        got = any(re.search(p, bare, re.I) for p in POSITIVE + NEGATIVE + IDENTITY)
        ok = got == want
        bad += not ok
        print(f"  [{'ok ' if ok else 'MISS'}] want={'flag ' if want else 'clear'}"
              f"  got={'flag ' if got else 'clear'}  {s[:62]}")
    print(f"  {len(CALIBRATION) - bad}/{len(CALIBRATION)} as designed.")
    return bad

DOWNGRADE = [
    ("the exact", "a sufficient"), ("exactly the", "a"),
    ("nothing else", "possibly more"), ("nothing more", "possibly more"),
    ("minimal", "sufficient"), ("the unique", "a"), ("the only", "a"),
    ("if and only if", "if"), ("cannot be", "is not known to be"),
    ("exactly when", "when"), ("exactly if", "if"),
    ("precisely when", "when"),
    ("are the same", "are related"), ("is exactly the", "is a"),
    ("not a coincidence", "possibly a coincidence"),
    ("two readings of one", "two readings of related"),
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
        bare = unquoted(s)
        pos = [p for p in POSITIVE if re.search(p, bare, re.I)]
        neg = [p for p in NEGATIVE if re.search(p, bare, re.I)]
        idt = [p for p in IDENTITY if re.search(p, bare, re.I)]
        if not (pos or neg or idt):
            continue
        has_witness = bool(WITNESS.search(s))
        flagged.append((s, pos + neg + idt, has_witness))
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
    # SESSION 155: `154` added `calibrate()` and never called it — a check that
    # exists and does not run, which is exactly the class `148` audited one cycle
    # earlier.  It runs first now, and a broken calibration blocks the report:
    # a gate whose own test set no longer behaves cannot be trusted to grade
    # anything else.
    if calibrate():
        print("\n  \u26a0\ufe0f calibration failed — this gate's verdicts are not trustworthy.")
        return 2
    print()
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
