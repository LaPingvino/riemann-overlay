#!/usr/bin/env python3
"""The absence queue — claims that something does NOT exist, listed for re-check.

**Why this, and not expiry.**  `132` filed claude.ai's design: give every entry a
`valid-as-of: <commit>` and flag it when its cited dependencies change.  `133`
tested that design against the four stale claims this project has actually
found (`120`, `121`, `127`, `128`) and it catches **none** of them:

| stale claim | what invalidated it | cited deps changed? |
|---|---|---|
| "code not in repo" (`λ`-sweep) | `window_opt.py` was **created** | no — it cited nothing |
| "unreachable from our root" (ceiling) | an **import** was added; the declaration never moved | **no** |
| "only capacity certificate came in with zeta-23" | `Capacity.lean` was **created** | no |
| "whether the profile is minimal is not proved" | two theorems were **proved** | no |

All four were invalidated by something being **added**, not by anything cited
changing.  Expiry watches the wrong direction: it asks "did my source move?",
and the defect is "does something now exist that I do not cite?".

⚠️ **SESSION 155 — "Calibration: it flags all four, 4/4" was a claim about a
past run, and nothing re-ran it.**  All four have since been corrected in the
registers, so none of them flags today and the sentence could no longer be
reproduced from the corpus.  That made it a green light with no witness — `148`'s
class (a check that cannot fail) applied to a *calibration claim* rather than to
an exit code.  Worse, `154` changed the settle logic in this very file, and there
was nothing that would have told me if that change had broken the four shapes the
instrument exists to catch.  The calibration is now **embedded and runnable**
below, independent of what the registers currently say.

**So: no detector, and no expiry.  A queue.**  Every claim of *absence* is a
standing obligation to re-check.  This script lists them.  It makes no judgment
about whether any is stale — it cannot — it only ensures none is invisible.
Calibration: it flags all four of the above, 4/4.

Run:  python3 forensics/absence_queue.py [FILE...]   (defaults to the registers)
Exit is always 0: this is a work queue, not an alarm.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, os.pardir)
DEFAULT = ["CLAIMS.md", "ISSUES.md", "LEADS.md", "FAILURES.md", "PRICES.md",
           "E.md"]

# Markers of an assertion that something does not exist / has not been done.
ABSENCE = [
    r"\bnot in the repo\b", r"\bno code\b", r"\bdoes not exist\b",
    r"\bis not proved\b", r"\bnot yet proved\b", r"\bunproved\b",
    r"\bunreachable\b", r"\bnot reachable\b",
    r"\bthe only .{0,60}\b(?:came in with|we can run|we have|exists)\b",
    r"\bnone exists\b", r"\bno such\b", r"\bis empty\b",
    r"\bnothing (?:certified|proved|exists|bounds)\b",
    r"\bnever been (?:run|done|proved|measured|triaged)\b",
    r"\bnot been (?:run|done|proved|measured|triaged)\b",
    # SESSION 194.  `S91`: `FAILURES.md` carried "the instantiation ... remains
    # prose" for many cycles and this queue never listed it, because the
    # patterns above are all ABSENCE-shaped ("X does not exist", "not proved")
    # and that sentence is DEBT-shaped — the project's own vocabulary for an
    # artifact it has not built.  A debt is an absence claim wearing a different
    # coat, and it carries the same standing obligation to re-check.
    #
    # Added against a recorded case one cycle later, per `154`'s discipline and
    # not against a measurement taken this cycle (`S39`).  Measured before
    # adding: `remains prose` 2 hits, `still owed` 2, the built/written shape 0.
    #
    # `\bremains open\b` was MEASURED (1 hit, `PRICES.md`) and deliberately NOT
    # added.  That hit is an open *question* — what the project has yet to
    # decide — not an artifact asserted missing.  Adding it would widen what
    # this queue means rather than fix a miss, and those are different
    # decisions.  The negative control below asserts that choice so it cannot
    # drift in unnoticed.
    r"\bremains? prose\b",
    r"\bstill owed\b",
    r"\bhas not been (?:written|built|formalised|formalized|instantiated)\b",
]

# Already carrying a dated re-check, or explicitly a counterfactual.
#
# ⚠️ SESSION 146: `⚠️` was removed from this list.  It marks **escalations** as
# well as corrections — `LEADS`'s "Odlyzko's tables and LMFDB are unreachable"
# sits under `**⚠️ ESCALATION**`, and a claim announcing itself as an open
# problem was being read as a claim already settled.  A settlement must cite a
# session; a warning sign is not a date.
SETTLED = re.compile(
    r"SESSION \d|kill condition|superseded|corrected|RETRACTED|\bwas graded\b",
    re.I)


# SESSION 154.  `146` triaged this queue's 13 and found **7 were not absence
# claims at all** (54% FP).  The filters were deliberately not added that cycle —
# `S39`'s rule against fitting a filter to the measurement that informs it — and
# are added here, one cycle later, against that recorded triage.
#
# Only the two MECHANICAL shapes are handled.  `146`'s other false positives (a
# past-tense record, a rhetorical question, a schema description, two ordinary
# statements) are not mechanically separable from real absence claims, and
# inventing rules for them is what `S39` warns against.  So this reduces the FP
# rate, it does not eliminate it, and the count still must not be quoted as a
# defect rate without triage (R17).
DIRECTIVE = re.compile(r"^\W*(never|do not|don't|always|cite|use|run|prefer)\b"
                       r"|\bnever cite\b|\bdo not cite\b|\bnever as a\b", re.I)
QUOTED = re.compile(r'\*"[^"]*"\*|"[^"]{0,200}"|`[^`]*`')


def sentences(text):
    for para in text.split("\n\n"):
        flat = " ".join(para.split())
        for s in re.split(r"(?<=[.!?])\s+", flat):
            s = s.strip()
            if s:
                yield s


# The four stale claims this queue was built from (`120`, `121`, `127`, `128`),
# as sentences rather than as a story about them.  Corpus-independent: these must
# flag on their own text, so a change to the settle logic cannot silently blind
# the instrument to the shapes that bought it.
CALIBRATION = [
    ("The window-optimisation table has no code in the repo.", True),
    ("`PairCeiling.ceiling_law256` is unreachable from our root.", True),
    ("The only capacity certificate we can run came in with zeta-23.", True),
    ("Whether the profile is minimal is not proved.", True),
    # KNOWN FALSE POSITIVE, documented and NOT calibrated against — `SESSION 187`.
    # A GRADE DEFINITION is not a claim of absence.  The queue
    # flags `CLAIMS.md`'s description of grade `B` ("a theorem could be stated;
    # none exists yet") as though it asserted something missing.  It defines a
    # category.  A new false-positive class, distinct from the directive and
    # quotation shapes `154` filtered, and left unfiltered on purpose: it is one
    # row, and `S39`'s rule says do not fit a filter to a single instance.
    #
    # It is deliberately absent from `CALIBRATION` below: putting it there with
    # `want=False` would assert behaviour this file does not implement, and the
    # guard would sit permanently red.  A known FP that is left alone belongs in
    # a comment, not in a test that fails.
    # Negative controls: shapes that must NOT be read as claims of absence.
    # SESSION 194 — the debt shape, from `S91`'s own text as it stood before
    # `193` discharged it.  Corpus-independent for the same reason as the four
    # above: the register has since been corrected, so this cannot be recovered
    # from the live files.
    ("The instantiation \u2014 the map from a bandwidth-one certificate to this "
     "program, and the passage from `Finset` to integral \u2014 remains prose.", True),
    ("### What is still owed, by this audit's own criterion", True),
    # Negative control asserting `194`'s SCOPE decision, not just its patterns:
    # an open question is not an absent artifact, and this queue does not claim
    # to list the former.
    ("What remains open is still entirely imported.", False),
    ("**Never as a bound.**  Do not cite a grade-N entry as one.", False),
    ("The ledger reads `Nsc 50.88%` and the row is carried by one axiom.", False),
]


def calibrate():
    """Run the four purchasing claims against the ABSENCE patterns."""
    print("=== absence_queue calibration (the four that bought it must flag) ===")
    bad = 0
    for s, want in CALIBRATION:
        if DIRECTIVE.match(s):
            got = False
        else:
            got = any(re.search(p, QUOTED.sub(" ", s), re.I) for p in ABSENCE)
        ok = got == want
        bad += not ok
        print(f"  [{'ok ' if ok else 'MISS'}] want={'flag ' if want else 'clear'}"
              f"  got={'flag ' if got else 'clear'}  {s[:60]}")
    print(f"  {len(CALIBRATION) - bad}/{len(CALIBRATION)} as designed.")
    return bad


def scan(path):
    """Flag absence claims whose paragraph — or the next one — carries no
    dated re-check.

    ⚠️ **SESSION 154 — this docstring asserted the standing rule backwards, and
    the scan implemented it backwards.**  It said "corrections in this project
    are written *below* the text they correct (the standing rule)".  The standing
    rule is the opposite: **a retraction must appear *above* what it retracts**
    (`CLAIMS.md` line 247, `NIGHT.md` line 157, added after `S25` found a
    retraction banner sitting below the numbers it retracted).  So every
    correctly-placed correction was invisible to this queue and only
    rule-violating ones settled a claim — the instrument was rewarding the
    violation.  `146`'s discharge of the Odlyzko escalation is the example: the
    ✅ block sits above the claim, exactly as required, and the claim kept
    listing.

    Both neighbours now count, with `146`'s heading exclusion applied to each."""
    try:
        text = open(os.path.join(ROOT, path), encoding="utf-8").read()
    except OSError:
        return []
    paras = text.split("\n\n")
    out = []
    for i, para in enumerate(paras):
        nxt = paras[i + 1] if i + 1 < len(paras) else ""
        prv = paras[i - 1] if i > 0 else ""
        if prv.lstrip().startswith("#"):
            prv = ""
        # SESSION 146: a following HEADING is not a correction.  The Odlyzko
        # escalation was settled by `## The slow-convergence recall, tested
        # (SESSION 139)` — the next block, about something else entirely.
        # Adjacency is not aboutness, and the two defects masked each other:
        # neither fix alone surfaces the claim, because `⚠️` in the paragraph
        # and `SESSION` in the heading were each sufficient on their own.
        if nxt.lstrip().startswith("#"):
            nxt = ""
        context = prv + " " + para + " " + nxt
        if SETTLED.search(context):
            continue
        flat = " ".join(para.split())
        for s in re.split(r"(?<=[.!?])\s+", flat):
            s = s.strip()
            if not s or DIRECTIVE.match(s):
                continue
            # A trigger inside quoted material is someone else's claim, or one
            # being retracted — `146` found both shapes here.
            bare = QUOTED.sub(" ", s)
            if any(re.search(p, bare, re.I) for p in ABSENCE):
                out.append(s)
    return out


def main(argv):
    files = argv[1:] or DEFAULT
    total = 0
    for f in files:
        hits = scan(f)
        if hits:
            print(f"\n=== {f} — {len(hits)} absence claim(s) awaiting re-check ===")
            for s in hits:
                print(f"  • {s[:150]}")
            total += len(hits)
    print(f"\n{total} claim(s) of absence carrying no dated re-check.")
    print("Each is an obligation, not a defect. Re-check when its subject "
          "could plausibly have been built since.")
    print()
    bad = calibrate()
    if bad:
        print("  ⚠️ the instrument no longer catches the shapes that bought it.")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
