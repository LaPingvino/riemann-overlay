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
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
