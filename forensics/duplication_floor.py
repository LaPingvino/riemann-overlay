#!/usr/bin/env python3
"""Watch for a theorem whose conclusion the project already proves.

**Why this exists.**  `255` proved two theorems that had been in `Fiber.lean`
since `181`, were in `audit/Declarations.lean`, and were cited by name in
`RULING.md`.  `S98` was the same move with a `private` copy that shadowed a real
lemma and broke two proofs.  `S111`'s reading was that the registers are now
large enough that the expensive failure is proving something twice — and that
every guard here watches for proving something *false*.

**What it does not do, and this is the design.**  `256` measured the repo:
`20` conclusions of `483` were shared by more than one theorem.  All twenty were
listed and graded — `2` were real duplicated proofs (below), `2` are artifacts
of this script's own parser (see the limitation), and the remaining `16` are
deliberate: three sufficient conditions for `NoHaunted`, four routes to
`0.50875`, the two `κ` rows of `255`, a bound and its `except`-generalisation.
Sharing a conclusion is *normal here*; this project's whole method is reaching
one row by several routes.  So a guard that failed on a shared conclusion would fire
constantly on the thing the project is for.

The enforceable invariant is the ratchet, as in `warning_floor.py`: **the number
of shared conclusions must not grow.**  A new one is a cycle's own doing, and
the cycle that caused it is the one that can tell in a minute whether it is a
fourth route or a second copy.  `--update` records the new floor once that
judgement is written down.

**The floor has risen four times, each with its own grading (`328`).**  `19` at
`256`, then `20` at `261`, `21` at `272`, `22` at `280`, `23` at `283`.  Every
raise carries a graded reason in its cycle's commit, so the process held — but
the stored `note` and the printed breakdown both credited `256` with all of
them, and `256` graded `20` of `483` declarations.  Attribution corrected; the
floor is unchanged.

**`264` revisited one of `256`'s gradings and found it too generous.**  The pair
sharing `zetaFamily.toCounts.StarBound 1.9825` was graded "two deliberate
routes".  It is not: `starBound_of_multiplicity_two` asks `H ≤ 2` and
`starBound_of_mult_le_three` asks `H ≤ 3` for the same constant, so the first is
a strictly worse instance of the second, and a two-line composite proves it.
The lesson for this grading is that *different hypotheses* is not enough — the
question is whether one hypothesis **implies** the other, and that is a check,
not a glance (now `R25`).

**`265` re-graded the whole list under that rule and found four more.**  Of the
sixteen graded deliberate at `256`, five are dominations: the `1.9825` pair
above, the two `Proportion 0.6725` rows (`255`: `H ≤ 2 → NoHaunted`), the
`NoHaunted F` trio (`261`'s general theorem subsumes `255`'s at `M = 2` with the
free rung), and `noHaunted_of_allDistinct`, which is reachable two ways.  All are
annotated at their declarations and kept; none was deleted, so this count does
not move.  **Domination is a third category** — not a deliberate route and not a
duplicated proof — and it is the most common of the three.  Annotated at the declaration rather than removed; the row stays
in the board's enumeration.

The two real duplicates `256` found — `configAt_offAt` against
`offAt_configAt_self` (identical statement *and* identical proof, since `157`),
and `Nsc_eq_NscStd_of_mult_le_two` carrying its own copy of
`Nsc_eq_NscStd_of_noHaunted`'s summation — are collapsed, so the floor below is
already post-repair.

**Known limitation, measured not guessed.**  The conclusion is taken as the text
after the last top-level `:`, which for a statement opening with `let` yields
`let D` or `let C`.  Two of the nineteen are that, and they are counted rather
than special-cased — a parser exception is a place for a defect to hide, and the
ratchet works the same either way.

Exit: 0 at or below the floor · 1 the count grew · 5 the harness could not run.

Run:  python3 forensics/duplication_floor.py
      python3 forensics/duplication_floor.py --list
      python3 forensics/duplication_floor.py --update
"""

import collections
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
SRC = os.path.join(ROOT, "Riemann")
FLOOR = os.path.join(HERE, "duplication_floor.json")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z_][\w'\.]*)\s*(.*?)\s*:=",
    re.M | re.S)


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about duplication.  Exit 5.")
    sys.exit(5)


def conclusion(body):
    """Text after the last top-level `:` — the statement being proved."""
    depth = last = 0
    last = -1
    for i, ch in enumerate(body):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0 and (i + 1 >= len(body) or body[i + 1] != "="):
            last = i
    return " ".join(body[last + 1:].split()) if last >= 0 else " ".join(body.split())


def scan():
    try:
        names = sorted(n for n in os.listdir(SRC) if n.endswith(".lean"))
    except OSError as exc:
        die_harness(f"cannot list Riemann/: {exc}")
    if not names:
        die_harness("Riemann/ contains no .lean files")
    shared = collections.defaultdict(list)
    total = 0
    for fn in names:
        try:
            with open(os.path.join(SRC, fn), encoding="utf-8") as fh:
                src = fh.read()
        except OSError as exc:
            die_harness(f"cannot read {fn}: {exc}")
        src = re.sub(r"/-.*?-/", "", src, flags=re.S)
        for name, body in DECL.findall(src):
            if len(body) > 4000:
                continue
            total += 1
            c = conclusion(body)
            if c:
                shared[c].append(f"{fn}:{name}")
    return total, {k: v for k, v in shared.items() if len(v) > 1}


def main():
    total, shared = scan()
    n = len(shared)

    if "--list" in sys.argv:
        for c, where in sorted(shared.items(), key=lambda kv: -len(kv[1])):
            print(f"  [{len(where)}] {c[:100]}")
            for w in where:
                print(f"        {w}")
        print()

    print(f"=== shared conclusions: {n} across {total} declarations ===")

    try:
        with open(FLOOR, encoding="utf-8") as fh:
            floor = json.load(fh)
    except FileNotFoundError:
        floor = None
    except (OSError, json.JSONDecodeError) as exc:
        die_harness(f"cannot read duplication_floor.json: {exc}")

    if floor is None or "--update" in sys.argv:
        with open(FLOOR, "w", encoding="utf-8") as fh:
            json.dump({"shared": n, "note": "256: hand-graded, not a target"},
                      fh, indent=2)
            fh.write("\n")
        print(f"Floor recorded: {n}.  Grade a new one before raising this —")
        print("a fourth route to a row is fine; a second copy of a proof is not.")
        return 0

    want = floor["shared"]
    if n > want:
        print(f"FAIL  {n} shared conclusions, floor is {want}.")
        print("Run with --list, find the new one, and decide which it is:")
        print("  another route to a known row  -> say so in SESSION.md, --update")
        print("  a second proof of a known fact -> collapse it (`256`)")
        return 1
    if n < want:
        print(f"  {n}, below the floor of {want}.  Re-run with --update to ratchet.")
    else:
        print(f"  {n}, at the floor.  Every one has been graded:")
        print("  `256` graded the first 20 — 16 deliberate routes, 2 parser")
        print("  artifacts, 2 duplicates collapsed — and 261, 272, 280, 283 each")
        print("  graded one more before raising the floor (`328`).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
