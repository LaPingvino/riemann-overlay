#!/usr/bin/env python3
"""The overclaim count in Lean docstrings, ratcheted — it may fall, never rise.

**Why this exists, and it is a measurement rather than a hunch.**  `342` asked
whether `CLAIMS.md`'s recorded *"`Fiber.lean` (36 flags) … untriaged"* was still
true.  It was not: `108`, with `205` across `Riemann/*.lean`.  The growth is the
decomposition arc `292`–`341`, which is my own prose.

`S131` is why that surface grows and no other does.  `session_gate` runs
`claims_gate` on the newest `SESSION.md` entry, so every cycle's prose *about* the
work is gated; its roster entry for `claims_gate` is CALIBRATION-only, because a
bare invocation lints stdin (`S123`).  **Nothing was checking the docstrings** —
the text a reader of the Lean actually meets.

**Why a floor and not a triage.**  `108` flags is several cycles of grading, and
`342` found the population to be mostly false positives of documented shapes — a
docstring heading an `iff`, an accurate `never`, a cast called "the same fact".
Rewording those to please the gate would be fitting the prose to the instrument,
which `S39` rules out.  What is worth preventing is *growth*: a flag added
tomorrow is one nobody has read.

This is `warning_floor` and `duplication_floor`'s pattern, and those two are the
precedent for it: bound an untriaged population, forbid it growing, and grade it
down when a cycle has reason to touch the file anyway.

**Per file, not one total** — a total lets a drop in one file mask a rise in
another, and the rise is the thing being watched.

**It shares `claims_gate`'s vocabulary rather than copying it.**  `POSITIVE`,
`NEGATIVE`, `IDENTITY`, `WITNESS`, `sentences` and `unquoted` are imported, so a
change to the wordlist moves these numbers and the floor has to be re-graded —
which is correct, since the population is defined by that wordlist.  It also runs
`claims_gate`'s own `calibrate()` first: a floor computed with a broken vocabulary
is not a floor, and that is a harness failure rather than a finding.

**Control, run live at `343`.**  Appended to `Riemann/Transfer.lean` (the one file
at `0`) a docstring reading *"This is the only route that can ever work."* —
unwitnessed, unscoped.  `Transfer.lean 1 > 0` and exit `1`.  Removed, rebuilt,
exit `0`.  `S60`: a guard that has never flagged is unproven.

A floor may be **lowered** by fixing or grading flags and running `--update`; the
report says when a ratchet is available.  Raising it needs `--update` too, and a
raise belongs in `SESSION.md` with the reason, exactly as `warning_floor`'s does.

Exit: 0 every file at or below its floor · 1 some file above · 5 harness failure.

Run:  python3 forensics/overclaim_floor.py
      python3 forensics/overclaim_floor.py --update
      python3 forensics/overclaim_floor.py --list Riemann/Fiber.lean
"""

import glob
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
STORE = os.path.join(HERE, "overclaim_floor.json")

sys.path.insert(0, HERE)


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the docstrings.  Exit 5.")
    sys.exit(5)


try:
    import claims_gate as cg
except Exception as exc:                                  # pragma: no cover
    die_harness(f"cannot import claims_gate: {exc}")

for name in ("POSITIVE", "NEGATIVE", "IDENTITY", "WITNESS", "sentences",
             "unquoted", "calibrate"):
    if not hasattr(cg, name):
        die_harness(f"claims_gate has no `{name}` — its interface moved, and "
                    f"this floor is computed from it")


def triggered(s):
    """`claims_gate`'s own test, minus the printing."""
    import re
    bare = cg.unquoted(s)
    return any(re.search(p, bare, re.I)
               for p in (*cg.POSITIVE, *cg.NEGATIVE, *cg.IDENTITY))


def flags(text):
    return [s for s in cg.sentences(text)
            if triggered(s) and not cg.WITNESS.search(s)]


def measure():
    out = {}
    paths = sorted(glob.glob(os.path.join(ROOT, "Riemann", "*.lean")))
    if not paths:
        die_harness("no Riemann/*.lean files found")
    for p in paths:
        try:
            with open(p, encoding="utf-8") as fh:
                text = fh.read()
        except OSError as exc:
            die_harness(f"cannot read {p}: {exc}")
        out[os.path.relpath(p, ROOT)] = len(flags(text))
    return out


def load():
    try:
        with open(STORE, encoding="utf-8") as fh:
            return json.load(fh)
    except FileNotFoundError:
        return None
    except (OSError, ValueError) as exc:
        die_harness(f"cannot read {STORE}: {exc}")


def main(argv):
    if cg.calibrate():
        die_harness("claims_gate's calibration failed, so the vocabulary this "
                    "floor counts with is not trustworthy")

    if "--list" in argv:
        rest = [a for a in argv[1:] if a != "--list"]
        if not rest:
            print("usage: --list PATH [PATH …]")
            return 0
        for p in rest:
            with open(p, encoding="utf-8") as fh:
                fs = flags(fh.read())
            print(f"=== {p}: {len(fs)} unwitnessed ===")
            for s in fs:
                print(f"  {s[:150]}")
        return 0

    live = measure()
    total = sum(live.values())

    if "--update" in argv:
        with open(STORE, "w", encoding="utf-8") as fh:
            json.dump({"files": live, "total": total}, fh,
                      indent=2, sort_keys=True)
            fh.write("\n")
        print(f"wrote the floor: {total} across {len(live)} files")
        return 0

    rec = load()
    if rec is None:
        print("FAIL  no floor on disk; run --update once and record why")
        return 1
    floors = rec.get("files", {})

    print(f"=== overclaim flags in Lean docstrings: {total} "
          f"(floor {rec.get('total', '?')}) ===")
    over, under = [], []
    for f in sorted(set(live) | set(floors)):
        n, fl = live.get(f), floors.get(f)
        if fl is None:
            over.append((f, n, "not on the floor — a new file"))
        elif n is None:
            under.append((f, 0, fl))
        elif n > fl:
            over.append((f, n, f"floor {fl}, this cycle added {n - fl}"))
        elif n < fl:
            under.append((f, n, fl))

    for f in sorted(live):
        mark = "OVER" if any(o[0] == f for o in over) else \
               ("down" if any(u[0] == f for u in under) else "ok  ")
        print(f"  [{mark}] {live[f]:>4}  {f}")

    if under:
        print()
        for f, n, fl in under:
            print(f"  ratchet available: {f} is {n}, floor {fl}")
        print("  Run --update to lock it in, and say in SESSION.md what moved.")

    if over:
        print()
        for f, n, why in over:
            print(f"  [OVER] {f}: {why}")
        print()
        print("  A new unwitnessed overclaim in a docstring is prose nobody has")
        print("  read.  Fix it, scope it, give it a witness — or --update the")
        print("  floor and justify the raise in SESSION.md, as `warning_floor`")
        print("  requires.  `S131`: this surface grew from 36 to 108 unwatched.")
        return 1
    print("  every file at or below its floor.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
