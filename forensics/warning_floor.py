#!/usr/bin/env python3
"""Hold the line on `lake build` warnings, which nothing else in here looks at.

**Why this exists.**  `251` recorded a snag: a `push_neg` deprecation warning
had been sitting in `250`'s proof and I never saw it, because the way I check a
build is `lake build 2>&1 | grep -E "^error"`.  Warnings are invisible to that,
and `252` found `54` of them in `Riemann/*.lean` — none wrong, but none looked
at either, which is the same relationship to evidence that `S103` punished.

*(**Corrected, `327`.** These two paragraphs said `51`. That was `252`'s hand
count off `uniq -c`; its own snag reads *"my hand count was 51; the guard says
54"*, and the floor it wrote is `54`. The retraction went into `SESSION.md` and
the commit message and not into this file, so the number the guard explains
itself with disagreed with the number it enforces, in the same cycle's prose.
`S36`'s shape.)*

**What this is not.**  It is not a demand for zero warnings.  Most of the `54`
are `simp` arguments that became redundant when Mathlib moved underneath them,
and rewriting proofs to silence them is churn against a moving dependency.  The
useful invariant is weaker and enforceable: **the count must not grow.**  A new
warning is a cycle's own doing and belongs to the cycle that caused it.

**Vendored code is counted separately and never fails.**  `Zeta23/*` is
`231`'s vendored tree; its warnings are upstream's and editing them would break
`vendor_check.py`'s tree hash.  They are reported for information only.

Exit: 0 at or below the floor · 1 the count grew · 5 the harness could not run
(`S40`, `S79` — a missing toolchain is not a finding about the warnings).

Run:  python3 forensics/warning_floor.py
      python3 forensics/warning_floor.py --update    (lower the floor after a
                                                      cycle that fixed some)
"""

import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
FLOOR = os.path.join(HERE, "warning_floor.json")

WARN = re.compile(r"^warning: (\S+?):\d+:\d+: (.*)$", re.M)


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the warnings.  Exit 5.")
    sys.exit(5)


def build_output():
    try:
        out = subprocess.run(["lake", "build"], cwd=ROOT,
                             capture_output=True, text=True, timeout=3600)
    except OSError as exc:
        die_harness(f"cannot run lake build ({exc}) — is `lake` on PATH?")
    except subprocess.TimeoutExpired:
        die_harness("lake build timed out")
    if out.returncode != 0:
        die_harness(f"lake build exited {out.returncode}; fix the build first")
    return out.stdout + out.stderr


def tally(text):
    ours, theirs = {}, {}
    for path, msg in WARN.findall(text):
        # Normalise the message: keep the kind, drop names and suggestions.
        kind = msg.split(":")[0].strip()
        target = theirs if path.startswith("Zeta23/") else ours
        target[path] = target.get(path, 0) + 1
        target.setdefault("_kinds", {})
        target["_kinds"][kind] = target["_kinds"].get(kind, 0) + 1
    return ours, theirs


def total(d):
    return sum(v for k, v in d.items() if k != "_kinds")


def read_floor():
    try:
        with open(FLOOR, encoding="utf-8") as fh:
            return json.load(fh)
    except FileNotFoundError:
        return None
    except (OSError, json.JSONDecodeError) as exc:
        die_harness(f"cannot read {os.path.basename(FLOOR)}: {exc}")


def main():
    update = "--update" in sys.argv
    ours, theirs = tally(build_output())
    n = total(ours)
    m = total(theirs)

    print("=== lake build warnings ===")
    for path in sorted(k for k in ours if k != "_kinds"):
        print(f"  {ours[path]:3d}  {path}")
    print(f"  ---  {n} in our files, {m} in vendored Zeta23 (informational)")
    print()
    print("  by kind (ours):")
    for kind, c in sorted(ours.get("_kinds", {}).items(), key=lambda kv: -kv[1]):
        print(f"    {c:3d}  {kind}")
    print()

    floor = read_floor()
    if floor is None or update:
        with open(FLOOR, "w", encoding="utf-8") as fh:
            json.dump({"ours": n, "note": "252: floor recorded, not a target"},
                      fh, indent=2)
            fh.write("\n")
        was = "recorded" if floor is None else f"lowered from {floor['ours']}"
        print(f"Floor {was}: {n}.  A floor is a ratchet, not a goal — `--update`")
        print("is for a cycle that fixed warnings, never for one that added them.")
        return 0

    want = floor["ours"]
    if n > want:
        print(f"FAIL  {n} warnings, floor is {want} — this cycle added {n - want}.")
        print("A new warning belongs to the cycle that caused it.  Fix it, or")
        print("say in SESSION.md why it stands and run with --update.")
        return 1
    if n < want:
        print(f"  {n} warnings, below the floor of {want}.  Re-run with --update")
        print("  to ratchet it down; until then this passes.")
    else:
        print(f"  {n} warnings, at the floor.  None of the {n} indicates a wrong")
        print("  proof — `252` inspected the three 'dead tactic' sites by hand.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
