#!/usr/bin/env python3
"""Run `claims_gate` over the newest `SESSION.md` entry, as a guard.

**Why this exists.**  `251` shipped a `SESSION.md` entry with a `claims_gate`
flag unresolved, because the gate and `git commit` were in one shell call and
the commit ran before the exit code could stop it.  `251d` diagnosed it and
wrote the rule — *"the gate and the commit never go in one call, or the gate's
exit code is the `&&` condition"*.  `269`–`276` honoured it.  `277` broke it the
same way, with a newline where the `&&` should have been, and `S113` recorded
the verdict: **a rule that depends on remembering a shell operator is a habit,
not a rule.**

This is the enforceable form.  It runs in the guard roster like every other
check, so a flagged entry cannot survive a cycle unnoticed — the cycle that
wrote it sees red if the guard runs after the entry is written, and the next
cycle sees red if it does not.  Either way the window is one cycle, not
however long until someone re-reads the prose.

**What "the newest entry" means.**  The text from the last `^## ` heading to the
end of the file.  Recent entries are `## `-headed and sub-sections are `### `,
so the boundary is unambiguous at the tail.  Older parts of the file use
`# SESSION NNN` with `## ` sub-sections, so this heuristic would carve those
wrongly — it is deliberately only applied to the newest entry, which is the only
one a cycle can still fix, and the only one this guard claims anything about.

**`SESSION 318` widened it, because it had closed one door of two.**  `318` ran
the roster and `git commit` in a single `Bash` call; `citation_check` exited `1`
and the commit ran anyway, with the entry asserting *"fourteen guards green"*.
This file gated `claims_gate` over the newest entry and nothing else, so the rest
of the roster was still only as good as the shell operator between it and the
commit — which is the thing `S113` says a rule cannot rest on.  `S122`.

So it now runs the whole roster.  One call to remember instead of fifteen, which
is the entire point: `55s`, of which `banner_check` is `39s` and `warning_floor`
`13s` because both invoke `lake`.  A cycle already pays that for `lake build`, so
the widening costs nothing it was not spending.

**One roster member is quieter than it looks, and `319` measured it.**  Bare
`claims_gate` with no file argument lints **stdin**; called with stdin closed —
which is how a roster loop calls it — it scans zero sentences and exits `0`.  Its
`CALIBRATION` still runs, so the line is not inert, but *"claims_gate green"*
has meant *"the calibration passed"* and not *"the registers are clean"*.  That
is `S49` reintroduced from the caller's side.  It is listed below with that
scope written down.  The corpus scan stays a triage tool rather than a gate:
`304` measured `194` flagged sentences across the registers, so demanding a clean
corpus would leave this red forever, which is `S89`.

**Every member controlled, `320`.**  `319` found one roster line reporting on an
empty scan, so `320` ran a positive control on each: perturb the thing the guard
watches, confirm red, restore, confirm green.

* fired on the perturbation — `board` (recorded constant), `window_opt` (a
  recorded digit), `vendor_check` (a vendored byte), `lawN256_shape` (the table's
  scale), `statement_index` and `process_index` (a fabricated row),
  `banner_check` (the banner's ledger figure);
* fired from their own in-process controls, with both polarities —
  `provenance_lint` (`5/5` replays, four that must block and one that must pass),
  `absence_queue` (`9/9`), `citation_check` (`4/4`);
* fired live in earlier cycles — `duplication_floor` (`303`, `316`);
* **`surprises` fires only on total schema collapse.**  Its one failure path is
  `if not rs`: it is a *tally*, and its green light means the table still parses,
  not that the register is sound.  Its own docstring never claimed otherwise —
  putting it in a guard roster was the caller's doing, as with `claims_gate`
  (`S123`), so it is labelled here rather than moved.  `S124`.
* **`warning_floor`, controlled at `327`** — `320` left it untested because its
  control needs a real Lean warning.  `327` appended a theorem with an unused
  binder to a leaf module: `55 warnings, floor is 54 — this cycle added 1`,
  exit `1`; reverted, rebuilt, exit `0`.  **All fourteen were controlled at `327`.**
* **`board --cones`, added at `340` and controlled by the event that motivated
  it.**  `337`'s axiom discharge moved ten of thirty-two recorded cones and this
  gate said `14/14 green` for three cycles, because the cone check is `board.py`'s
  opt-in mode and the roster ran it bare.  Running it at `340` printed ten
  `[WRONG]` rows and exited `1`; recording the measured sets took it to `32/32`
  and exit `0`.  That is a live red and a live green, on the same guard, in one
  cycle.

**Shown to go red, because `S60` says a guard that has never flagged is
unproven.**  `319` appended a fabricated row to `statement_index.tsv` and ran
this: `[FAIL] statement_index`, `13/14 green` (the roster was fourteen then and is fifteen since `340`), exit `1` — while `--entry-only`
still exited `0`, which is what proves the roster half is doing the work.  The
row was removed and the index re-verified afterwards.

Exit: 0 the newest entry is clean and the roster is green · 1 something is red ·
5 the harness could not run (`S40`, `S79`).

Run:  python3 forensics/session_gate.py
      python3 forensics/session_gate.py --show   (print the entry it checked)
      python3 forensics/session_gate.py --entry-only   (skip the roster)
"""

import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
SESSION = os.path.join(ROOT, "SESSION.md")
GATE = os.path.join(HERE, "claims_gate.py")


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the entry.  Exit 5.")
    sys.exit(5)


def newest_entry():
    try:
        with open(SESSION, encoding="utf-8") as fh:
            text = fh.read()
    except OSError as exc:
        die_harness(f"cannot read SESSION.md: {exc}")
    starts = [m.start() for m in re.finditer(r"^## ", text, re.M)]
    if not starts:
        die_harness("SESSION.md has no `## ` heading; the entry boundary is "
                    "not where this guard thinks it is")
    return text[starts[-1]:]


def main():
    if not os.path.exists(GATE):
        die_harness("forensics/claims_gate.py is missing")

    entry = newest_entry()
    title = entry.splitlines()[0][3:].strip()

    if "--show" in sys.argv:
        print(entry)
        return 0

    tmp = None
    try:
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False,
                                         encoding="utf-8") as fh:
            fh.write(entry)
            tmp = fh.name
        try:
            out = subprocess.run([sys.executable, GATE, tmp], cwd=ROOT,
                                 capture_output=True, text=True, timeout=600)
        except OSError as exc:
            die_harness(f"cannot run claims_gate.py: {exc}")
        except subprocess.TimeoutExpired:
            die_harness("claims_gate.py timed out")
    finally:
        if tmp and os.path.exists(tmp):
            os.unlink(tmp)

    print("=== newest SESSION.md entry, gated ===")
    print(f"  entry: {title[:70]}")

    # `claims_gate` exits 1 when it flags.  `259` recorded that its closing
    # advice line prints only on failure, so either signal works; the exit code
    # is the one that cannot be misread, which is the whole point of `S113`.
    if out.returncode == 5:
        die_harness("claims_gate.py reported its own harness failure")
    if out.returncode != 0:
        print("  [FAIL] the entry carries an unresolved claims_gate flag:")
        for line in out.stdout.splitlines():
            if "NO CONVERSE" in line or "downgrade ->" in line:
                print("   " + line.strip()[:150])
        print()
        print("  Fix the sentence, or supply the converse witness.  `S113`: this")
        print("  guard exists because the gate-then-commit rule was a habit.")
        return 1

    print("  [ok ] no unresolved flags")

    if "--entry-only" in sys.argv:
        return 0
    return roster()


# The guards, self excluded.  Instruments are NOT here — `prose_numerals`,
# `dependency_profile` and `equiv_check` exit `0` by design or cost minutes, and
# a roster member that cannot fail is worse than one outside it that can (`S50`).
ROSTER = [
    ("provenance_lint", "the flagship"),
    ("claims_gate", "CALIBRATION only — bare, it lints stdin and scans nothing"),
    ("absence_queue", "claims of absence awaiting re-check"),
    ("board", "the ζ-level rows, their constants and their binders"),
    ("surprises", "a TALLY — its one failure path is total schema collapse"),
    ("window_opt", "the seven digits"),
    ("banner_check", "LOOP.md's ⚠️ block against the disk — invokes lake"),
    ("vendor_check", "vendor/zeta23 against the pin"),
    ("warning_floor", "the build's warning count — invokes lake"),
    ("duplication_floor", "shared conclusions"),
    ("lawN256_shape", "the vendored enclosure table"),
    ("statement_index", "index freshness"),
    ("process_index", "index freshness"),
    ("citation_check", "declaration names cited in docstrings"),
    # `340`: added, with a witness for why.  `board.py`'s cone check is opt-in
    # (`--cones`), so `337`'s axiom discharge moved ten recorded cones and nothing
    # in this roster noticed for three cycles while it reported `14/14` green.
    # The reason cone-checking was opt-in — "running lake from a linter would make
    # the cheap check expensive" — does not apply to this gate, which already runs
    # two lake-invoking guards and is called once before a commit rather than on
    # every edit.
    ("board --cones", "the same rows' cones, asked of the kernel — invokes lake"),
]


def roster():
    print()
    print("=== the roster, in this call rather than beside the commit (`S122`) ===")
    bad = harness = 0
    for name, why in ROSTER:
        base, *args = name.split()
        script = os.path.join(HERE, base + ".py")
        if not os.path.exists(script):
            die_harness(f"roster member {base}.py is missing")
        try:
            r = subprocess.run([sys.executable, script, *args], cwd=ROOT,
                               stdin=subprocess.DEVNULL, capture_output=True,
                               text=True, timeout=1800).returncode
        except OSError as exc:
            die_harness(f"cannot run {name}.py: {exc}")
        except subprocess.TimeoutExpired:
            die_harness(f"{name}.py timed out")
        tag = "ok  " if r == 0 else ("HARNESS" if r == 5 else "FAIL")
        if r == 5:
            harness += 1
        elif r != 0:
            bad += 1
        print(f"  [{tag:7s}] {name:20s} {why}")
    print(f"  {len(ROSTER) - bad - harness}/{len(ROSTER)} green")
    if harness:
        print("  A harness failure is not a verdict.  Check `lake` is on PATH.")
        return 5
    if bad:
        print("  Red.  `S113`/`S122`: this is the call that is supposed to stop")
        print("  the commit, so do not commit until it is green.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
