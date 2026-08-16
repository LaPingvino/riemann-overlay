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

Exit: 0 the newest entry is clean · 1 it carries an unresolved flag ·
5 the harness could not run (`S40`, `S79`).

Run:  python3 forensics/session_gate.py
      python3 forensics/session_gate.py --show   (print the entry it checked)
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
    return 0


if __name__ == "__main__":
    sys.exit(main())
