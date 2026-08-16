#!/usr/bin/env python3
"""Check `LOOP.md`'s `⚠️ READ FIRST` banner against the disk.

**Why this exists.**  The banner is the disk's defence against the cron prompt's
fixed text: the prompt ages while the repo moves (`S33`), and the banner lists
what the prompt gets wrong.  It is therefore the single most load-bearing
anti-staleness document in the project — and until `SESSION 195` it was prose,
stamped "Last checked `SESSION 149`", verified by nobody.

`149` had already learned this shape once on this very block: the `102` version
said "wrong in three ways" above **four** rows and stayed that way for
forty-seven cycles.  The fix then was to stop asserting a total.  This is the
same fix carried further — the rows now assert things a script can run.

**The binding is two-way, and that is the point.**  Each check is anchored to a
substring that must appear in the banner.  If the disk moves so a row becomes
false, the check fails.  If the banner is edited so an anchor disappears, the
check *also* fails — a row cannot be quietly dropped and leave the file green.
`S91`/`S92` are this project's record of a register going stale in the **paid**
direction, which no amount of watching the claim side would have caught.

**What this does not do.**  One row is not mechanically checkable today and is
reported as `UNCHECKED` rather than counted green.  `148` found 9 of 16 scripts
here cannot return a failing exit code at all; a checker that prints a clean
bill over rows it never checked would be that defect wearing a lab coat.

Exit: 0 all checked rows hold · 1 a row failed or an anchor is missing ·
5 the harness itself could not run (`S40`, `S79` — a missing toolchain is not a
finding about the banner).

Run:  python3 forensics/banner_check.py
"""

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the banner.  Exit 5.")
    sys.exit(5)


def read(path):
    try:
        with open(os.path.join(ROOT, path), encoding="utf-8") as fh:
            return fh.read()
    except OSError as exc:
        die_harness(f"cannot read {path}: {exc}")


def lean_sources():
    d = os.path.join(ROOT, "Riemann")
    try:
        names = sorted(n for n in os.listdir(d) if n.endswith(".lean"))
    except OSError as exc:
        die_harness(f"cannot list Riemann/: {exc}")
    return "\n".join(read(os.path.join("Riemann", n)) for n in names)


def declared(src, name):
    return re.search(rf"^(?:theorem|lemma|def)\s+{re.escape(name)}\b",
                     src, re.M) is not None


def ledger():
    """The metric's own line, not a memory of it (`S27`)."""
    try:
        out = subprocess.run(["go", "run", "tools/proportion.go"], cwd=ROOT,
                             capture_output=True, text=True, timeout=900)
    except OSError as exc:
        die_harness(f"cannot run proportion.go: {exc}")
    except subprocess.TimeoutExpired:
        die_harness("proportion.go timed out")
    if out.returncode != 0:
        die_harness(f"proportion.go exited {out.returncode}:\n{out.stderr[-800:]}")
    return out.stdout


def provenance():
    try:
        out = subprocess.run([sys.executable, "forensics/provenance_lint.py"],
                             cwd=ROOT, capture_output=True, text=True, timeout=600)
    except OSError as exc:
        die_harness(f"cannot run provenance_lint.py: {exc}")
    except subprocess.TimeoutExpired:
        die_harness("provenance_lint.py timed out")
    return out.stdout


# ---------------------------------------------------------------- the checks
#
# `anchor` is a substring that must be present in the banner.  It is not
# decoration: a missing anchor is a FAILURE, so a row cannot be deleted or
# reworded past recognition without this file going red.

def check_nsc(env):
    m = re.search(r"Nsc:\s*([0-9.]+)%", env["ledger"])
    if not m:
        return False, "could not find the `Nsc` figure in proportion.go's output"
    val = float(m.group(1))
    if val == 0.0:
        return False, "the ledger really does read `Nsc 0.00%` — the banner row is wrong"
    if not declared(env["lean"], "certified_nsc_unconditional"):
        return False, "`certified_nsc_unconditional` is not declared; the row cites a ghost"
    if f"{val:.2f}" not in env["banner"]:
        return False, f"ledger reads `Nsc {val:.2f}%`, which the banner does not state"
    return True, f"ledger `Nsc {val:.2f}%`, `certified_nsc_unconditional` declared"


def check_binding(env):
    m = re.search(r"binding:\s*(\S+)", env["ledger"])
    if not m:
        return False, "could not find the binding field in proportion.go's output"
    if "Fujii" in m.group(1):
        return False, "the binding constraint really is Fujii — the banner row is wrong"
    return True, f"binding is `{m.group(1)}`, not Fujii"


def check_minimality(env):
    missing = [n for n in ("profile_not_minimal", "profile_minimal_among_local")
               if not declared(env["lean"], n)]
    if missing:
        return False, "not declared: " + ", ".join(missing)
    return True, "`profile_not_minimal` and `profile_minimal_among_local` both declared"


def check_queue123(env):
    if "## W32" not in env["failures"]:
        return False, "`FAILURES.md` has no `## W32` section; the row cites a ghost"
    ok, why = check_minimality(env)
    if not ok:
        return False, why
    return True, "`FAILURES.md` W32 section present; `075`/`077` theorems declared"


def check_queue4(env):
    m = re.search(r"tier GRH\s*:\s*(\d+)/(\d+)", env["prov"])
    if not m:
        return False, "`provenance_lint` no longer prints a `tier GRH` line"
    got = f"{m.group(1)}/{m.group(2)}"
    if m.group(1) != "0":
        return False, f"the GRH tier is no longer empty: `tier GRH: {got}`"
    if got not in env["banner"]:
        return False, f"`provenance_lint` prints `tier GRH: {got}`, which the banner does not state"
    return True, f"`provenance_lint` prints `tier GRH: {got}`, as the row says"


ROWS = [
    ("ledger Nsc 0.00%", "`ledger Nsc 0.00%`", check_nsc),
    ("binding constraint = Fujii", "binding constraint = Fujii", check_binding),
    ("profile minimality", "Minimality of the profile is NOT proved", check_minimality),
    ("queue items 1, 2, 3", "queue items 1, 2, 3", check_queue123),
    ("queue item 4 (W19 / GRH tier)", "queue item 4", check_queue4),
    ("RECENT's profile clause", "`RECENT`'s", check_minimality),
]

# Rows whose content is a claim about a PAST MEASUREMENT rather than about
# current disk state.  Not checkable by rerunning anything, and deliberately not
# faked into a check: `148`'s finding is that a green light over an unchecked
# row is the defect, not the cure.
UNCHECKED = [
    ("queue item 5", "queue item 5",
     "cites `148`'s measurement (9 of 16 scripts cannot return a failing exit "
     "code). A claim about a past audit, not about current state; re-measuring "
     "it is a cycle's work, not a guard's."),
]


def banner_text(loop):
    m = re.search(r"^> ## ⚠️ READ FIRST.*?(?=\n\n)", loop, re.S | re.M)
    return m.group(0) if m else None


def main():
    loop = read("LOOP.md")
    banner = banner_text(loop)
    if banner is None:
        print("FAILURE: LOOP.md has no `⚠️ READ FIRST` banner block.")
        print("That block is the disk's defence against the cron prompt; its")
        print("absence is a finding, not a pass.")
        return 1

    env = {
        "banner": banner,
        "loop": loop,
        "lean": lean_sources(),
        "failures": read("FAILURES.md"),
        "ledger": ledger(),
        "prov": provenance(),
    }

    print("=== LOOP.md ⚠️ READ FIRST — each row against the disk ===")
    bad = 0
    for label, anchor, fn in ROWS:
        if anchor not in banner:
            print(f"  [FAIL] {label:32s} anchor absent from the banner: {anchor!r}")
            bad += 1
            continue
        ok, why = fn(env)
        print(f"  [{'ok ' if ok else 'FAIL'}] {label:32s} {why}")
        if not ok:
            bad += 1

    for label, anchor, why in UNCHECKED:
        mark = "----" if anchor in banner else "FAIL"
        if mark == "FAIL":
            print(f"  [FAIL] {label:32s} anchor absent from the banner: {anchor!r}")
            bad += 1
        else:
            print(f"  [----] {label:32s} UNCHECKED — {why}")

    stamp = re.search(r"Last checked\s+`?SESSION (\d+)`?", banner)
    print()
    print(f"{len(ROWS)} row(s) checked, {len(UNCHECKED)} deliberately unchecked, "
          f"{bad} failing.")
    if stamp:
        print(f"Banner stamped `SESSION {stamp.group(1)}`.  The stamp is a date, "
              f"not a witness — the rows above are the witness.")
    if bad:
        print("A failing row means the banner and the disk disagree.  Fix the")
        print("banner AT THE LOCATION of the stale row; do not fix this script.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
