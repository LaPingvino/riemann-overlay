#!/usr/bin/env python3
"""Verify the vendored zeta-23 against its recorded provenance.

`ISSUES` `#28(a)` had two halves.  The first pinned the dependency to an exact
commit; the second — *"no vendored copy"* — stayed open for many cycles because
a pin is a promise about someone else's disk.  `SESSION 231` vendored it under
Joop's ruling.  This checks the vendoring is still real.

**Three things can rot, and this checks all three.**

1. The bytes.  `vendor/zeta23` is hashed and compared to `vendor/PROVENANCE.md`'s
   recorded tree hash — the same `sha256` over sorted paths and file digests.
2. The lakefile.  `[[require]] name = "zeta23"` must carry `path`, not `git`.
3. The manifest.  Its `zeta23` entry must be `type: "path"`.

Three, because `231` learned that (2) alone does nothing: with the manifest
still saying `git`, lake re-cloned zeta-23 from GitHub and built from the clone
while the build stayed green.  A vendoring that only edits the lakefile is
indistinguishable from no vendoring at all except by looking for the clone.

Exit: 0 all three hold · 1 one failed · 5 the harness could not run
(`S40`, `S79`).

Run:  python3 forensics/vendor_check.py
"""

import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
VENDOR = os.path.join(ROOT, "vendor", "zeta23")
SKIP_DIRS = {".lake", ".git"}
SKIP_EXT = (".olean", ".ilean", ".trace")


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the vendoring.  Exit 5.")
    sys.exit(5)


def tree_hash(root):
    """sha256 over sorted relative paths and each file's sha256."""
    paths = []
    for d, dirs, files in os.walk(root):
        dirs[:] = [x for x in dirs if x not in SKIP_DIRS]
        for f in files:
            if f.endswith(SKIP_EXT):
                continue
            paths.append(os.path.relpath(os.path.join(d, f), root))
    h = hashlib.sha256()
    for p in sorted(paths):
        h.update(p.encode())
        h.update(b"\0")
        try:
            with open(os.path.join(root, p), "rb") as fh:
                h.update(hashlib.sha256(fh.read()).digest())
        except OSError as exc:
            die_harness(f"cannot read {p}: {exc}")
    return h.hexdigest(), len(paths)


def recorded_hash():
    path = os.path.join(ROOT, "vendor", "PROVENANCE.md")
    try:
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
    except OSError as exc:
        die_harness(f"cannot read PROVENANCE.md: {exc}")
    m = re.search(r"tree hash\s*\|\s*`([0-9a-f]{64})`", text)
    if not m:
        print("FAIL  PROVENANCE.md records no tree hash.")
        return None
    return m.group(1)


def check_lakefile():
    try:
        with open(os.path.join(ROOT, "lakefile.toml"), encoding="utf-8") as fh:
            text = fh.read()
    except OSError as exc:
        die_harness(f"cannot read lakefile.toml: {exc}")
    m = re.search(r"\[\[require\]\]\s*\n\s*name\s*=\s*\"zeta23\"(.*?)(?=\n\[\[|\Z)",
                  text, re.S)
    if not m:
        return False, "lakefile.toml has no `zeta23` require"
    body = m.group(1)
    if re.search(r"^\s*git\s*=", body, re.M):
        return False, "the `zeta23` require still carries `git =`"
    if not re.search(r"^\s*path\s*=", body, re.M):
        return False, "the `zeta23` require carries no `path =`"
    return True, "requires `zeta23` by path"


def check_manifest():
    try:
        with open(os.path.join(ROOT, "lake-manifest.json"), encoding="utf-8") as fh:
            man = json.load(fh)
    except OSError as exc:
        die_harness(f"cannot read lake-manifest.json: {exc}")
    except json.JSONDecodeError as exc:
        return False, f"lake-manifest.json is not valid JSON: {exc}"
    for p in man.get("packages", []):
        if p.get("name") == "zeta23":
            if p.get("type") != "path":
                return False, f"manifest records `zeta23` as type {p.get('type')!r}"
            return True, f"manifest records `zeta23` as path {p.get('dir')!r}"
    return False, "manifest has no `zeta23` entry"


def main():
    print("=== vendored zeta-23 ===")
    bad = 0

    if not os.path.isdir(VENDOR):
        print("  [FAIL] bytes      vendor/zeta23 does not exist")
        return 1
    got, n = tree_hash(VENDOR)
    want = recorded_hash()
    if want is None:
        bad += 1
    elif got != want:
        print(f"  [FAIL] bytes      tree hash {got[:16]}… ≠ recorded {want[:16]}…")
        print(f"         {n} files hashed; the vendored copy has been edited")
        bad += 1
    else:
        print(f"  [ok ] bytes      {n} files, tree hash matches vendor/PROVENANCE.md")

    for label, fn in (("lakefile", check_lakefile), ("manifest", check_manifest)):
        ok, why = fn()
        print(f"  [{'ok ' if ok else 'FAIL'}] {label:9s} {why}")
        bad += not ok

    print()
    if bad:
        print("A failing row means the build may be reaching the network for")
        print("zeta-23.  `231`: editing the lakefile alone does not vendor —")
        print("the manifest is the authority, and lake will re-clone without it.")
    else:
        print("Vendoring intact.  Mathlib remains a git dependency; see")
        print("vendor/PROVENANCE.md for what this does and does not remove.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
