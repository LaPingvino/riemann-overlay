#!/usr/bin/env python3
"""Trust audit of an external Lean 4 development — the reproducible form of a grep audit.

**Why this exists.**  `SESSION 445`: a scout audited Levent Alpöge's claimed RH
development (2026-11-20, 17.4M lines) by hand-run `grep`s and reported the result
in prose.  A grep audit that lives in a chat log cannot be re-run by a reader, so
this is the same audit as a script: every token list is written down below, the
counts it prints are a function of the tree, and anyone can run it on their own
copy.

**What it checks** (comments and string literals are stripped first, so a
docstring that *mentions* `sorry` does not count):

1. **Pins** — `lean-toolchain`, the `lakefile`'s requires and options, every
   package revision in `lake-manifest.json`; with `--ref-manifest`, the same
   rows side by side with another project's pins.
2. **Shipped artefacts** — `.lake/`, `*.olean`, a local `Mathlib/` directory,
   native code: anything that would let a build skip work or substitute a
   dependency.
3. **Forbidden tokens** — declarations or attributes that put something past the
   kernel or assume it: `axiom`, `sorry`, `admit`, `native_decide`,
   `implemented_by`, `extern`, `unsafe`, `ofReduceBool`/`reduceBool`,
   `trustCompiler`, `debug.skipKernelTC`, `addDeclWithoutChecking`, `csimp`, and
   `opaque` (kernel-checked, listed for review).
4. **Metaprogram sites** — every file that runs or defines code at elaboration
   time (`run_cmd`, `#eval`, `modifyEnv`, `addDecl`, `elab`, `macro`, `syntax`,
   `notation`, `initialize`, …).  These skip the *elaborator's* checks; whether
   they skip the *kernel's* is a question for a reader of each site, which is
   why they are listed rather than scored.
5. **Shadowing** — any declaration, notation or macro in the tree that reuses
   the name of a statement-level object (`RiemannHypothesis`, `riemannZeta`,
   `LFunction`, `DirichletCharacter`, …), which could make a faithful-looking
   top-level statement mean something else.
6. **The top-level statement** — the `theorem` lines of the main file(s), and
   whether the files that define their statements import anything but Mathlib.

**What it does not do.**  Grep is necessary, not sufficient.  It cannot see a
kernel bypass spelled in a way the lists below do not name, and it says nothing
about whether the proofs check.  The decisive tests are a full build and
`#print axioms` on the top-level theorem, ideally through an independent checker
(`lean4checker`, or the Lean FRO's comparator) — see `COMPARISON.md`'s checklist.

Exit: 0 report written, no forbidden token · 1 a forbidden token was found ·
5 harness failure (missing tree, unreadable file).

Run:  python3 -I tools/trust_audit.py PATH/TO/DEV
      python3 -I tools/trust_audit.py PATH/TO/DEV --main src/Main.lean \\
          --ref-manifest lake-manifest.json --json out.json
"""

import argparse
import json
import os
import re
import sys

FORBIDDEN = {
    # Word-boundary, not line-anchored: `set_option … in axiom x : False` and
    # two commands on one line must count (`445`'s drill).
    "axiom": r"\baxiom\b",
    "sorry": r"\bsorry\b",
    "sorryAx": r"\bsorryAx\b",
    "admit": r"\badmit\b",
    "native_decide": r"\bnative_decide\b",
    "implemented_by": r"\bimplemented_by\b",
    "extern": r"\bextern\b",
    "unsafe": r"\bunsafe\b",
    "reduceBool": r"\b(?:of)?[Rr]educeBool\b",
    "reduceNat": r"\bLean\.reduceNat\b|\bofReduceNat\b",
    "trustCompiler": r"\btrustCompiler\b",
    "debug.skipKernelTC": r"\bskipKernelTC\b",
    "addDeclWithoutChecking": r"\baddDeclWithoutChecking\b",
    "csimp": r"\bcsimp\b",
    "opaque": r"\bopaque\b",
}

METAPROGRAM = {
    "run_cmd": r"\brun_cmd\b",
    "run_elab": r"\brun_elab\b",
    "run_meta": r"\brun_meta\b",
    "#eval": r"#eval\b",
    "modifyEnv": r"\bmodifyEnv\b",
    "addDecl": r"\baddDecl\b",
    "addAndCompile": r"\baddAndCompile\b",
    "elab": r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:scoped|local|private)[ \t]+)*elab(?:_rules)?\b",
    "macro": r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:scoped|local|private)[ \t]+)*macro(?:_rules)?\b",
    "syntax": r"^[ \t]*(?:(?:scoped|local|private)[ \t]+)*syntax\b",
    "notation": r"^[ \t]*(?:(?:scoped|local|private)[ \t]+)*(?:notation|infixl?|infixr|prefix|postfix)\b",
    "initialize": r"^[ \t]*(?:builtin_)?initialize\b",
    "import Lean": r"^import[ \t]+Lean(?:\.|\b)",
}

SHADOW_NAMES = ["RiemannHypothesis", "riemannZeta", "LFunction",
                "DirichletCharacter", "hurwitzZeta", "completedRiemannZeta",
                "Complex.re", "IsPrimitive"]

DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:private|protected|noncomputable|partial|unsafe)[ \t]+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|opaque|axiom|instance)[ \t]+([^\s(:{\[]+)",
    re.M)

TOKEN = re.compile(r'/-|-/|--[^\n]*|"(?:\\.|[^"\\\n])*"')


def strip_keep_lines(src):
    """Remove (nested) block comments, line comments and string literals,
    keeping every newline so line numbers survive."""
    res, depth, pos = [], 0, 0
    for m in TOKEN.finditer(src):
        tok = m.group(0)
        seg = src[pos:m.start()]
        res.append(seg if depth == 0 else "\n" * seg.count("\n"))
        if tok == "/-":
            depth += 1
        elif tok == "-/":
            depth = max(depth - 1, 0)
        else:
            res.append("\n" * tok.count("\n") if depth == 0 else "")
        pos = m.end()
    tail = src[pos:]
    res.append(tail if depth == 0 else "\n" * tail.count("\n"))
    return "".join(res)


def die(msg):
    print(f"HARNESS: {msg}", file=sys.stderr)
    sys.exit(5)


def lean_files(root):
    for d, dirs, fs in os.walk(root):
        dirs[:] = sorted(x for x in dirs if x not in (".lake", ".git"))
        for f in sorted(fs):
            if f.endswith(".lean"):
                yield os.path.join(d, f)


def pins(root, ref):
    out = {}
    tc = os.path.join(root, "lean-toolchain")
    out["toolchain"] = open(tc).read().strip() if os.path.exists(tc) else None
    lf = [f for f in ("lakefile.toml", "lakefile.lean") if os.path.exists(os.path.join(root, f))]
    out["lakefile"] = lf[0] if lf else None
    if lf:
        txt = open(os.path.join(root, lf[0]), encoding="utf-8").read()
        out["lakefile_flags"] = [l.strip() for l in txt.splitlines()
                                 if re.search(r"moreLeanArgs|moreLinkArgs|extern_lib|precompile|"
                                              r"skipKernel|trustCompiler|leanOptions|\bweak\.|"
                                              r"maxHeartbeats|^\s*rev\s*=|^\s*git\s*=|^\s*path\s*=", l)]
    mf = os.path.join(root, "lake-manifest.json")
    out["packages"] = {}
    if os.path.exists(mf):
        for p in json.load(open(mf)).get("packages", []):
            out["packages"][p["name"]] = p.get("rev") or p.get("dir") or p.get("type")
    if ref:
        out["ref_packages"] = {p["name"]: p.get("rev") or p.get("dir")
                               for p in json.load(open(ref)).get("packages", [])}
    return out


def artefacts(root):
    found = []
    for d, dirs, fs in os.walk(root):
        for x in list(dirs):
            if x in (".lake", "build") or (x == "Mathlib" and d != root):
                found.append(os.path.relpath(os.path.join(d, x), root) + "/")
        if ".git" in dirs:
            dirs.remove(".git")
        for f in fs:
            if f.endswith((".olean", ".ilean", ".c", ".so", ".dylib", ".dll", ".a", ".o")):
                found.append(os.path.relpath(os.path.join(d, f), root))
    return found


def scan(root, max_sites):
    forb = {k: re.compile(v, re.M) for k, v in FORBIDDEN.items()}
    meta = {k: re.compile(v, re.M) for k, v in METAPROGRAM.items()}
    shadow = re.compile(r"\b(" + "|".join(re.escape(n) for n in SHADOW_NAMES) + r")\b")
    res = {"files": 0, "lines": 0,
           "forbidden": {k: {"count": 0, "sites": []} for k in FORBIDDEN},
           "metaprogram": {k: {"count": 0, "files": {}} for k in METAPROGRAM},
           "shadowing": []}
    for p in lean_files(root):
        try:
            raw = open(p, encoding="utf-8", errors="replace").read()
        except OSError as e:
            die(f"cannot read {p}: {e}")
        res["files"] += 1
        res["lines"] += raw.count("\n")
        src = strip_keep_lines(raw)
        rel = os.path.relpath(p, root)
        for k, rx in forb.items():
            for m in rx.finditer(src):
                e = res["forbidden"][k]
                e["count"] += 1
                if len(e["sites"]) < max_sites:
                    ln = src.count("\n", 0, m.start()) + 1
                    e["sites"].append(f"{rel}:{ln}: {raw.splitlines()[ln-1].strip()[:160]}")
        for k, rx in meta.items():
            n = len(rx.findall(src))
            if n:
                e = res["metaprogram"][k]
                e["count"] += n
                e["files"][rel] = n
        for m in DECL.finditer(src):
            last = m.group(1).split(".")[-1]
            if last in SHADOW_NAMES or m.group(1) in SHADOW_NAMES:
                ln = src.count("\n", 0, m.start()) + 1
                res["shadowing"].append(f"{rel}:{ln}: declares {m.group(1)}")
        # The keyword is matched on the stripped text, the name on the raw line:
        # a notation's own string literal is exactly where a shadowing name sits.
        rawlines = raw.splitlines()
        for ln_no, line in enumerate(src.splitlines(), 1):
            if re.match(r"\s*(?:scoped\s+|local\s+)?(?:notation|macro|syntax|macro_rules|infix\w*|prefix|postfix|"
                        r"attribute|export|open\s+\S+\s+renaming)\b", line) \
                    and ln_no <= len(rawlines) and shadow.search(rawlines[ln_no - 1]):
                res["shadowing"].append(f"{rel}:{ln_no}: {rawlines[ln_no - 1].strip()[:160]}")
    return res


def toplevel(root, mains):
    out = []
    for m in mains:
        p = os.path.join(root, m)
        if not os.path.exists(p):
            out.append({"file": m, "missing": True})
            continue
        raw = open(p, encoding="utf-8").read()
        src = strip_keep_lines(raw)
        imports = re.findall(r"^import\s+(\S+)", src, re.M)
        thms = [l.strip() for l in src.splitlines() if re.match(r"\s*theorem\s", l)]
        out.append({"file": m, "imports": imports, "theorems": thms})
        srcdir = os.path.dirname(p)
        for imp in imports:
            q = os.path.join(srcdir, *imp.split(".")) + ".lean"
            if os.path.exists(q) and imp.split(".")[0] not in ("Mathlib", "Lean", "Std", "Init"):
                s2 = strip_keep_lines(open(q, encoding="utf-8").read())
                imps2 = re.findall(r"^import\s+(\S+)", s2, re.M)
                defs = [l.strip() for l in s2.splitlines() if re.match(r"\s*(def|abbrev|structure)\s", l)]
                out.append({"file": os.path.relpath(q, root), "imports": imps2,
                            "only_mathlib": all(i.split(".")[0] == "Mathlib" for i in imps2),
                            "defs": defs})
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("--main", action="append", default=None)
    ap.add_argument("--ref-manifest")
    ap.add_argument("--json")
    ap.add_argument("--max-sites", type=int, default=20)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    if not os.path.isdir(root):
        die(f"missing tree: {root}")
    mains = a.main or ["src/Main.lean"]

    report = {"root": root, "pins": pins(root, a.ref_manifest),
              "artefacts": artefacts(root), "toplevel": toplevel(root, mains)}
    report.update(scan(root, a.max_sites))

    P = report["pins"]
    print(f"=== trust audit: {root}")
    print(f"  {report['files']} .lean files, {report['lines']} lines")
    print("\n=== 1. pins")
    print(f"  toolchain: {P['toolchain']}")
    print(f"  lakefile:  {P['lakefile']}")
    for l in P.get("lakefile_flags", []):
        print(f"    {l}")
    for n, r in sorted(P["packages"].items()):
        ref = P.get("ref_packages", {}).get(n)
        cmp = "" if ref is None else ("   = ref" if ref == r else f"   ref: {ref}")
        print(f"  {n:18} {r}{cmp}")
    print("\n=== 2. shipped artefacts")
    print("  none" if not report["artefacts"] else "\n".join("  " + x for x in report["artefacts"][:50]))
    print("\n=== 3. forbidden tokens (comments and strings stripped)")
    bad = 0
    for k, e in report["forbidden"].items():
        mark = "ok " if e["count"] == 0 else ("REVIEW" if k == "opaque" else "FOUND")
        if e["count"] and k != "opaque":
            bad += 1
        print(f"  [{mark:6}] {k:24} {e['count']}")
        for s in e["sites"]:
            print(f"           {s}")
    print("\n=== 4. metaprogram sites (elaborator-level; read each, they are not scored)")
    for k, e in report["metaprogram"].items():
        print(f"  {k:14} {e['count']:6} in {len(e['files'])} files")
        for f, n in sorted(e["files"].items(), key=lambda kv: -kv[1])[:a.max_sites]:
            print(f"      {n:5}  {f}")
    print("\n=== 5. shadowing of statement-level names")
    print("  none" if not report["shadowing"] else "\n".join("  " + s for s in report["shadowing"][:100]))
    print("\n=== 6. top-level statement")
    for t in report["toplevel"]:
        print(f"  {t['file']}" + ("  MISSING" if t.get("missing") else ""))
        for k in ("imports", "theorems", "defs"):
            for x in t.get(k, []):
                print(f"    {k[:-1]:8} {x}")
        if "only_mathlib" in t:
            print(f"    imports only Mathlib: {t['only_mathlib']}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(report, f, indent=1)
    print(f"\n{'CLEAN of the listed tokens' if not bad else f'{bad} forbidden token kind(s) FOUND'}"
          " — necessary, not sufficient; see the module docstring.")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
