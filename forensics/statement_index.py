#!/usr/bin/env python3
"""A greppable index of every theorem in this repo and in the vendored dependency.

**Why this exists.**  Two failures, twelve cycles apart, with one cause.

* `255` re-proved `noHaunted_of_mult_le_two` and `noHaunted_not_mult_le_two`,
  which had been in `Fiber.lean` since `181`, were in `audit/Declarations.lean`,
  and were cited by name in `RULING.md`.  `S111`.
* `267` found `zeta23_xiPrime` axiomatising `0.85838` while
  `Zeta23/XiPrime/Final.lean` proves that exact constant, sorry-free, in lines we
  vendor and never import.

In both, the thing already existed and the cost of finding it was higher than the
cost of redoing it.  `268` measured the scale of the second: we reach `3.0%` of
`103,067` vendored lines, so "already proved somewhere on disk" is now the normal
case rather than the exception.

**What this makes cheap.**  One `grep` over `forensics/statement_index.tsv`
answers *"does anything already conclude this?"* across `~5,100` declarations in
both trees.  Columns are `tree`, `module`, `kind`, `name`, `statement`,
`reachable`, `doc`.

`reachable` is the column that matters for the dependency: `yes` means our build
already imports it and it can be cited today; `no` means the proof exists but
would need a build (`268` prices those — `RvM.Statement` `9,148` lines,
`ThmD.Final` `44,441`, `XiPrime.Final` `82,256`).

**What it is not for.**  Searching before *proving* is wrong.  Most of this
project's content is about structures the dependency has no concept of — the
ledger, the profile, hauntedness — and an index hit there is a false alarm.  The
rule this pairs with is: **search before assuming, and before fetching.**  An
axiom or a literature request is the moment to run it; a new theorem about the
ledger is not.

**One blind spot, measured rather than guessed** (`S117`).  This indexes
*statements*, so a declaration that names a construction only in its proof is
invisible to a search for that construction.  `row_essentially_optimal` reads
`∃ D : ZeroData, …` and builds its `D` with `chain` inside the proof; searching
`chain a` returns eight rows and that is not one of them.  The rule the blind
spot implies is narrow: **an existential witness cannot be found by what it is
made of, only by what it concludes** — so search for the *conclusion* when
asking "has anyone built one of these", and expect the builder query to
under-report.

`S117` also records the failure this does *not* excuse: `296` answered "has
`chain` been used as a witness before?" with a grep for `chain a` followed by a
bracket, which
matches only witnesses that inline a list literal.  Every prior one binds the
list with `set L := …` first, so the grep returned zero and the zero was read as
an answer.  The index would have returned two of the four.

**Staleness is checked, not trusted.**  Run with no arguments to verify the
committed index still matches the sources; exit `1` if it drifted.  `--write`
regenerates it.  `--find PATTERN` searches it.

Exit: 0 index current (or search ran) · 1 index stale · 5 harness failure.

Run:  python3 forensics/statement_index.py
      python3 forensics/statement_index.py --write
      python3 forensics/statement_index.py --find 'simple_on_line'
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
INDEX = os.path.join(HERE, "statement_index.tsv")

TREES = [("ours", os.path.join(ROOT, "Riemann"), "Riemann"),
         ("dep", os.path.join(ROOT, "vendor", "zeta23"), "")]

# `269` first wrote this as one regex with an optional leading docstring under
# `re.S`.  That silently dropped `697` declarations of `5,114` — a docstring's
# `.*?` runs forward across the next declaration and swallows it.  An index that
# quietly omits `14%` answers "nothing already proves this" from a partial
# snapshot, which is the failure it exists to prevent.  Scan anchored for the
# declaration, then look *backwards* for its docstring.
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([A-Za-z_][\w'\.]*)", re.M)


def statement_of(text, start, stop):
    """Text from the declaration name to its top-level `:=`."""
    seg = text[start:stop]
    depth = 0
    for i, ch in enumerate(seg):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and seg[i:i + 2] == ":=" and depth == 0:
            return seg[:i]
    return seg


def doc_before(text, start):
    """The docstring immediately above a declaration, if any."""
    head = text[:start].rstrip()
    if not head.endswith("-/"):
        return ""
    open_at = head.rfind("/--")
    if open_at < 0 or "-/" in head[open_at + 3:-2]:
        return ""
    return re.sub(r"\s+", " ", head[open_at + 3:-2]).strip()[:160]


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the index.  Exit 5.")
    sys.exit(5)


def modules(root):
    out = {}
    if not os.path.isdir(root):
        die_harness(f"missing tree: {root}")
    for d, dirs, fs in os.walk(root):
        dirs[:] = [x for x in dirs if x != ".lake" and not x.startswith(".")]
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                mod = os.path.relpath(p, root)[:-5].replace(os.sep, ".")
                try:
                    with open(p, encoding="utf-8") as fh:
                        out[mod] = fh.read()
                except OSError as exc:
                    die_harness(f"cannot read {p}: {exc}")
    return out


def reachable_dep(dep):
    """Modules our build actually imports.  Roots include Riemann.lean itself —
    `267` reported 2.1% by starting from the directory and missing the root's
    `import Zeta23.PairCeiling.CeilingLaw256` on line 14."""
    text = ""
    paths = [os.path.join(ROOT, "Riemann.lean")]
    d = os.path.join(ROOT, "Riemann")
    if os.path.isdir(d):
        paths += [os.path.join(d, f) for f in sorted(os.listdir(d))
                  if f.endswith(".lean")]
    for p in paths:
        if os.path.exists(p):
            with open(p, encoding="utf-8") as fh:
                text += fh.read()
    imports = {m: set(re.findall(r"^import\s+([\w.]+)", s, re.M))
               for m, s in dep.items()}
    seen, stack = set(), list(re.findall(r"^import\s+(Zeta23[\w.]*)", text, re.M))
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(x for x in imports.get(m, ()) if x in dep)
    return seen


def flat(s, n=240):
    s = re.sub(r"\s+", " ", s).strip()
    return s[:n]


def build():
    rows = []
    dep = modules(TREES[1][1])
    reach = reachable_dep(dep)
    for tree, root, prefix in TREES:
        src = modules(root) if tree == "ours" else dep
        for mod, text in sorted(src.items()):
            full = f"{prefix}.{mod}" if prefix else mod
            ms = list(DECL.finditer(text))
            for i, m in enumerate(ms):
                stop = ms[i + 1].start() if i + 1 < len(ms) else len(text)
                stmt = statement_of(text, m.end(), stop)
                doc1 = doc_before(text, m.start())
                r = "-" if tree == "ours" else ("yes" if mod in reach else "no")
                rows.append("\t".join(
                    (tree, full, m.group(1), m.group(2), flat(stmt), r, doc1)))
    return rows


def read_index():
    try:
        with open(INDEX, encoding="utf-8") as fh:
            return [l.rstrip("\n") for l in fh if l.strip()][1:]
    except FileNotFoundError:
        return None
    except OSError as exc:
        die_harness(f"cannot read the index: {exc}")


HEADER = "\t".join(("tree", "module", "kind", "name", "statement",
                    "reachable", "doc"))


def main():
    args = sys.argv[1:]

    if args and args[0] == "--find":
        if len(args) < 2:
            print("usage: --find PATTERN")
            return 0
        pat = re.compile(args[1], re.I)
        rows = read_index()
        if rows is None:
            die_harness("no index; run --write first")
        hits = [r for r in rows if pat.search(r)]
        print(f"=== {len(hits)} match(es) for {args[1]!r} ===")
        for h in hits[:40]:
            f = h.split("\t")
            print(f"  [{f[0]}{'/' + f[5] if f[5] != '-' else ''}] {f[3]}")
            print(f"       {f[1]}")
            print(f"       {f[4][:150]}")
        if len(hits) > 40:
            print(f"  … {len(hits) - 40} more")
        return 0

    rows = build()
    if "--write" in args:
        with open(INDEX, "w", encoding="utf-8") as fh:
            fh.write(HEADER + "\n")
            fh.write("\n".join(rows) + "\n")
        print(f"wrote {len(rows)} rows to forensics/statement_index.tsv")
        return 0

    have = read_index()
    if have is None:
        print("FAIL  no index on disk; run --write")
        return 1
    if have != rows:
        print(f"FAIL  index is stale: {len(have)} rows on disk, {len(rows)} in "
              f"the sources.")
        print("A stale index is worse than none — it answers 'nothing already")
        print("proves this' from a snapshot.  Run --write.")
        return 1
    ours = sum(1 for r in rows if r.startswith("ours\t"))
    reach = sum(1 for r in rows if "\tyes\t" in r)
    print(f"=== statement index: {len(rows)} declarations, current ===")
    print(f"  ours              {ours:>5}")
    print(f"  dependency        {len(rows) - ours:>5}  "
          f"of which reachable today: {reach}")
    print("  search it before adding an axiom or fetching literature;")
    print("  not before proving something about the ledger.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
