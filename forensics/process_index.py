#!/usr/bin/env python3
"""A greppable index of this project's process knowledge — rules, surprises, issues.

**Why this exists.**  `S115`: `ISSUES` `#14` recorded in session `003` that
detached builds do not survive a `Bash` call, and `281` hit exactly that `278`
cycles later and wrote it up as a discovery.  With `S111` (re-proving theorems
that existed), `S113` (the gate-then-commit rule) and `S114` (two neighbouring
quantities sharing a headline number), that is four recurrences of one shape in
thirty cycles: **the knowledge was on disk and finding it cost more than
rediscovering it the hard way.**

`R26`'s `statement_index` made theorems searchable — `5,118` of them.  Nothing
made *rules* searchable.  `#14` is marked `fixed`, and being marked fixed is
exactly why no instrument read it again.

**What it indexes, and why these four.**  Each is already structured, so this is
extraction rather than curation — a hand-made list would go stale like the prose
it replaces.

* `LOOP.md` — the `| R<n> | title | body |` rule table.
* `SURPRISES.md` — the `| S<n> | session | expected | happened | found-by | kind |`
  table.
* `ISSUES.md` — `## #<n> — [bin/status] title` headers with their first paragraph.
* `FAILURES.md` — `## W<n> — …` headers with their first paragraph.

**What it cannot do, stated plainly.**  It answers a query; it does not know when
to be queried.  `R26` works because it names its trigger (*before assuming or
fetching*).  The honest trigger here is narrower than "always": **before running
a long or unusual command, and before writing up a snag as new.**  The second
half is the one that would have caught `281`.

**And it only holds what a register holds.**  A lesson that lives solely in a
`SESSION` entry is not indexed, because `SESSION.md` is a log rather than a
register — `269` made the same call about entry boundaries there.  If a rule
matters, it belongs in `LOOP`, `ISSUES`, `SURPRISES` or `FAILURES`, and this
index is the reason that placement is now load-bearing.

Exit: 0 index current (or search ran) · 1 index stale · 5 harness failure.

Run:  python3 forensics/process_index.py
      python3 forensics/process_index.py --write
      python3 forensics/process_index.py --find 'detached|background'
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, os.pardir))
INDEX = os.path.join(HERE, "process_index.tsv")
HEADER = "\t".join(("kind", "id", "source", "text"))


def die_harness(what):
    print(f"HARNESS FAILURE: {what}")
    print("This is not a finding about the index.  Exit 5.")
    sys.exit(5)


def read(name):
    try:
        with open(os.path.join(ROOT, name), encoding="utf-8") as fh:
            return fh.read()
    except OSError as exc:
        die_harness(f"cannot read {name}: {exc}")


def flat(s, n=400):
    return re.sub(r"\s+", " ", s).strip()[:n]


def build():
    rows = []

    # LOOP.md — the rule table.  Bold markers around the id are optional.
    for m in re.finditer(r"^\|\s*\*{0,2}(R\d+[a-z]?)\*{0,2}\s*\|(.*)$",
                         read("LOOP.md"), re.M):
        rows.append(("rule", m.group(1), "LOOP.md", flat(m.group(2))))

    # SURPRISES.md — the surprise table.
    for m in re.finditer(r"^\|\s*(S\d+)\s*\|(.*)$", read("SURPRISES.md"), re.M):
        rows.append(("surprise", m.group(1), "SURPRISES.md", flat(m.group(2))))

    # ISSUES.md and FAILURES.md — headers plus their first paragraph.
    # `285`: the id may carry a parenthetical — `## #29 (original note,
    # superseded) — …` — which a `[a-z()]*` class misses because of the spaces.
    # Caught by comparing the row count against the header count; an index that
    # silently omits is `269`'s defect repeated.
    for name, pat, kind in (("ISSUES.md",
                             r"^## (#\d+(?:\s*\([^)]*\))?[a-z]*)\s*—\s*(.*)$",
                             "issue"),
                            ("FAILURES.md", r"^## (W\d+[a-z]*)\s*—\s*(.*)$", "failure")):
        text = read(name)
        ms = list(re.finditer(pat, text, re.M))
        for i, m in enumerate(ms):
            stop = ms[i + 1].start() if i + 1 < len(ms) else len(text)
            body = text[m.end():stop].strip().split("\n\n")
            first = body[0] if body else ""
            rows.append((kind, m.group(1), name,
                         flat(m.group(2) + " — " + first)))

    return ["\t".join(r) for r in rows]


def read_index():
    try:
        with open(INDEX, encoding="utf-8") as fh:
            return [l.rstrip("\n") for l in fh if l.strip()][1:]
    except FileNotFoundError:
        return None
    except OSError as exc:
        die_harness(f"cannot read the index: {exc}")


def main():
    args = sys.argv[1:]

    if args and args[0] == "--find":
        if len(args) < 2:
            print("usage: --find PATTERN")
            return 0
        rows = read_index()
        if rows is None:
            die_harness("no index; run --write first")
        pat = re.compile(args[1], re.I)
        hits = [r for r in rows if pat.search(r)]
        print(f"=== {len(hits)} match(es) for {args[1]!r} ===")
        for h in hits[:25]:
            f = h.split("\t")
            print(f"  [{f[0]}] {f[1]}  ({f[2]})")
            print(f"      {f[3][:200]}")
        if len(hits) > 25:
            print(f"  … {len(hits) - 25} more")
        return 0

    rows = build()
    if "--write" in args:
        with open(INDEX, "w", encoding="utf-8") as fh:
            fh.write(HEADER + "\n")
            fh.write("\n".join(rows) + "\n")
        print(f"wrote {len(rows)} rows to forensics/process_index.tsv")
        return 0

    have = read_index()
    if have is None:
        print("FAIL  no index on disk; run --write")
        return 1
    if have != rows:
        print(f"FAIL  index is stale: {len(have)} rows on disk, {len(rows)} in "
              f"the registers.  Run --write.")
        return 1

    counts = {}
    for r in rows:
        counts[r.split("\t")[0]] = counts.get(r.split("\t")[0], 0) + 1
    print(f"=== process index: {len(rows)} entries, current ===")
    for k in ("rule", "surprise", "issue", "failure"):
        print(f"  {k:9s} {counts.get(k, 0):>4}")
    print("  query it before a long or unusual command, and before writing up")
    print("  a snag as new.  It holds what the registers hold — a lesson kept")
    print("  only in a SESSION entry is not in here.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
