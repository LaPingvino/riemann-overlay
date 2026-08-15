#!/usr/bin/env python3
"""Tally SURPRISES.md mechanically.

The register is the record; this script is the only thing allowed to state its
counts, so nobody (me included) can quote a number the table does not support.

Per the register's anti-Goodhart clause, the total is deliberately printed LAST
and the `corrected by` breakdown first: the breakdown is the informative
statistic, the total is not a score.

Run: python3 forensics/surprises.py
"""

import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REGISTER = os.path.join(HERE, os.pardir, "SURPRISES.md")

ROW = re.compile(r"^\|\s*(S\d+)\s*\|([^|]*)\|([^|]*)\|([^|]*)\|([^|]*)\|([^|]*)\|")


def rows(path=REGISTER):
    out = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            m = ROW.match(line.strip())
            if m:
                sid, session, expected, happened, by, cls = (
                    g.strip() for g in m.groups())
                out.append({
                    "id": sid, "session": session, "expected": expected,
                    "happened": happened, "by": by, "class": cls,
                })
    return out


def norm_by(field):
    """The corrector, without the timing qualifier ('self, late' -> 'self')."""
    return field.split(",")[0].split("(")[0].strip()


def main():
    rs = rows()
    if not rs:
        print("SURPRISES.md: no rows parsed — schema drift?", file=sys.stderr)
        return 1

    by = collections.Counter(norm_by(r["by"]) for r in rs)
    cls = collections.Counter(r["class"] for r in rs)
    late = [r["id"] for r in rs if "late" in r["by"]]

    print("corrected by  (the informative statistic)")
    for k, v in by.most_common():
        print(f"  {k:10s} {v:3d}")

    print("\nclass")
    for k, v in cls.most_common():
        print(f"  {k:12s} {v:3d}")

    external = sum(v for k, v in by.items() if k != "self")
    print(f"\n  external corrections : {external}/{len(rs)}"
          f"  ({100 * external / len(rs):.0f}% found by something that is not me)")
    if late:
        print(f"  self-caught LATE     : {', '.join(late)}"
              "   <- these are the expensive ones")

    # Correlated misses: the quantity FRAMING's seam claim lives on.  Counted
    # from the dedicated section rather than the main table, because the field
    # is only pre-registered from 2026-08-15 onward and the backfill is partial.
    text = open(REGISTER, encoding="utf-8").read()
    both = text.count("**shared priming**") + text.count("**anchoring on disclosure**")
    print(f"\ncorrelated misses (both instances endorsed): {both}"
          "   rescued by the seam: 0")
    print("  see 'Correlated misses' below the table; kill condition is on the"
          " `both` rate after 20 further entries.")

    print(f"\ntotal recorded surprises: {len(rs)}"
          "   (not a score; see the anti-Goodhart clause)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
