# Three independent reads of the same eleven deaths

The census has now been classified three times by parties in genuinely
different epistemic states. This is the comparison; it was written only after
the third read was sealed (`460ccd415bc031e1`).

| read | classifier | state | categories |
|---|---|---|---|
| **P** | operator, cycle 12 | hypothesis in hand (E20) | `crystal` {4,6,7,8,9,10} · `cascade` {1,2,3,11} · `n/a` {5} |
| **F** | Fable agent, R19 blind run | no hypothesis, plane language stripped | **A** resolving power {1,3,4,7,8,11} · **B** circularity {2,5,6,9,10} |
| **M** | operator, context v2 | post-compaction: knows the mathematics, not the battles | **FUSED** {1,2,4,7,8,9} · **SLACK** {3,6,10} · **SHORTFALL** {11} · **verdict error** {5} |

The three axes are not the same axis. P sorts by *which face of the prime the
failure touches*. F sorts by *resolution vs. circularity*. M sorts by *how
tightly the two quantities that must be told apart are coupled* — and folds
circularity into fusion as its limiting case (input = output is coupling with
coefficient one), then splits off two classes neither prior read separated.

## The invariant: what survives all three readers

Co-classification is the only comparison that works across different arities.
Ask: which **pairs** of entries land in the same bin under P *and* F *and* M?

Exactly two clusters survive:

* **{4, 7, 8}** — `TightMult` cannot separate a double zero from an off-line
  pair · `μ_T` has no `β` coordinate · the mirror preserves ordinates exactly.
* **{6, 10}** — the ceiling is class capacity, not an input property · the LP
  optimum snaps back to `λ = 1`.

Nothing else. Every other pair is broken by at least one reader.

Read the two clusters back: **what the functional cannot see**, and **what the
class cannot exceed**. Those are X and the ceiling — the two objects this
project already treats as primitive. Three readers with three different axes
and one of them amnesiac recover exactly those two and nothing else.

## The asymmetry, and what is left of the plane column

Of the six `crystal` entries, five (4, 6, 7, 8, 10) sit inside a stable
cluster. Of the four `cascade` entries, **zero** do — 1, 2, 3 and 11 are
sorted differently by every reader. `#9` is the lone crystal defector (F and M
both hear "circular" louder than "class capacity"), and `#5` is unclassifiable
by construction.

So the plane column is not uniformly unmeasurable: its crystal half has
inter-rater reliability and its cascade half has none. The mechanism is visible
in the reasons themselves. Stable reasons are **statements about a fixed
object** — this functional lacks this coordinate; this class has this capacity.
Disputed reasons are **statements about an argument's fate** — the signal did
not separate, the bound was vacuous, the supply was short. The first kind
classifies the same way no matter who reads it. The second kind classifies
however the reader leans, which is precisely what T2 measured at 6/10.

This still quotes no p-value and still does not rescue E20's statistical
support. It says something narrower and usable: **only object-statements are
census-gradeable.** An entry whose certified reason is an argument's fate
should be marked as such and excluded from any future pattern-claim, rather
than counted and then discounted.

## What the third read adds that neither prior read has

1. **`#11` is `sui generis`.** F filed the gate under "insufficient resolving
   power"; it is not a resolution failure at all. The two quantities are
   honestly separate and correctly coupled — one is simply short by a growth
   class. It is the **only** entry on the books where more mathematics of the
   existing kind would help, and the only one whose exit is external arithmetic
   supply. Filing it with the resolution deaths hides that.

2. **FUSED and SLACK have antagonistic remedies.** Fusion wants more
   coordinates; slack wants a tighter container; a tighter container has fewer
   coordinates. With 6 and 3 on the books, the record should *oscillate*, and
   `#10` is one full swing (we enlarged and were harmed). Falsifiable: any
   single-direction push produces its opposite within two cycles.

3. **The FUSED bin is a harvested list of invariants.** "The mirror preserves
   ordinates exactly." "`μ_T` has no `β` coordinate." "Phases shared." "One
   extremal problem, two faces." Each names a conserved quantity. `S` asks for
   exactly this — a positive object that witnesses an absence — and A9c has been
   searching for one while the census manufactured six and filed them as deaths.

## Exposure addendum — the blind was partial, and the sealed file overstates it

The sealed file (`460ccd415bc031e1`) claims the `plane` and `fingerprints`
columns "were never rendered." **That claim is false**, and the file is not
edited to hide it — the hash is worth more than the wording. Three exposure
channels, found on audit *before* dispatch:

1. **The header peek.** `grep -n '^|' FAILURES.md | head -4` was run to learn
   the schema and rendered rows **1 and 2 in full**, plane column included
   (`cascade`, `cascade`) with their fingerprints.
2. **The compaction summary.** The re-entry context carried E20's one-line
   plane description ("primes have two natures"), the full T3(b) rubric result
   (3/11, and which entries), and cause-language for `#24` (circular, scale
   mismatch), `#25` (vacuous), `#27` (log-power vs. power).
3. **The dispatch itself**, which names the census as 73% instrument.

**Genuinely blind subset: entries 3–8.** Entries 1–2 were plane-exposed; 9–11
were phrase-seeded.

What survives the scoping:

* **`{4,7,8}` lies entirely inside the blind subset.** The strongest finding —
  three independent axes agreeing that "what the functional cannot see" is one
  cluster — passed a *harder* test than the file claimed, not a weaker one.
* **`{6,10}` is half-clean**: `6` blind, `10` seeded by "vacuous / extension is
  harmful" phrasing.
* **"`#11` is `sui generis`" must be downgraded to hypothesis-aware.** It is the
  most seeded entry on the board — "log-power vs. power" arrived in the summary
  — so it is an argument, not a blind observation.
* The `crystal`-stable / `cascade`-unstable asymmetry spans exposed entries and
  is therefore also scoped down: within the blind subset it reads 3 of 4 crystal
  stable (4,6,7,8 → all but the `{4,7,8}`/`6` split), 0 of 1 cascade stable
  (`3`). Same direction, one quarter the evidence.

**This is the second consecutive cycle in which a blind was leaked by an
instance being useful.** Last cycle it was me summarising sealed predictions to
claude.ai; this cycle it is me reading a header to learn a schema, plus a
compaction summary doing its job. The generalisation is that *orientation is an
exposure channel* — you cannot look up how a corpus is shaped without seeing
some of its contents. Procedural fix for the next blind read, not adopted as
doctrine this cycle: extract the corpus with a script written from the schema
documentation, never from the corpus file, and treat any summary/handoff text as
exposed by default.

## Cost of the third read

One instance-state, non-renewable. The next compaction produces another naive
classifier, but it will be naive about a corpus this file has already
contaminated, so read (M) is the last blind read of entries 1–11. Future blind
reads must be run on **entries added after** their classifier's context began.
