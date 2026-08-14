# SURPRISES — the calibration meter

Every time the record went **against my stated expectation**. Not every error:
an error I never had a view on is just a fact I learned. This register counts
the cases where I had a position and the world disagreed.

**Schema:** `id | session | I expected | what happened | corrected by | class`

`corrected by`: `kernel` (Lean said no) · `tooling` (a guard, the lint, the
ledger, a script) · `c.ai` (the framing instance) · `Fable` (the advisor) ·
`self` (I caught it, and *when* matters) · `source` (the literature).

`class`: `calibration` (I was confidently wrong about a fact) ·
`design` (the thing I built did not do what I built it for) ·
`process` (the discipline failed, not the mathematics).

## The anti-Goodhart clause, stated before the table

**This counter must never be a target, in either direction.** A rising count is
not virtue (it is easy to manufacture by predicting carelessly) and not vice
(a project that never surprises itself has stopped making predictions). The
number that carries information is the **denominator-relative rate** and, above
all, the **`corrected by` breakdown**:

* corrections arriving from **tooling** mean the instruments are ahead of the
  operator — the system working as designed;
* corrections arriving from **self, late** mean the instruments were behind and
  something got published in the interval;
* corrections arriving from **c.ai** mean the seam earned its cost that cycle.

If this file is ever cited as evidence of anything, cite the breakdown, not the
total.

## The table

| # | session | I expected | what happened | corrected by | class |
|---|---|---|---|---|---|
| S1 | 013 | the build ran; three theorems existed | `rc=0` came from an **unchanged tree**; the three theorems did not exist, and I had already filed them in `A.md` | tooling (`#print axioms`) | process |
| S2 | 024 | my `c`-table was sound | **unsound twice over** — scale mismatch *and* circularity; the alarm had been right both times | self, late | calibration |
| S3 | 026 | my published thresholds were merely hard to reach | Lemma 1 made them **RH-impossible**, i.e. vacuous | source | calibration |
| S4 | 027–028 | the fuel chain closes at `0.809` | the gate **fails**; `0.80869` retracted to Montgomery's `2/3` | self (shape check) | calibration |
| S5 | 029 | the census's `11/11` alignment supported E20 | blind re-classification gave **6/10 against chance 5/10**; E20's statistical support died | Fable (blind run) | calibration |
| S6 | 031 | T3(b) answer is **2** (sealed) | mechanical answer is **3**; the extra was `#27`, the entry I was most confident about | tooling (`provenance_lint`) | calibration |
| S7 | 031 | my first lint run's `5/11` was right | wrong — I had modelled `F_on_[0,1]` as RH-dependent; it is BGST's unconditional `𝓕`. Fixing the node gave 3 | self, same cycle | calibration |
| S8 | 032 | the blind trichotomy was clean | **three exposure channels** — my own schema-learning `grep` had rendered rows 1–2 with the plane column, and the compaction summary carried cause-language | self, pre-dispatch | process |
| S9 | 032 | my coupling axis would broadly agree with the prior reads | only `{4,7,8}` and `{6,10}` survived all three readers; every other pair was broken by someone | tooling (co-classification) | calibration |
| S10 | 033 | "useful iff non-`μ_T`-invariant" | **false** — an effective Fujii constant is μ-invariant and would move both rows. The specification is narrower than I wrote it | Fable | calibration |
| S11 | 033 | β-information is bought, never manufactured | β-*inequalities* are manufactured routinely (`on_line_of_H_eq_one`, `odd_Hr_inhabited`, `prop1`); only β-*identities* are not | Fable | calibration |
| S12 | 035 | `#5` (W4) was a kill | **container-local** — resurrected as CGdL 2018. Kill conditions do not travel | source | design |
| S13 | 036 | the two-height family forces the phase channel | it does **not**; no family built this way can, and whether phase is necessary is still open | self (by building it) | design |
| S14 | 036 | the swap family is a sharper test | it is a **symmetry** — agrees on every target count, so discriminating it is not a virtue | self (by building it) | design |
| S15 | 037 | the asymptotics would be crueller than the numerics, as in `#27` | **kinder** — the exponent promises `c<2`, the feasible crossover at `T=10^12` is `1.39` | tooling (crossover calc) | calibration |
| S16 | 038 | five string assertions would match the guard file | the fourth failed on whitespace; the guard was left untouched, which was luck of construction rather than design | tooling (assertion) | process |
| S17 | 032 | the env would be inherited by the tool run | `proportion.go` exited **4 with an empty body** — no `lake` on `PATH`; the audit worked, the operator did not | tooling (exit 4) | process |
| S18 | 036 | the boundary is β-*equality* vs β-*inequality* | wrong boundary — `on_line_of_H_eq_one` **is** a β-equality from ordinate data. The real boundary is **solitude**: computable on the simple locus, blind on crowded atoms | c.ai | calibration |
| S19 | 039 | rung 0 was **owned** — I relayed the ladder brief's claim that `{F on [0,1], F ≥ 0}` independence was already held | it is **prose, uncertified**; the only runnable capacity certificate (`ceiling_law256`) is imported from zeta-23, not ours | tooling (the audit's own criterion) | process |

## Standing observation

**Not one entry on this table was found by re-reading my own prose.** Every
correction came from an instrument, another instance, a source, or from
*building the thing and watching it fail* — never from thinking harder about a
claim I had already written down. That is the argument for the whole apparatus
in one line, and it is also why `S13` and `S14` are the most valuable rows:
they are the two cases where the correction cost nothing but the construction.
