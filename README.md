# riemann — Lean skeleton for the overlay program

A Lean 4 formalization of the *reduction structure* of the program document
"Toward 100% of Zeta Zeros on the Critical Line". Not a proof of anything
about `ζ`: the deliverable is the **interfaces**, and a machine check that the
arrows of the dependency graph compose.

```
Riemann/Basic.lean        H(γ), N⊛, Prop 1, N + N_off ≤ N⊛     proved, axiom-free
Riemann/Transfer.lean     (★) ⟹ proportion 2 − C               proved, axiom-free
Riemann/Fujii.lean        the numeric window for [OPEN 0]      proved, axiom-free
Riemann/Gauge.lean        NscStd is not gauge-invariant        proved, axiom-free
Riemann/Blindness.lean    no μ_T-invariant hypothesis computes proved, axiom-free
                          NscStd or N_off
Riemann/Fiber.lean        the blindness is supported exactly   proved, axiom-free
                          on the crowded atoms
Riemann/Zeta.lean         zetaZeroData                         proved, axiom-free
Riemann/Gaps.lean         one Prop per open problem            definitions
Riemann/Assumptions.lean  every axiom, with its source         trusted base
Riemann/Program.lean      the §6 arrows                        proved from the axioms
Riemann/Proportion.lean   the fitness function                 certified vs conjectural
```

`audit/regression/Boom_2026-08-13.lean` is a **negative** test: it derived
`False` from an earlier version of the axioms and must never compile again
(ISSUES #8).

## Where to start

* **`FRAMING.md`** — where this came from: the companion document written by the
  collaborating claude.ai instance, describing the half of the project that does
  not live in this repository (the operator, the two instances, the seam between
  them), followed by a verification appendix that audits its own claims against
  these files and records the one that had to be corrected.
* **`F.md`** — the fictions: derivations narrated as if they existed, each
  naming the cast that would have to be hired for the story to compile. A
  fiction whose cast is proven impossible converts to a rung.
* **`CLAIMS.md`** — every class-impossibility assertion ("no member of class `C`
  can do `X`"), graded **A** certified / **B** certifiable-but-prose / **C**
  class-undefined. Anything cited as a bound must be grade A.
* **`SURPRISES.md`** — the calibration meter: every time the record went against
  a stated expectation, with who or what did the correcting. Tallied
  mechanically by `forensics/surprises.py`; read the breakdown, never the total
  (the file says why).
* **`METHOD.md`** — how the project is run: the loop, the rules R1–R19, the
  two-row ledger, the anti-Goodhart defences, the guards.
* **`VERIFYING.md`** — exact reproduction instructions and how to check every
  claim below yourself.

Then the registers, in this order: `SESSION.md` (the numbered log — read it
first), `ISSUES.md` (the friction — that is where the content is),
`STATEMENTS.md` (the translation layer, which needs human audit), `LEADS.md`
(the wildcard queue), `FAILURES.md` (the census of deaths, with its
contamination note), `E.md`, `A.md`, `S.md`, `PRICES.md`.

## What is proved, what is assumed, what is conjectural

**Proved, axiom-free** — and this is the project's own content — the
combinatorial core and the transfer:

```lean
theorem certified_axiomFree (F : Family) (C : ℝ) (h : F.toCounts.StarBound C) :
    F.toCounts.Proportion (2 - C) ∧
      ∀ ε > 0, ∀ᶠ T in atTop, F.Noff T ≤ (C - 1 + ε) * F.Nz T
```

For **any** zero family, `(★)` transfers to a proportion and the off-line count
is capped. Alongside it: the gauge/blindness/fiber cluster, which proves that
no `μ_T`-invariant hypothesis — of any strength — computes `NscStd` or `N_off`,
and locates that obstruction exactly on the atoms of mass `≥ 2`.

**Assumed** — the trusted base is exactly the **nine axioms** of
`Riemann/Assumptions.lean`, each carrying its source in a docstring: the two
imported baselines (PRZZ 2019 at `0.4162`, zeta-23 Theorem D at `0.6725`), the
`ξ'` proportion `0.85838`, Levinson–Montgomery, the ineffective Fujii bound,
close-pair bookkeeping, `xiPrimeFamily`, `closePairsZeta`, and `zetaNonempty`.
There are no axioms anywhere else in the repository.

**Conjectural** — the `Nsc` row opens at `c₀ ≤ 4.5`; Route I at `c₀ ≤ 0.33`;
`100%` conditional on [OPEN D].

## The score

The ledger is **two rows, always reported together**: `NscStd` is the
literature's notion (multiplicity one, on the line — zeta-23's `N0simple`) and
`Nsc` is this project's stronger notion (`H = 1`: the ordinate carries nothing
else). They are linked by `ZeroData.two_NscStd_le` at a cost of `(C−1)/2`, so
the gap between them is a certified function of `C` that closes exactly when
`(★)` succeeds. The current line of `PROPORTION.log`:

```
2026-08-14 | base: v2/cd7a22e688df (zetaNonempty) | context: v2 (compacted)
  | certified[NscStd: 67.25%, Nsc: 0.00%] | conjectural: 100.00% (OPEN D)
  | axioms: 2 (Riemann.baseline_zeta23, Riemann.zetaNonempty) | sorries: 0
  | binding: Riemann.baseline_zeta23
```

`certified` counts only lemmas with no `sorry` in their cone (axioms of
`Assumptions.lean` permitted and listed by name). The `NscStd` row is today
carried entirely by an axiom — the imported zeta-23 Theorem D, whose discharge
is blocked only on constructing `zetaFamily` from zeta-23's
`zerosIn`/`zeroMult`. The `Nsc` row reads `0.00%` because no unconditional
`(★)` exists at any constant, and `LOOP.md`'s empty-row principle says a row
that is honestly zero beats a row quietly redefined until it is not.

The `axioms: 2` field is the axiom **cone of the best certified row**, not the
size of the trusted base (which is 9); see `VERIFYING.md` §3.2.

## Build

```bash
lake exe cache get                       # Mathlib oleans for the pinned rev
lake build                               # ~3700 jobs cold
lake env lean audit/PrintAxioms.lean     # trusted-base audit
lake env lean audit/Declarations.lean    # every claimed name must exist
go run tools/proportion.go -append       # the score (also runs the guards)
```

Toolchain: `leanprover/lean4:v4.33.0-rc2` (see `lean-toolchain`). Mathlib and
the rest are inherited transitively from `zeta-23-lean` and pinned by exact
revision in `lake-manifest.json` — that file and `lean-toolchain` are tracked
for exactly this reason. `.lake/` is gitignored.

`tools/proportion.go` is a gate, not a reporter: it exits `4` if a claimed
declaration is missing, `5` if a file in `audit/regression/` *compiles*, and `3`
if the trusted base's statement hash moved without a `base.version` bump — and
in cases `3` and `4` it refuses to write the log line. Full details, including
the exit-4 signature of a missing `lake` on `PATH`, are in `VERIFYING.md`.
