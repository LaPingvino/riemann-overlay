/-
# Assumptions

**Every** axiom of this development is declared here and nowhere else, so
that the trusted base is auditable in one screen.  Each carries its source.
`grep '^axiom' Riemann/Assumptions.lean` is the audit; the count feeds
`PROPORTION.log`.

Rules of the house:
* literature results Mathlib does not have → axiom **here**, with the paper
  and theorem number, and a row in `STATEMENTS.md`;
* open problems → **not** axioms; they are `Prop`s in `Gaps.lean`, carried as
  hypotheses.  An open problem must never be assumed;
* **an axiom may only speak about the fixed constants declared in this file**
  (`zetaFamily`, `xiPrimeFamily`, `closePairsZeta`).  An axiom quantified over
  an arbitrary `Family` asserts a theorem about `ζ` for adversarial toy
  models, and is refutable — that mistake was made and caught on 2026-08-13;
  see ISSUES.md #8 and `audit/regression/`;
* raising the certified proportion by adding an axiom is not progress and
  must be flagged in `SESSION.md`.

## Consistency model

`#print axioms` audits proof cones; it cannot tell you the base is
satisfiable.  So the base carries an explicit model, and **anyone who adds a
new axiom must extend it**:

> `D T := {(1/2, 0)}` for every `T` (one zero, on the line; `refl_inv` is
> trivial), `zetaFamily = xiPrimeFamily` that family, `closePairsZeta ≡ 0`,
> `c₀ = 1`.

Then: `Nsc/Nz = 1`, so every `Proportion` axiom holds; `Noff = 0`, so
`levinson_montgomery` holds; `ClosePairLowerBound closePairsZeta _ _ c₁` is
false for every `c₁ > 0`, so `fujii_closePair_bookkeeping` is vacuous; and
`Cbound 1 λ ≥ λ + √(log 2)/λ > 1` for `λ < 1`, `≥ λ ≥ 1` otherwise, so
`fujii_ineffective` holds against `N⊛ = N`.
-/
import Riemann.Gaps
import Riemann.Zeta

namespace Riemann

/-! ### The objects -/

/-- **All that remains of the old `axiom zetaFamily`**: that `ζ` has zeros.

Base v1 assumed the whole structure — that the zeros of `ζ` form a
reflection-invariant multiset family at all.  Base v2 assumes only eventual
nonemptiness: finiteness in a window, the multiplicity function, closure under
`ρ ↦ 1 − conj ρ` and multiplicity invariance are **constructed** in
`Riemann/Zeta.lean` from theorems of `zeta-23-lean`.

Discharging what is left needs `(zetaZeroData T).N = Zeta23.Ncount 0 T` (a
`finsum` ↔ `Finset.sum` conversion) and eventual positivity of `Ncount` from
`Zeta23.RvM.riemannVonMangoldt`.  Plumbing, not mathematics.

**`270`: the first step is done.**  `Riemann.zetaZeroData_N` proves
`(zetaZeroData T).N = Zeta23.Ncount 0 T`, axiom-free and with no new import —
`Ncount` and `zeroMult` are already in the `17`-module closure we reach.

What remains is eventual positivity, and it has a price rather than a
difficulty.  `Zeta23.RvM.Statement.riemannVonMangoldt` needs `GammaFacts`, which
`Zeta23.gammaFacts` proves unconditionally, and `Assembly.tendsto_N_atTop` turns
`RiemannVonMangoldt zetaZeroConfig` into the divergence this axiom asserts.  The
chain is complete and unconditional.  The cost is the import.

**`271` corrects the price and the shape of what is left.**

* `Zeta23.gammaFacts` is **not** in `RvM.Statement`'s closure, so the discharge
  needs `Zeta23.GammaFacts.Complete` as well: **`34` modules, `11,710` lines**,
  not `270`'s `27`/`9,148`.
* `RiemannVonMangoldt.main` is **dyadic** — `Z.N T (2·T)` — where this axiom is
  cumulative.  The import alone does not close it; the missing step is
  `Riemann.Ncount_mono_left`, which is ours and needs no import.

**`281`: `ThmD.Final`'s build measured — `18m12s` one-time, `+6s` per
elaboration.**  `268` priced it at `125` modules and `44,441` lines and left the
wall-clock unmeasured.  It is `1092s` of build from the state after `270`'s, and
afterwards `import Zeta23.ThmD.Final` costs about six seconds on top of
`import Riemann`'s nine.

**`279`: `baseline_zeta23`'s numeric second cost is gone.**
`Riemann.baseline_decimal_le_exact` proves `0.6725 ≤ 3/2 − cot(1/√2)/√2`,
axiom-free — so the decimal this axiom asserts is a proved floor for the exact
constant `ThmD` establishes, and the two no longer differ by an unbridged
rounding. `ThmD`'s `44,441`-line build remains that axiom's price; the numerics
do not.

**`272` closes the last gap on our side.**  `Riemann.zetaNonempty_of_rvm_main`
takes exactly `RiemannVonMangoldt.main`'s statement — the asymptotic
`|N(T,2T) − T·ℓ₁/2π| ≤ C·log T` — and returns this axiom.  Positivity of the
dyadic count follows because `ℓ₁ → ∞` bounds the main term below by `T/2π`, and
`log` is eventually beaten by any multiple of the identity; both are proved
unconditionally in `Riemann/Zeta.lean` at no build cost.

So the discharge is now **one imported fact and one rewrite**: obtain
`Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts |>.main`, rewrite with the
already-reachable simp lemma `Zeta23.zetaZeroConfig_N`, and apply
`zetaNonempty_of_rvm_main`.  The price is `34` modules and `11,710` lines.

**`281` corrects what `270` and `271` said about that price.**  Both called it
*"a standing tax on every `lake build`"*.  That is wrong: `lake` caches, so the
`7m32s` is a **one-time** build.  The recurring cost is olean loading, and
measured over three runs it is `9.0s` against `9.3s` for `import Riemann` alone
— indistinguishable.  The discharge costs one build of about seven and a half
minutes and, per cycle afterwards, nothing measurable. -/
axiom zetaNonempty : ∀ᶠ T in Filter.atTop, 0 < (zetaZeroData T).N

/-- The zeros of `ζ` as a `Family` — now a **construction**, not an axiom. -/
noncomputable def zetaFamily : Family where
  D := zetaZeroData
  nonempty := zetaNonempty

/-- The zeros of `ξ'` as a `Family` (Route II). -/
axiom xiPrimeFamily : Family

/-- The close-pair functional `(2/λ)∫₀^λ 𝒩(α)dα` of the zeta zeros, as a
function of `(λ, T)`.  Declared rather than defined: defining it needs the
zero-counting integral, which is downstream of `zetaFamily`. -/
axiom closePairsZeta : ℝ → ℝ → ℝ

/-! ### Route I -/

/-- **Proposition 2 / Fujii.**  Gallagher–Mueller (Crelle 1978) with Fujii's
unconditional second moment of `Δ_U S(t)` (Trans. AMS 1974/1981), assembled
as in GLSS arXiv:2503.15449 §5–6: `(★)` holds with constant `Cbound c₀ λ` for
*some* `c₀ > 0`.  The constant is not effective — that is [OPEN 0]. -/
axiom fujii_ineffective : ∃ c₀ > 0, EffectiveFujii zetaFamily.toCounts c₀

/-- The `𝒩`-term bookkeeping of the same identity, for the zeta family.
(As a general statement over arbitrary families and arbitrary `closePairs`
functions this is false — ISSUES.md #8.) -/
axiom fujii_closePair_bookkeeping :
    ClosePairBookkeeping closePairsZeta zetaFamily

/-! ### Route II -/

/-- **zeta-23**, `Zeta23/XiPrime/Final.lean` (`xiDeriv_simple_on_line`,
sorry-free): unconditionally at least `0.85838` of the zeros of `ξ'` in
`(T, 2T]` are simple and on the critical line.

**This closes [OPEN B]** — the de-conditioning of Farmer–Gonek–Lee that the
program document calls "the most tractable gap" is already done, in the
artifact the document cites.  See ISSUES.md #2.

Stated as the proportion the paper actually proves.  It does **not** give
`(★)` for `ξ'`: Proposition 1 runs `N_sc ≥ 2N - N⊛`, so a proportion bounds
`N⊛` from *below*.  `UnconditionalFGL` is therefore carried as a hypothesis,
not asserted here (ISSUES.md #7). -/
axiom zeta23_xiPrime : xiPrimeFamily.toCounts.Proportion 0.85838

/-- **Levinson–Montgomery 1974**: the off-line zero counts of `ζ` and `ξ'`
agree up to `O(log T)`. -/
axiom levinson_montgomery : LevinsonMontgomery zetaFamily xiPrimeFamily

/-! ### External baselines

The records this project must beat.  Axioms *about the zeta family*, counted
as such in `PROPORTION.log`. -/

/-! **`baseline_przz` was deleted here, `SESSION 233`, on Joop's ruling.**

Pratt–Robles–Zaharescu–Zeindler (2019) — `41.62%` of the zeros on the critical
line, on the standard count — used to be an axiom at this position.  It is a
*consequence* of the axiom below: `ProportionStd` is monotone in its constant
(`Family.ProportionStd.mono`) and `0.4162 ≤ 0.6725`, so
`Riemann.przz_of_zeta23` derives it in one line.

Keeping both meant the trusted base asserted a fact it could prove.  The
literature record still stands and is still citable; what changed is that this
project no longer *assumes* it.  Declared axioms `9 → 8`; base `v2 → v3`; no
certified number moves, because nothing ever consumed the axiom — a repo-wide
search before deleting found it only in its own declaration and two docstrings.
-/

/-- zeta-23 (Anthropic, Aug 2026) Theorem D, formalised sorry-free in
`zeta-23-lean`: `67.25%` of the zeros are simple and on the critical line.

A placeholder for an **import**: the Lean proof exists, at toolchain
`v4.33.0-rc2` (ISSUES.md #4). -/
axiom baseline_zeta23 : zetaFamily.ProportionStd 0.6725

end Riemann
