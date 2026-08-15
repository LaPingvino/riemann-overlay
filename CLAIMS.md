# CLAIMS — every class-impossibility assertion, graded

This project's most valuable statements are of the form *"no member of class `C`
can do `X`"*. They are also the easiest kind to leave in a docstring, because
they feel settled once the argument is understood. Two were found living as
prose in three cycles (`FAILURES.md` `#10`'s rung 0, and `Gauge.lean`'s
LP-optimality), and both turned out to be true — so the risk was never that we
believed false things, but that a reader could not tell which beliefs they were
entitled to check.

This file is the inventory. **Anything cited as a bound must appear here with
grade A.**

## The three grades

* **A — certified.** A machine-checked statement quantified over the named
  class. Cite freely.
* **B — certifiable, but prose.** The class is well defined and a theorem could
  be stated; none exists yet. **This is the disease.** Cite only with the word
  "unformalised" attached.
* **C — class undefined.** The claim quantifies over something informal ("cheap
  invariants", "post-1974 technology"). It cannot be promoted without first
  defining the class, and it is **not a bound**. Never cite as one.

## The inventory

| claim | class | certificate | grade |
|---|---|---|---|
| `μ_T` cannot see `β`; `NscStd` is not an ordinate functional | `μ_T`-invariant hypotheses (closed under deduction) | `Blindness.no_muInvariant_theory_computes_NscStd`, `NscStd_not_ordinate_functional` | **A** |
| `N⊛` is depth-blind; depth-shaped input has price zero | same | `Blindness.no_muInvariant_bundle_computes_Noff`, `Fiber.blind_at_every_crowded_mass` | **A** |
| Vertical blurring cannot separate a zero from its twin (A2) | smoothing at any radius `r ≥ 0` | `Blindness.two_le_Hr_of_off_line`, `Basic.on_line_of_Hr_eq_one` | **A** |
| The blindness is supported exactly on crowded atoms; mass one is sighted | same | `Fiber.Noff_eq_zero_of_simple` + `blind_at_every_crowded_mass` | **A** |
| No functional of `μ_T` discriminates the fiber coordinate; the Landau weight does | functionals factoring through `μ_T` | `Fiber.not_discriminates_of_factors`, `landau_discriminates` | **A** |
| `prop1` is optimal among linear bounds in `(N, N⊛)` | `LinearBound a b` | `Optimal.prop1_LP_optimal` | **A** |
| Extension past the known range is useless, and fatal if the multiplier dips negative | `{F pinned on A, F ≥ 0 off A}`, `A` measurable | `Capacity.no_gain_past_known_integral`, `unbounded_below_of_neg_outside_integral` | **A** |
| `offline_le`'s `(C−1)` cannot be improved to `(C−1)/2` | the inequality itself | `Gauge.offline_le_tight` (saturating witness) | **A** |
| Route I cannot do better than `c₀ ≈ 0.16` | any effective Fujii constant | `Fujii.c0_lower_bound` | **A** |
| The bandwidth-one ceiling is `≤ 0.6818287` | bandwidth-one certificates | `Zeta23.PairCeiling.ceiling_law256` — **imported**, and *not reachable from `import Riemann`* | **A**, with a caveat parked for Joop |
| "Multiplicity bounds cannot tighten `C`" (W7, precise part) | `BoundedMult M` — `H γ ≤ M`, pure counting, no Euler product | `Optimal.prop1_LP_optimal_cheap` | **A** |
| "No free classical invariant *of any kind* will tighten `C`" (W7, general) | *"classical invariant"* — still informal | — | **C** |
| "Post-1974 extremal technology cannot buy anything through the window" | *"post-1974 technology"* — informal | — | **C** |
| E20's plane: the cleavage is the one thing no single-natured instrument can certify | *"single-natured instrument"* — informal | — | **C**, and already marked statistically unsupported in `FAILURES.md` |

## The sweep's verdict (night cycle 8)

**Kill condition, stated first:** *if the sweep finds no further uncertified
class-impossibility claims beyond the two already fixed, the "pattern" was two
coincidences and must not be generalised into doctrine.*

**It fired, in the informative direction.** Every Lean docstring's impossibility
claim is backed — `c0_lower_bound` and `offline_le_tight` are real theorems, not
prose, and I expected at least one of them not to be. **Grade B is now empty.**

The two remaining uncertified claims are **grade C, not grade B**: their classes
are informal, so they are not theorems-in-waiting but statements of a different
species. Promoting them would require *defining* "cheap invariant" and
"post-1974 technology" first, which is a research question rather than a
formalisation task.

**So the pattern does not generalise into doctrine.** What survives is narrower
and more useful: a standing inventory, and the rule that a claim cited as a
bound must be grade A. The disease was real, finite, and is now cured; what
remains is a category that was never curable by formalisation and must instead
be *marked*.


## Amendment (night cycle 9) — grade C is not a life sentence

`CLAIMS.md` asserted, one cycle ago, that promoting a grade-C claim "would
require *defining* the class first, which is a research question rather than a
formalisation task". **For W7 that took one cycle.**

Every constraint in the cheap family has the same shape — an upper bound on
horizontal multiplicity — and that shape is pure counting with no multiplicative
input. `BoundedMult M D := ∀ γ, D.H γ ≤ M` is the class, and
`Optimal.prop1_LP_optimal_cheap` proves that assuming *any* such bound
(`M ≥ 2`) leaves the two-moment optimum at `2 − C`. The binding configurations
have `H ≤ 2`, so the cheap invariants are satisfied by construction and cannot
bind — which is exactly what the autopsy said, now as a theorem.

**Scope, stated plainly:** this certifies the vacuity of *multiplicity bounds*
for *this* extremal problem. The wider claim — that no classical invariant of
any kind tightens `C` — quantifies over a class still undefined and stays C.

**Revised guidance:** grade C means *the class has not been defined yet*, not
*the class cannot be defined*. When a C entry's claims all share one shape, that
shape is usually the definition. Filed as `SURPRISES` S23.
