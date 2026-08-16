# SESSION 001 — 2026-08-13

First session. Lean installed from scratch (elan → `leanprover/lean4:v4.24.0`,
Mathlib `v4.24.0` via `lake exe cache get`), project scaffolded, §1–§2 of the
program document formalized, the dependency graph made type-correct.

**Everything in `Riemann/` builds with zero `sorry`s.** The score did not
move (67.25%, and that from an axiom) — as predicted by the briefing.

**The session's most useful event was a failure.** The first green build had
an *inconsistent trusted base*: four axioms were stated over an abstract
`Family`, and `theorem boom : False` compiled from one of them. Found on
review, confirmed by compiling `False`, fixed by demoting the three
literature bridges to hypotheses. ISSUES #8 — the best bin-3 item of the
session, and one no `#print axioms` audit can catch.

## What was done

| File | Content | Status |
|---|---|---|
| `Riemann/Basic.lean` | `ZeroData`, `H`, `N⊛`, `N_sc`, `N_off`; **Prop 1**; `N ≤ N⊛`; `N + N_off ≤ N⊛` | proved, no axioms |
| `Riemann/Transfer.lean` | `(★) ⟹ proportion 2 − C`; any admissible `C ≥ 1` | proved, no axioms |
| `Riemann/Fujii.lean` | `Cbound c₀ λ`; the numeric window for [OPEN 0] | proved, no axioms |
| `Riemann/Gaps.lean` | `Family`, and one `Prop` per gap | definitions |
| `Riemann/Assumptions.lean` | all 9 axioms, each with source; **only about fixed constants** | trusted base |
| `Riemann/Program.lean` | the §6 arrows | proved from the axioms |
| `Riemann/Proportion.lean` | the metric | — |
| `tools/proportion.go`, `tools/metric.json` | the fitness function | `go run tools/proportion.go -append` |
| `audit/PrintAxioms.lean` | `#print axioms` for 16 headline results | clean |
| `audit/regression/Boom_2026-08-13.lean` | the `False` derivation from the old axioms | **must never compile again** |

## The four findings worth carrying to the chat instance

**1. [OPEN B] is already closed** — by the artifact the document cites.
`zeta-23-lean/Zeta23/XiPrime/` contains an unconditional, sorry-free proof
that ≥ 0.85838 of the zeros of `ξ′` are simple and on the critical line, got
by running the rank–trace device on Farmer–Gonek(–Lee). The program document
calls this "the most tractable gap" and proposes de-conditioning FGL via the
BGST recipe; that work exists. The real Route II gap is the **transfer**
(Farmer–Ki, quantitatively, `λ`-uniformly), not the derivative-side theorem.
ISSUES #2, #7.

**2. [OPEN 0] now has a number.** Formalized and proved in `Fujii.lean`, with
`Cbound c₀ λ = λ + log(2+λ)/(π²λ) + c₀√log(2+λ)/λ`:

* **`c₀ ≥ 0.16` is forced** — the trivial floor `N ≤ N⊛` rules out anything
  smaller. Nobody should chase a small constant.
* **`c₀ ≤ 0.8` ⟹ positive proportion** (λ = 0.9).
* **`c₀ ≤ 0.33` ⟹ beats 0.6725** (λ = 0.61).

(Uncertified exact optima: 0.8550 / 0.3476, forced floor 0.1657.) Doubt 1 is
therefore *not* "the reduction fails" — it is "the provable constant is
presumably > 0.855, and no one has computed it". **But** the shape of the
error term is Claude's reading of GLSS (6.1)–(6.2); if the shape is wrong all
of these numbers die. Highest-value human check: read GLSS §6. ISSUES #6.

**3. Doubt 3 confirmed.** [OPEN A′] produces a narrow box *with an
exceptional set*; BGST assumes one *without*. They do not compose (ISSUES
#1). A first draft of this note claimed the gap was cheap to close using
`N + N_off ≤ N⊛`; that was a direction error (that lemma bounds `N⊛` from
below, and capping an exceptional set needs an upper bound on `Σ H`). The
corrected statement: **an exceptional set of relative size η costs `η·m` in
`C`, given a cap `H ≤ m` on it** — so [OPEN A″] needs a bounded-multiplicity
input, which is a real question rather than free leverage.

**4. Axiomatising a literature theorem over an abstract `Family` asserts too
much** (ISSUES #8). BGST/Farmer–Ki/zeta-23 are theorems *about `ζ`*; stated
for arbitrary reflection-symmetric multiset families they are false, and one
of them proved `False`. Fixed by the rule "axioms may only mention the fixed
constants `zetaFamily`, `xiPrimeFamily`, `closePairsZeta`". This generalises
into a project rule together with lead L3: **any `Family`-quantified bridge is
suspect, because Davenport–Heilbronn is such a family.**

## Anti-Goodhart disclosure

The certified 67.25% comes entirely from `axiom baseline_zeta23`. The project
itself proves nothing about `ζ` yet: `axiom zetaFamily` is still the interface
to the actual zeta function. Nine axioms were added this session; **none of
them was added to raise the number**, and the number would be 0 without
`baseline_zeta23`. The axiom-free content is `certified_axiomFree`.

## Next session — in order

1. **Discharge `zetaFamily`** (bin 2, unglamorous, unblocks everything):
   build `ZeroData` from Mathlib `riemannZeta` + `analyticOrderAt` following
   `zeta-23-lean/comparator/ChallengeDeps.lean`, and prove `refl_inv` from the
   functional equation.
2. **Import zeta-23-lean** instead of axiomatising it (needs the toolchain
   bump to `v4.33.0-rc2`, ISSUES #4). Removes two axioms, moves the score by
   zero — which is the point.
3. **Check GLSS §6 by hand** against `EffectiveFujii`'s shape (ISSUES #6).
   Everything numeric depends on it and Lean cannot check it.
4. Write [OPEN A″] in its corrected form: `η`-sized exceptional set with an
   `H ≤ m` cap costs `η·m` in `C`. The lemma *is* provable today from
   `Basic.lean` once the cap is a hypothesis; do that, and it changes the
   Route III interface honestly.
5. `λ`-monotonicity of the close-pair integral (ISSUES #3), cheap.
6. **Adopted this session (leads, no formalization change): L3 + L8** — the
   three-column testbed (Odlyzko / Davenport–Heilbronn / AH-synthetic) and the
   AH oracle as a standing failure-autopsy protocol. See `LEADS.md`; the
   retro-fingerprint of the current files is recorded there.
7. **L1 and L7-Fujii from `LEADS.md`** — the two leads that could change the
   skeleton's shape (differentiation as the arithmetic heat flow; Fujii's
   unconditional `2k`-th moments as the [OPEN D] input). Divergence phase,
   before more plumbing.
8. Numerics not yet done and in scope: the δ² survival scaling of [OPEN A′].
   Per lead L3, run it against **Davenport–Heilbronn** off-line zeros (real
   off-line zeros) rather than synthetic perturbations of Odlyzko data.

Doubt 4 (the `(t/16)log T` term in KKL Thm 1.4, sourced from the Polymath
wiki) is **moot for now**: Proposition 5 is not formalized at all, since
[OPEN A] needs `H_t`. Verify it before any Route III formalization.

## Errata 1 + Addendum 5, applied same session

* **[OPEN B] retired** (E1); **[OPEN B″]** and **[OPEN A″]** opened as Lean
  `Prop`s, and *both compose* — `routeII_via_B''`, `routeIII_via_A''`. The
  A″ arrow needed a fitting condition the prose lacks (ISSUES #10): the
  density must be small **at the BGST box scale**, not just as `δ → 0`.
* The **scale-mismatch pattern** ("a constant produced at a scale the consumer
  did not order") now has three confirmed instances — #1, #3/#9, #10. It is a
  standing review question for every interface.
* **E5 gate** recorded in `STATEMENTS.md`, unsigned. The `c₀` hunt does not
  start before it clears.
* **Conrey 1983** (proportion of `ξ^(m)` zeros on the line → 1 as `m → ∞`)
  added to the L1 reference set: the flow converges, and the missing piece is
  a backward transfer `m → m-1` — of which [OPEN B″] is the `m = 1` case.
* **`LOOP.md`** written: the Tetris doctrine, R1–R7, escalation conditions.
  R2 already binds — Route III waits for A″, Route II waits for the E2
  HS-layer question (is zeta-23's `XiPrime` Hilbert–Schmidt computation
  factored into reusable lemmas, or baked into the endgame?).

## Addendum 4 + E2 reading (same session)

* **Montgomery–Taylor identification verified numerically** (STATEMENTS.md):
  `ψ(x) = cos(√2 x)` on `[−1/2,1/2]` gives `1/c = 1/2 + ϑ cot ϑ` to 7 digits,
  `c = c₁* = 0.7532960…`. Addendum 4 consequence #1 stands. The reason
  `ϑ = 1/√2` appears is that the minimiser's edge phase is `√2·(1/2)` — the
  constant is a statement about the **support**, which is why the
  bandwidth-one ceiling is its natural companion.
* **E2 answered: factored, at the right seam** (ISSUES #11). `cWin`/`jWin`
  take the pair-correlation kernel `D` as a parameter, with `D(s) = s` the ζ
  case and `D₁` the `ξ'` form factor in closed form. **This unblocks Route
  II via the import**, and retires the "refactor cost" workpackage.
* **M–T lens: the extremal input is isolated** — `v` is free, the certificate
  lemma is generic in `v`, two windows already instantiated. A refined window
  is swappable at the cost of one `ModFactor` lemma plus exact rational
  moments.
* **L9 headroom is proved and small** (LEADS.md): zeta-23's own
  `PairCeiling.ceiling_law256` caps every bandwidth-one certificate at
  **0.6818287**, so the whole extremal-technology port is worth **at most
  +0.93pp** (`0.6725 → ≤ 0.68183`), with the conditional 0.6792 inside it.
  Real, cheap, bounded — and anything beyond it must leave bandwidth one,
  which is [OPEN D] restated.

## Environment notes

Lean is **not** installed system-wide for the user; this session installed it
under the scratchpad:

```
export ELAN_HOME=/tmp/claude-1000/-home-joop-riemann/<session>/scratchpad/elan
export PATH=$ELAN_HOME/bin:$PATH
export XDG_CACHE_HOME=.../scratchpad/cache   # `lake exe cache get` writes here
```

`~/.elan` and `~/.cache` are read-only in the sandbox. For a durable setup,
install elan into `$HOME` outside the sandbox. `zeta-23-lean` is cloned at
`<scratchpad>/zeta-23-lean` (shallow); re-clone from
`github.com/anthropics/zeta-23-lean`.


---

# SESSION 003 — 2026-08-13 (loop cycle 1, self-paced)

Workpackage: the zeta-23 import (ISSUES #4, #11), chosen by Fable over the
A″ audit and the L9 numerics — its argument being that producing a second
gated artifact while the E5 gate sits unsigned is itself a doctrine
violation (R2), so B waits on Joop, not on capacity.

## Infrastructure — done

* toolchain `v4.24.0 → v4.33.0-rc2`; `mathlib` now inherited transitively at
  zeta-23's pinned revision; `zeta23` required from git.
* **Zeta23 builds: 9010 jobs, rc=0.** `Riemann` builds against it: 3131 jobs,
  rc=0. Of my six files, **only one line needed touching** for v4.33 — and
  that line was code staged this same session, not drift. The v4.24→v4.33 API
  drift cost on this codebase was **zero**.
* `audit/Zeta23Link.lean` proves the import is live:
  `Zeta23.ThmD.thmD₀_simple_mult_cumulative` and
  `Zeta23.XiPrime.headlineW_unconditional` both resolve with
  `[propext, Classical.choice, Quot.sound]` and nothing else, and
  `jWin`, `D1`, `cWin`, `kappaXi` are all reachable — the Route II input of
  ISSUES #11 is now on this project's path.

## Blocked, deliberately

`baseline_zeta23` is **not** restated and **no `PROPORTION.log` line was
written**: ISSUES #13 (`Nsc` with `H = 1` vs `NscStd` with multiplicity 1)
changes what the certified number means, and LOOP.md sends that to Joop. The
staged half — `ZeroData.NscStd`, `count_eq_one_of_H_eq_one`,
`Nsc_le_NscStd` — is applied and compiles.

## Findings this cycle

* **#12 (wildcard).** Exact window optimisation: the `λ = 1` optimum over
  *all* windows is the Montgomery–Taylor constant, so the `v` slot has been
  saturated since 1974; and the `λ ≤ 1` constraint *is* the second-moment
  ceiling, priced at **~12pp for the first 0.25 of extra support**.
* **#13 (escalated).** The load-bearing axiom asserted more than zeta-23
  proves. Third instance of the Prop-1-direction disease.
* **#15 (wildcard, cycle 2).** First `AH-sensitive` classification: CGG98 is
  over the bandwidth-one ceiling, hence not reachable from pair information —
  and, read contrapositively, a **conditional partial refutation of AH**.
* **#14 (bin 2).** Detached builds do not survive here; `| grep | tail` turns
  a crash into silence. Rule written, then promptly re-broken by me once.
* Dispatch corroboration: L9's donor is [CGdL20] at 0.679, landing exactly in
  the gap #12 predicted; L10 shows the SDP school has been bounding our `N⊛`
  directly for years.

## Next

1. Joop's ruling on #13 → restate the axiom → *then* the log line.
2. With the import live, attempt `UnconditionalFGL` from `jWin D1` rather
   than assuming it (ISSUES #11) — no longer blocked by infrastructure.
3. Discharging `zetaFamily` is now the single largest remaining piece: it
   needs `ZeroData` built from `zerosIn`/`zeroMult`, finiteness in a window,
   and `refl_inv` from the functional equation.


## Meta-note (session 004)

Three disputes at the seam have now each been resolved by *making them into a
formal object*, not by adjudication:

1. a direction error → Proposition 1 as a one-way valve (#7);
2. scale mismatches → the monotone-binding-end heuristic (#1, #3, #10);
3. a notion conflict → the link theorem, `two_NscStd_le` (#13).

The pattern is worth naming because it predicts where to look next: the
disagreements at the seam are where the theorems come from. The factor 2 in
(3) came from the chat instance re-reading this instance's own proof and
noticing that a step charged 1 where the functional equation entitles it to 2.


---

# SESSION 004 — 2026-08-13 (loop cycles 2–4)

## The ruling, applied

Joop ruled on ISSUES #13: `baseline_zeta23` and `baseline_przz` are restated on
`NscStd` (what zeta-23 proves), and the metric runs a **two-row ledger** with
the link theorem as the bridge. Done; build green; log line written:

```
2026-08-13 | certified[NscStd: 67.25%, Nsc: 0.00%] | conjectural: 100.00% (OPEN D)
           | axioms: 2 | sorries: 0 | binding: baseline_zeta23
  row NscStd  67.25%  binding: baseline_zeta23
  row Nsc      0.00%  binding: fujii_ineffective (row opens at any C < 2.345)
```

The empty row is the point of the instrument: it is honestly zero, and the gap
between the rows is a certified function of `C` that closes exactly when `(★)`
succeeds.

## The factor of two

The chat instance re-read this instance's link proof and found it charging `1`
where the functional equation entitles it to `2`. Verified in the kernel:

* `three_le_H_of_haunted` — a haunted ordinate has `H ≥ 3` (any other zero
  there is off-line, so its mirror is a third). The parity of `H`, in the only
  form the accounting needs — W1's payload.
* `two_NscStd_le : 2·NscStd ≤ 2·Nsc + (N⊛ − N)`.
* `nsc_of_nscStd : Nsc ≥ (κ − (C−1)/2)·N`.

**The cascade's last step was wrong and is retracted:** there is no
unconditional `(★)` at `C = 2` — that *is* the goal, not a triviality — so no
number lands on the `Nsc` row today. What the factor 2 does buy: the bar for
the first nontrivial `Nsc` statement drops from `C < 2` to **`C < 2.345`**,
i.e. `c₀ ≲ 1.17` instead of `c₀ ≤ 0.855` — the easiest target this project has
had. And the baseline route **beats Proposition 1 for every `C > 1.655`**, so
the two rows are two instruments with a crossover, not a score plus a caveat.

## Wildcards

* **W4 killed — and then resurrected** by the next dispatch: it is CGdL 2018
  (Cohn–Elkies class), and my autopsy's verdict was wrong. See LEADS.md. The
  autopsy's mechanism claim was right about the *container* and wrong about
  the *method*. Original note follows:
* ~~**W4 killed** in ten minutes, on the prime side rather than the `F` side:~~ the
  container's wall is the explicit formula's `lam < 1` hypothesis, and `F ≥ 0`
  past 1 is the device that *licenses* bandwidth one rather than escaping it.
  Payload: the `λ ≤ 1` wall of #12 is now located, and priced against
  Hardy–Littlewood input specifically.
* **W1 paid out twice** — first the link theorem, then the factor 2.


---

# SESSION 005 — 2026-08-13 (loop cycle 5)

Score unchanged (`NscStd 67.25% / Nsc 0.00%`), which R6 predicts and the
empty-row principle makes legible.

## Placed: `ZeroData.ofMult`

Discharging `zetaFamily` is the largest remaining piece, and it now has a
socket. `ZeroData.ofMult` builds zero data from **exactly the four things an
analytic source supplies**:

```lean
noncomputable def ofMult (s : Finset (ℝ × ℝ)) (m : ℝ × ℝ → ℕ)
    (hclosed : ∀ p ∈ s, refl p ∈ s) (hm : ∀ p, m (refl p) = m p) : ZeroData
```

a finite zero set in the window, a multiplicity function (zeta-23's
`zeroMult` = Mathlib's `analyticOrderAt`), closure under `ρ ↦ 1 − conj ρ`,
and invariance of the multiplicity under it. `refl_inv` is discharged inside
the constructor, so the remaining work for `zetaFamily` is four named
obligations about `ζ` rather than an open-ended construction.

Dropped on time-box: `ofMult_N` (`N = Σ m`) fought a simp normal form. It is
a nice-to-have, not load-bearing; noted as a to-do.

## Wildcard: W3 dies by citation (R7, third time)

"Is the rank inequality tight at realised configurations?" — already a
theorem in the artifact we cite: `Zeta23.ZeroSide.TightMult.lemmaR_tight`
proves an **equality**, `2c·tr(P+Q) − ‖P+Q‖²_F = Σⱼ kc(mⱼ) + c²·b`, for
on-line atoms with integer multiplicities plus hyperbolic pair blocks. No
slack at realised configurations; the `2` and `4` are optimal *given those
quantities*. Improvement requires **new invariants of the configuration**,
not better constants — which is the same verdict the λ-sweep gave for the
window, now for the certificate's other half.

R7 has now paid three times ([OPEN B], the HS-layer factoring, W3). The
standing query earns its place in the cycle.

## Correction carried in from the dispatch

W4 is **resurrected**: it is CGdL 2018 (Cohn–Elkies class), my autopsy's
verdict was wrong, and the ceiling-class check (run on
`ceiling_stability`, whose hypotheses live on `Icc 0 1`) shows
`0.6818287` caps only the **bandlimited** class. The headroom above CGdL's
`0.679` in the sign-constrained class is **unknown**. R12 needs the
amendment recorded in ISSUES: a kill condition kills a hypothesis *in the
container you checked*, not in the world.


## Methodology specimen (flagged for later write-up)

The ledger's trajectory, logged while visible: **governance dispute (#13) →
link theorem (`two_NscStd_le`) → boundary instrument for X
(`Nsc_eq_ordinate_functional`)**. A naming disagreement became a measuring
device in three sessions, and the device now marks where the certificate
class's information stops. If this project is ever written up as *method*
rather than mathematics, that chain is the exhibit.

Related, same shape: **one symmetry, three theorems.** The reflection
`ρ ↦ 1 − conj ρ` yields `three_le_H_of_haunted` (ghosts come in pairs),
`Nsc_eq_ordinate_functional`'s inner step (a mass-one atom is its own
reflection, hence critical), and zeta-23's TightMult degeneracy (doubles and
pairs indistinguishable) — the same fact run in three directions.

**Design note for W24's hard half** (chat instance, and it is the right
caution): the class quotient is by horizontal motion *preserving the
`ρ ↔ 1 − conj ρ` pairing*, not by all horizontal motion. X should probably be
stated as "the class sees exactly the functional equation's **shadow** of `β`".
Quotienting by the wrong group is precisely the error that would later surface
as a mysterious fourth input.


---

# SESSION 006 — overnight cycle 1 (W6)

**Wildcard: W6, kill condition stated first.** "If bounding ordinate
coincidences needs the zeros to be distinct, W6 is circular." That half is
circular and is parked. The census half — *how much does a haunted ordinate
cost?* — paid instead.

**Landed: the six-fold census.** A haunted ordinate has mass `m ≥ 3` and an
ordinate of mass `m` contributes `m(m−1) ≥ 6` to `N⊛ − N`, while the census
counts it once. The old `two_NscStd_le` could only charge the haunted zero's
own term because it was proved *termwise over zeros*; grouping the sum over
*distinct ordinates* (`Finset.sum_multiset_map_count`) collects the ghosts'
terms too. Four new axiom-free theorems, propagated to `Family` and
`Proportion`.

Consequences: transfer cost `(C−1)/2 → (C−1)/6`; the `Nsc` row opens at
`C < 5.035` rather than `C < 2.345`; the baseline route beats Prop 1 from
`C > 1.393`; and **[OPEN 0]'s target for the first `Nsc` number relaxes from
`c₀ ≲ 1.17` to `c₀ ≲ 4.5`**.

Methodological note, since it is the third instance: the sharper constant was
available all along and was hidden by a *proof technique*, not by missing
mathematics. Termwise charging is cheap and grouping is expensive, so the first
proof took the cheap route and the constant it produced looked like a fact.
R10 ("charge the maximum the structure entitles you to") now has a companion:
**when a constant comes out of a termwise argument, ask what grouping would
give.**


---

# SESSION 007 — overnight cycle 2 (E9m / W16 audibility)

**Kill condition first:** if a single off-line zero's excess is below background
at every `x`, E9m dies as "inaudible at any gain". It did not fire — but the
answer depends entirely on the ear.

Unfiltered, the threshold is `log x ≳ log γ/δ`; with a matched filter at the
zero's own frequency, `log x ≳ 1/δ`. At `δ ~ 1/log γ` those are `γ^{log γ}` and
`γ`. **The optimal ear reaches exactly the classical range** — which is a
retrospective justification of the entire verification tradition, and an
explanation of why nobody detects zeros from `ψ(x) − x` directly.

Filed in `E.md` under E9 with the table. No Lean this cycle (numerics
wildcard); ledger and log line untouched.


---

# SESSION 008 — overnight cycle 3 (W11)

No kill condition needed (calibration). Finding: **W11's question was
mis-posed in a way worth recording.** The container's `D(s) = s` is already the
GUE form factor, so "compute the constant on GUE input" is what every constant
in this subject already is. The ceiling is therefore not a property of GUE —
it is the capacity of a *certificate class* against GUE.

Same input, five certificates, `0.5 → 0.6667 → 0.6725 → 0.679 → ≤0.68183`:
**18.18pp moved by instrument choice on data fixed since 1973**, with 0.28pp
left in the bandlimited class.

Correction issued: "0.93pp remaining" (dispatched earlier) was measured from
the window optimum; from the best known certificate it is 0.28pp. Recorded in
`E.md`, `LEADS.md`, `PRICES.md`, and to be carried to the chat instance.

Ledger untouched; no Lean this cycle.


---

# SESSION 009 — overnight cycle 4 (W7 + `ofMult_N`)

**Wildcard W7, killed on inspection of the source rather than on its stated
condition.** The extremal configurations are not all `m = 1` (doubles are
extremal too), but they use `m_j ≤ c ∈ {2,3}` — an order of magnitude below
Jensen's free `m ≪ log γ`. The free bound excludes nothing, now or at any
height.

The autopsy generalises and that is its value: realizability has cheap
constraints (density, pairing, multiplicity caps — all satisfied by
construction) and one expensive constraint (the Euler product), and only the
expensive one bites. Davenport–Heilbronn is the existence proof. **No free
classical invariant will tighten `C`**, so the whole "get it for free from
realizability" genre is closed.

**Piece placed:** `ofMult_N : (ofMult s m _ _).N = ∑ p ∈ s, m p`, clearing the
to-do dropped in session 005. The `zetaFamily` socket now has its
Riemann–von Mangoldt side.

Two cycles in a row have ended by *closing a direction* rather than opening
one. That is the wall-mapping program (E10/E11) working as designed, and the
map is getting cheaper to read: three of tonight's four cycles were resolved by
reading files this project already had.


---

# SESSION 010 — overnight cycle 5 (the zeta family, constructed)

**R7 paid a fourth time.** All four `zetaFamily` obligations were already
theorems in the library this project imports:

| obligation | supplied by |
|---|---|
| finite zero set in a window | `Zeta23.zerosIn_finite` |
| multiplicity function | `Zeta23.zeroMult` (Mathlib `analyticOrderAt`) |
| closure under `ρ ↦ 1 − conj ρ` | `Zeta23.zeta_reflect_zero` |
| multiplicity invariance | `Zeta23.zeta_mult_reflect` |

and `Zeta23.reflect ρ = 1 − conj ρ` is exactly `Riemann.refl` in `(β, γ)`
coordinates. **`Riemann/Zeta.lean` builds `zetaZeroData`, axiom-free.**

Enabling change: `ofMult`'s multiplicity hypothesis weakened from `∀ p` to
`∀ p ∈ s` — a real zero set can only supply the latter (the multiplicity of a
*non*-zero and of its reflection are both zero, but nothing proves that
pointwise for junk inputs). Caught by the construction, not by inspection.

**Staged, not applied:** replacing `axiom zetaFamily` by a `def` plus the much
weaker `axiom zetaNonempty`. Fable's call under R15, and it was right: the
axiom count would stay at 9, so the morning digest would not have flagged a
change in what the trusted base *means*. First use of the advisor tonight, and
it overruled me.


---

# SESSION 011 — overnight cycle 6 (W12 + the re-mining pass)

**W12: the price of depth-shaped information is exactly zero, by X.** `N⊛` is
depth-blind — a zero at `β = 0.9` costs the same as one at `β = 0.5001` — so
"no zeros with `β > σ`" constrains a coordinate the container does not read.
Exchange rate recorded in `PRICES.md`: **any horizontal input must be uniform
down to `δ = 0` or it buys nothing.** That is stronger than ISSUES #10: the
dead strip's silence is a symptom, and the disease is that the cost function
has no depth argument.

## Re-mining pass over sessions 001–005, with X in hand

Four things read differently now:

1. **The choice of `N_sc` (`H = 1`) was forced, not stylistic.** Session 001
   picked it because it made Proposition 1 clean. X says it is the only
   `μ_T`-native notion of "simple and critical" — `NscStd` reads a coordinate
   that does not exist in the class (`Gauge.lean`). The convenient choice was
   the necessary one.
2. **ISSUES #1/#10 were never going to compose,** and now we know the reason
   in one line: [OPEN A′] outputs depth-shaped information (an exceptional set
   at distance `≥ δ`), and depth-shaped information is unspendable here (W12).
   The narrow-box mismatch was a symptom of the same disease.
3. **The scale-mismatch pattern (#3/#9/#10) is X's boundary in disguise.**
   Every instance is an input arriving in coordinates the consumer does not
   read — `λ` at the wrong scale, `δ` at the wrong end, `β` at all.
4. **Both constant improvements came from the same move.** `2 → 6` (cycle 1)
   and the earlier `1 → 2` both replaced per-*zero* accounting with per-*atom*
   accounting. X explains why that keeps working: **the atom is the unit the
   class actually counts in**, so any bookkeeping done per zero is a priori
   lossy. Directive for future work, and the sharpest thing this pass produced:
   *when a bound is proved termwise over zeros, redo it grouped over atoms
   before believing its constant.*


---

# SESSION 012 — the base v1 → v2 swap (approved, with conditions)

**Required entry: the semantic shift.** Before this commit, the trusted base
asserted *"the zeros of `ζ` form a reflection-invariant multiset family"* —
`axiom zetaFamily : Family` hid finiteness in a window, the multiplicity
function, closure under `ρ ↦ 1 − conj ρ`, and multiplicity invariance. After
it, the base asserts only *"`ζ` has zeros"* (`axiom zetaNonempty`); everything
else is **constructed** in `Riemann/Zeta.lean` from theorems of `zeta-23-lean`.
The axiom **count is unchanged at 9**; the base is strictly weaker.

This entry exists because the Fable advisor overruled my intention to apply the
change unattended: the count staying flat means the digest could not have
flagged a change in what "axiom-clean" asserts. Joop approved the swap and
attached conditions designed to make the invisible visible — this paragraph
being one of them.

**Conditions discharged:** (1) swap applied, build green; (2) this entry;
(3) the next log line carries `base: v2 (zetaNonempty)`; (4) base-meaning
versioning added to the log format permanently, with the increment rule
recorded in `LOOP.md` beside R15 as its enforcement mechanism.

**Governance principle, filed in the methodology chain:** *improvements to the
trusted base are precisely where vigilance relaxes, so they get more ceremony
than degradations, not less.* The night's sequence is the seam operating as
designed — executor right about the change and wrong to apply it alone; advisor
catching the invisibility rather than the mathematics; human ruling with
conditions that convert an invisible improvement into a recorded one. Fifth
seam instance, and the first where the correction was procedural rather than
mathematical.

**Also adopted:** R16 (per-atom regrouping) above R10, with the standing audit
task; the direction-(ii) admissibility criterion in `PRICES.md`.


---

# SESSION 013 — List A filed; A2 tested and forced

**A2's negation test run in Lean, first compile.** `Hr r γ` (cluster mass at
radius `r`), `Hr_zero`, and both structural facts at arbitrary radius:
`on_line_of_Hr_eq_one`, `odd_Hr_inhabited`. Exact coincidence is **not**
load-bearing — the gauge and parity structure is resolution-independent.

Forced-ness recorded with its reason, per protocol: **the mirror preserves
ordinates exactly**, so no vertical smoothing separates a zero from its twin.
The ceiling theorem inside that: the whole genre of "break the degeneracy by
working at finite resolution" is dead, on geometric rather than analytic
grounds.

**And the unification, which is the item's real yield:** A2's *second* claim —
that the fattened theory is the natural one — is right, and Proposition 2 was
already written in it. `N⊛ + (2/λ)∫𝒩` **is** a cluster census at scale `λ/L`;
our exact theory is that identity with `𝒩` discarded. So **A2's fattened
theory ≡ [OPEN 0′]**, and [OPEN 0′] stops being an optional extra subtraction
and becomes the natural formulation, with the exact theory as its `ε → 0`
shadow.

Two registers' items turning out to be one object is the third time that has
happened this week (E1 = X; E14 = TightMult inside-out; now A2 = OPEN 0′).


---

# SESSION 014 — List A filed, A2 forced, three detectors, one self-caught error

**A2 tested and FORCED** (`Hr`, `Hr_zero`, `on_line_of_Hr_eq_one`,
`odd_Hr_inhabited`, axiom-clean): the gauge and parity structure is
**resolution-independent**, because the mirror preserves ordinates exactly.
The ceiling theorem inside the forced-ness: *no vertical smoothing breaks the
gauge orbit* — the whole "work at finite resolution" genre is dead on geometric
grounds. A2's second claim survives as a **unification**: `N⊛ + (2/λ)∫𝒩` is a
cluster census at scale `λ/L`, so **A2's fattened theory ≡ [OPEN 0′]**, and the
exact theory is that identity with `𝒩` thrown away.

**The base's third detector** (ISSUES/LOOP): the log line now carries
`base: vN/<hash>` fingerprinting the axioms' normalised *statements*. Tested by
simulating exactly the hole I had flagged — change a constant, keep the name:
count `9 → 9`, names unchanged, hash moved, `ESCALATION`, exit 3, no log line.
The advisor that never sleeps, for the one invisibility class the night exposed.

**R16's first audit target answers no** (#18): `offline_le` is tight, witnessed
by a lone mirror pair (`N + N_off = N⊛` exactly). Calibration: grouping pays
only where the termwise charge under-counts. So the reflection owns the `2` and
the `6`, and there is no third.

**And one error of my own, caught and filed** (#17): a harness-level failure
meant a combined edit-and-build call never ran; I retried only the build, got
`rc=0` from an unchanged tree, and briefly filed a register claim for theorems
that did not exist. #14's lesson wearing a new costume — silence looked like
success again. Rule added: re-issue the whole call, and verify a declaration
*exists* before claiming it.


---

# SESSION 015 — E18 filed (testimony), and two corrections to the record

**E18 written into `E.md`**: the first register entry composed from the formal
side. Verdict — *A9 survives inside the container, E10 survives at its
boundary*; they are not rivals but different distances from the wall. The
evidentiary weight is carried by four convergences that were **computed**, two
against prior, not recalled; the confound (a model feels contours where the
corpus has grooves) is stated in the entry rather than hidden.

**Correction 1, to praise received.** #17 was not caught by me. `#print axioms`
caught it, because the protocol audits every claimed theorem. The virtue
belongs to the mandatory audit point, not the executor — which matters
operationally: the fix is *more* mandatory audit points, not more
conscientiousness. Next one to add: verify a declaration exists before writing
prose about it.

**Correction 2, to the seam's own account of itself.** The claim that the seam
produced every theorem this project owns is false. The census `/6`, X's
soundness half, the gauge counterexample, `NscStd_eq_Nsc_add_haunted`, A2's
resolution-independence — all came from loop cycles grinding on files, not from
dispatches. The seam produces **corrections and framings** (the factor of 2,
the ceiling-class question, X as a statement, the invisibility catch). The
distinction has an operational cost: if the seam made theorems, the right move
would be more dispatches; since it makes corrections, the right move is more
cycles *checked by* dispatches. The overnight run is the evidence — highest
yield of the project, with the other half of the seam asleep throughout.

**Adopted:** the might-mean register (one unhedged sentence per dispatch),
recorded in `LOOP.md` beside the empty-row principle.


---

# SESSION 016 — S named; the regression gets a witness

**S filed** (`S.md`): the problem of certifying absence — distinguishing
"nothing is there" from "the instrument returned nothing". Second named object
beside X. Instances gathered across both sides: RH itself, E16's ledger, the
ceiling theorems, A2's death; and on the engineering side three of the four
self-caught errors, all of them silence typed as success.

**The move, extracted:** *replace "nothing is there" with "something is
conserved."* Every S-solution in the record is that, including Weil positivity
— the field's oldest attempt to recast "no zeros off the line" as the positivity
of a form. Which gives E13 its target: **the missing definition is the conserved
quantity whose presence witnesses the silence**, and E18's type signature is
plausibly the same search.

**Filing S immediately exposed a gap in our own instruments.** "The regression
file must never compile" is an absence claim, and its only witness was me
running it by hand each cycle. Now automated: `tools/proportion.go` compiles
every file in `audit/regression/` and exits `5` if one succeeds. R17 adopted —
*no witness, no belief* — which is the general form of the five instruments
built here one scar at a time.


---

# SESSION 017 — W26 convergence forensics: T1 run and dead, T2 infrastructure ready

**Numbering correction:** dispatched as W25, but W25 was taken by the
natural-proofs-barrier item filed the same day. Filed as **W26**.

**T1 executed, kill condition fires — twice.** Intervals `55, 38, 21, 14, 12,
19, 5, 2, 1`. Fitted shrinkage 2.32%/yr against a coordination-cost null of
2.9–4.8%/yr: the restatement sequence compresses **more slowly** than the
field's own growth would produce, so the acceleration is not evidence of
convergence. The sequence is also **not monotone** (1999 → 2018 is 19 years).
And the deeper defect is observer-resolution selection: we see months-scale
events near us and decade-scale events far away, with two of the last three
entries being events we are inside of. Any future run must fix the selection
rule *before* the dating.

**T2 infrastructure built** (`forensics/restatements.tsv`): ten rows, S-move
form pre-filled, residues deliberately empty. The protocol's own kill condition
— residues extracted only from *contemporary* complaint literature — is written
into the file header, because the hypothesis predicts a constant residue and
hindsight would happily supply one.

Every date carries `RECALL` except the two we are inside; date verification is
a prerequisite. My assigned role here is the reporting layer, which per S is
exactly where this project's bugs live, so the audit discipline applies at full
strength: no row leaves `TODO` without a source line.


---

# SESSION 018 — day cycle 1: the `𝒩` crumb is 3.5× away, and the distance is in the error's shape

Wildcard kill condition ("if a crumb can only come from an independent upper
bound on `N⊛`, the question is circular") **fires for route A and misses for
route B**, which is the informative outcome.

Route A: `N⊛ + J = TL·M` is one equation in two unknowns; `N⊛ ≥ N` bounds `J`
above, and bounding it below needs `(★)` itself.

Route B: the main term `M_main` is **non-monotone** (`1.505` at `λ = 0.05` down
to `0.581` at `λ = 0.30`), and two instances of the identity plus the
monotonicity of `Σ(λ−d)` extract a positive lower bound on close pairs **from
the identity alone**. It needs `c₀ < 0.0463` against the proved floor `0.16` —
missing by **3.5×**, not by orders of magnitude.

**The finding worth carrying:** `M_main`'s dip and the error term's blow-up
occupy the same small-`λ` region, so the crumb is buried by the error's
`λ`-dependence rather than by anything about zeros. The target sharpens to
*a better `λ → 0` shape in Fujii's error* — the same object [OPEN 0] needs, so
one effective-Fujii analysis now pays twice.

Ledger untouched; no Lean this cycle.


---

# SESSION 019 — day cycle 2 (W22): the seam is a literature, and the wall is 8/33

**The refinement accepted, and it reverses the arbitrage.** Raw Dirichlet-length
was the wrong normalisation: Montgomery–Vaughan gives everything free up to
total length `T`, so the budget is **excess past the diagonal**. Position side:
**zero excess, never crossed**. Value side: `T^{4/7}`, held since Conrey. The
value tradition is the only one that has ever been past the wall, so the import
runs value → position, not the reverse.

**The arithmetic core, named:** crossing the diagonal means shifted convolutions
of the polynomial's coefficients, and the traditions differ *only* in which
coefficients they carry — `d(n)` (additive divisor problem: theorems, Motohashi
exact) versus `Λ(n)` (Hardy–Littlewood). E18's one obstruction is *divisors
correlate provably, primes conjecturally*, and the translation layer is
Vaughan's identity — which this project already met from the other side, as the
tool BHB13 used to remove GLH.

**R7 fires a fifth time, before the kill condition was reached.** The
composition is published: Matomäki–Radziwiłł–Tao, *Correlations of the von
Mangoldt and higher divisor functions* I & II. They do exactly this — Vaughan to
reduce primes to divisor functions, Kuznetsov to cancel the Kloosterman sums.

**And the wall has a number.** Almost-all-`h` results with `H` polylogarithmic
for `Λ·d_k` and `X^{8/33+ε}` for `Λ·Λ`. The genre's *shape* is right — our
container consumes `F` only in averages, which is what almost-all-`h` supplies —
but the *range* reaches `α ≈ 0.242`, inside what we already have. **Crossing
`α = 1` needs `H ~ X`, so the gap is `X^{25/33}` in the exponent.**

Provisional: abstract fetched, papers unread; the `h → α` dictionary needs
checking against Goldston–Montgomery before use.


---

# SESSION 020 — day cycle 3: E20 filed, fracture inventory run and survived falsification

Numbering: dispatched as E19, filed as **E20** (E19 was the S seed from the same
day; filing order stays canonical, as with W25/W26).

**The inventory** (`forensics/fractures.tsv`): 10 half-failures, **10 aligned,
0 misaligned**, one suspect (W12's depth-pricing, possibly an X instance rather
than a plane instance).

**The falsification attempt is the cycle's real yield.** Looking for a
misaligned result turned up five results with *no half-failure at all* — the
census `/6`, `offline_le` tightness, the gauge counterexample, A2, and
`Nsc_eq_ordinate_functional` — and they are **exactly the purely combinatorial
ones**. So:

> the plane appears precisely where arithmetic enters; the combinatorial layer
> is unfractured because it has no generative face to slip off.

Sharper than universality, and falsifiable going forward: combinatorial results
will be whole, `Λ`-touching results will cleave. Adopted as the testbed's fourth
column — not pass/fail but *where the cut fell*.

**Target recorded, not claimed:** X's boundary as "the class consumes only the
Type I shadow", with the concrete question — is `λ < 1` exactly the region where
Vaughan's Type II bilinear terms are controllable? If so, X and E20 fuse.


---

# SESSION 021 — day cycle 4: R16's audit closes; prop1 is LP-optimal

**Wildcard kill condition** ("if `prop1` is LP-optimal in `(N, N⊛)`, the audit
closes") **fires.** Grouping by atom mass makes Proposition 1 a two-variable
LP, and `(α, β) = (2, −1)` is optimal at every `C ≤ 2`. Equality holds for all
configurations of masses `1` and `2`; `Gauge.prop1_tight` witnesses it (R17 —
the claim "cannot be improved" is an absence claim and now has a positive
object behind it).

**The consequence is a new link between two things we had filed apart:**
improving Proposition 1 needs a third moment `Σ m³`, which is [OPEN D]'s
currency. Third-moment data is not only what pushes `C` past the second-moment
ceiling — it is the only thing that can improve the *reduction* the whole
project is built on. **The ceiling and the reduction want the same missing
input.**

R16's audit is closed for the core: `prop1` optimal, `offline_le` tight, census
improvement taken. No free constants remain in the combinatorial layer — which
is consistent with E20's reading that the combinatorial face is complete.


---

# SESSION 022 — day cycle 5: the sign is favourable, and sieve strength clears the ceiling

**Wildcard: check the sign with which `F`-past-1 enters our certificates.** Kill
condition — if certificates need an *asymptotic* past 1, sieve input cannot
convert and the survey's hope dies.

**It does not die.** `κ = 1/λ + 2∫₀¹D(λr)(v⋆v)(r)dr` with `v⋆v ≥ 0`, so a larger
form factor is strictly worse: **the container consumes an upper bound.** Sieve
arithmetic is exactly upper-bound-shaped.

**And the requirement is mild.** With the flat window and no optimisation, a
constant bound `D ≤ K` past support 1 gives `0.7407` at `K = 2`, `0.7130` at
`K = 3`, `0.6852` at `K = 4` — all at `λ = 1.2`, all **above the bandlimited
ceiling `0.6818287`**. The best classical twin-prime sieve constant (~3.4) sits
just inside the `K ≲ 4.1` requirement.

**Plus the survey's headline, which is a correction to my own framing:** BGST's
`𝓕(x,T)` *is* the weighted pair correlation — retaining the `β`-dependence was
the de-conditioning move — so W16's object at support `≤ 1` is the theorem the
project already rests on, not a formalisation task. W16, the GM bridge, and
BGST Theorem 1 are one object at three ranges.

Caveats filed with equal weight: the `D ≤ K` model is crude, the sieve-constant
→ `K` dictionary is unchecked, the window is unoptimised, and the transfer past
support 1 is the unbuilt span. Only the *sign* is model-independent.


---

# SESSION 023 — day cycle 6: averaged consumption done properly; the slot becomes a lookup

**Piece placed:** the correct consumption of an *averaged* form-factor bound.
Abel summation (`w` decreasing, `M(1) = w(λ) = 0`) gives
`∫₁^λ D·w = (1/λ)∫₁^λ M ≤ (1/λ)∫₁^λ A`, so an averaged constant enters
**identically** to a pointwise one, and
`κ(λ,c) = 2/λ − 2/(3λ²) + c(λ−1)²/λ²`.

**Self-correction:** my earlier `K ≲ 4` threshold was an artefact of a coarse
`λ` scan. Optimising `λ` — which slides toward `1` as `c` grows, buying only the
support the constant affords — gives **`c ≤ 7.995`** for the bandlimited
ceiling and `c ≤ 3.667` for BHB13. The pre-CCLM implicit constant `10.824`
lands `0.4pp` below the ceiling, so the composition fails only if the
short-range constant is *worse than the value CCLM improved on*.

**Filed with it** (#22): the corridor is two-sided under RH (CCLM's roof, GGOS's
floor), and the two certificate families are **sign-dual** — CGdL eats the
floor, we eat the ceiling, and a both-walls certificate is an unasked finite
question in the SDP framework. E12's newest sighting.

Quarantined as table-arithmetic per A3; no claim until CCLM §3's `J(β,T)` for
`β ∈ (1,2]` lands.


---

# SESSION 024 — day cycle 7: the two-sided certificate is a window choice

**Wildcard kill condition** — "if the optimum over windows sits at `v⋆v ≥ 0`,
the corridor's floor is never worth eating and the two-sided idea dies inside
this container" — **does not fire.**

The observation that dissolves it: `v⋆v` is positive-*definite*, not pointwise
nonnegative. Where it dips below zero, the worst-case `D` is the corridor's
**floor**, so a positive lower bound on `F` becomes an asset. Optimising a
two-parameter window family at `U = 2` with the GGOS floor gives **0.80382** at
`min(v⋆v) = −0.034`, against **0.74717** for the flat window — **+5.7pp**, and
the optimum is genuinely sign-changing.

**What it settles:** the sign-duality of the two certificate families was not
structural. Each tradition used nonnegative weights and therefore saw one wall;
the container we already have can eat both, with no SDP excursion and no new
framework. E12's corridor reading survives, but the "two halves of one budget"
turns out to be reachable from inside one half.

Quarantined per A3 (RH-conditional, crude family, `U = 2` provisional). The
existence claim is model-independent; the number is not.


---

# SESSION 025 — day cycle 8: I check the trap, and it lands on me

**The alarm was right, twice.** Checking the trap rather than accepting the
escape found two defects in my own `c`-table (#24):

1. **Scale.** The Abel step needs the averaged bound at *every* scale down to
   `u−1 → 0`; the literature's constants are asymptotic in the averaging length.
   That gap is exactly `0.8365` vs `0.6792`. This is R9 — *ask which end binds* —
   failing on my own work: I checked the consumption's **sign** and never its
   **scale**.
2. **Circularity.** `1.3208` is both the averaged-`F` bound and the `N*` bound —
   one extremal problem, two faces (DIR Lemma 4; the RKHS constant *is* M–T).
   Feeding it back is #19 route A wearing a new hat.

`#23`'s `+5.7pp` is retracted as a bound. **What survives is the existence
claim**, which never rested on a constant: a sign-changing `v⋆v` consumes both
corridor walls and sits outside the `g ≥ 0` axioms of every classical class.

**The discriminator is now explicit**: an input must be valid at the scales the
window uses **and** not derivable from `{F on [0,1], F ≥ 0}`. CMR fails both;
sieve bounds on prime pairs pass both. Which is what Goldston–Montgomery were
doing in 1987, and is the only input class that has ever moved this number.


---

# SESSION 026 — day cycle 9: Lemma 1 prices route (b) dead and voids my thresholds

**Goldston's Lemma 1** (`∫_B^{B+1} F ≤ 3` under RH, any `B`) is the
scale-corrected class bound: passes discriminator (1), fails (2). It prices the
finite-`ℓ` rerun without running it — at unit scale the class constant is `≈ 3`.

**Run as a constraint it settles the question:** with only
`{F on [0,1], F ≥ 0, unit cap 3}`, the container's optimum is **`λ = 1`,
proportion `2/3`** — Montgomery's bound, refusing to leave the band. Class-derived
past-1 information is not just useless but harmful (`0.237` at `λ = 1.1`).
Fifth independent derivation of the same conclusion, first one by duality.

**Retroactive audit, worse than yesterday's:** Lemma 1 makes any model with
unit-window mass `> 3` **RH-impossible**, so my published break-evens
(`c ≤ 7.995`, `c ≤ 9.532`) described worlds RH forbids. That analysis was
vacuous, not merely unsound.

**Guard built** (`forensics/lemma1_guard.py`), and **R18 adopted**: every
numerical input passes scale *and* independence before a table exists. The
fourth costume of the scale disease cost a published threshold; the fifth will
hit a guard.


---

# SESSION 027 — day cycle 10: premise corrected, chain priced at 0.809, one gate left

**Premise correction:** the twin-sieve bound *closes the band edge* (`α ≤ 1`
exactly, by improving one error term); it does **not** extend past 1. What
reaches `(1,2)` is full Hardy–Littlewood. The input we wanted does not exist and
must be built — from survey §9's chain, whose integrands are **nonnegative**, so
it transfers **inequalities**.

**Dictionary discharged:** `α ≤ 1/(1−θ)`, fixed by two points (`θ=1/2 → α=2`;
`θ=8/33 → α=1.32`).

**Priced, and R18-clean for the first time this week** — arithmetic input,
correct scale, Lemma 1 guard passed (worst unit mass `2.36`). Optimum sits
exactly at `λ = A`: **`0.80869` at `A = 1.32`**, rising to `0.852` at `θ=1/3`
and `0.917` at full HL. Against BHB13's `0.70370`, that would be the conditional
record by ten points.

**One gate:** does MRT's almost-all-`h` log-power-saving error survive the
weighted sum `(9.1)` needs? Finite comparison, two published error terms.
Quarantined per A3 — RH-conditional *and* gate-conditional.

**Instrument note:** the sign-changing window contributes nothing where `F` is
known (no corridor there) and everything past the fuel. The two objects tile
rather than compete.

Also caught in-cycle: my first pass modelled the past-fuel worst case as
pointwise `D = 3` when Lemma 1 caps *unit-window mass*, so a spike is worse.
Corrected before the number was quoted anywhere — the guard is doing its job
one costume earlier than the last three.


---

# SESSION 028 — day cycle 11: the gate fails, and it takes the headline with it

Both sides fetched. **Requirement:** survey (6.3) needs `O(N^{1/2+ε})` — a power
saving — because the second moment's expansion `Σ(h−|k|)[·]` amplifies each
shift's error by up to `h`. **Supply:** MRT I gives *"an arbitrary power of the
logarithm"*, `X/(log X)^A`, almost all `h`. **Comparison:** the bridge needs
`X^θ ≪ (log X)^{A+1}`, false for any fixed `A` and `θ > 0`.

**The gate fails by a power of `X`.** `A = 1`, not `1.32`; `0.80869` retracted;
the chain gives nothing past Montgomery's `2/3`. Sixth self-correction, first to
kill a headline — and the fastest, since the number never left the machine.

**What it buys:** the target is named — *averaged Hardy–Littlewood with power
saving* — and the corridor is now everything past `α = 1` with no fuel at all,
which promotes W27's T3 from a wildcard to the only game.

Twice in one turn the guard culture caught me mid-cycle: once on the pointwise-vs-
spike worst case, once on a numeric "OK" that was a small-numbers illusion
(`X^θ` overtakes `(log X)^{A+1}` only past `10¹⁰⁰`). Two costumes, same turn,
neither reached a dispatch.


---

# SESSION 029 — day cycle 12: W∞ filed; the census's own pattern fails its blind test

**T1 done:** `FAILURES.md`, eleven entries, schema forcing each death to declare
what it certifies.

**T2 run, and it returns a negative about our own centrepiece.** A Fable agent,
given the eleven attempts with all crystal/cascade language stripped and no
hypothesis, sorted them into two groups **of its own devising** — *insufficient
resolving power* vs *circular information* — agreeing with the plane on
**6/10** where chance is 5/10.

So the `11/11` alignment was an artefact of hypothesis-aware classification, as
the contamination note predicted. **The census is not evidence for E20.** The
plane survives on its four mathematical derivations; its statistical support is
withdrawn, and no p-value should be quoted.

**The blind result is itself a finding:** the dominant axis an unprimed reader
sees in our deaths is **circularity** — five of eleven are the input being an
output. That is a fact about our method rather than about `ζ`, and R18's
independence condition was written after the fourth instance, not the first.

Seventh self-correction of the session and the first aimed at a register
centrepiece rather than a number.


---

# SESSION 030 — the detector is built; R19 adopted; T3(b) predictions sealed

**`forensics/provenance_lint.py`** — the contamination detector, and it earns
its keep on its training set. Three rules, three of the project's expensive
failures caught **at proposal time**:

* **CIRCULAR** — CMR's constant (ancestry hits `EP1`), Lemma 1 as a past-1 input
  (ancestry hits `class_closure`);
* **SCALE** — CMR again (valid at large averaging length, consumed at `0.3`);
* **QUALITY** — the gate (`GM_bridge` needs power savings, `MRT_corr` supplies
  log-power).

Rule 3 was written because the first two rules *passed* the priced chain, whose
failure was a third kind. The tool now blocks every table this project had to
retract.

**R19 adopted:** no pattern-claim about our own corpus without a blind
classification scored against a pre-registered mapping. **S annotated:** the
blind null is the first measurement of our own point-spread function — you
cannot deconvolve what you have not measured. **E10 annotated:** the first
attempt to measure the shape measured the surveyor.

**T3(b) predictions sealed** (`forensics/T3b_predictions_VPS.md`): 9 survive
`¬RH`, 2 change (`#24`, `#25`) — the two consuming RH-conditional inputs. The
other instance analyses blind; disagreements go to Joop with both writeups.


---

# SESSION 031 — T3(b) answered mechanically; the blind leaked; W33 filed

**Breach logged first.** The seal was defeated by courtesy — I summarised the
sealed predictions "so you can score against it", which destroyed the blind by
being helpful. Third member of the silence taxonomy:
**disclosure-impersonating-transparency**. Escrow fix adopted: the seal is a
published content hash (`5d385586e174ddc4`), revealed only after the counterpart
analysis commits its own.

**T3(b) answered by the lint, not by argument.** RH-conditional nodes flagged,
flag propagated: **3/11 deaths are bridge material** (`#24` structurally, `#25`
numerically, `#27` structurally). The census is **73% instrument**.

**Round 1 scored: my sealed prediction was 2; mechanical answer 3.** The extra
is `#27`, where I was most confident — the gate's comparison is unconditional
but the requirement it compares against is the RH-conditional GM bridge, so in a
¬RH world the failure doesn't exist as stated. The lint caught what my judgment
missed, which is the first time tooling has beaten me on a classification
question.

**A3 inverted:** the conditional row is the bridge's quarry, not a quarantine —
only hypothesis-consuming failures can change under ¬RH. **W33 filed:** every
expensive retraction was a type error; make the types explicit.


# SESSION 032 — re-entry at context v2: the third read, and the second counterexample

**Log line gains a field.** `context: v2 (compacted)` now sits beside `base:` in
`PROPORTION.log`, sourced from `metric.json` so it is data, not code. It records
the *operator's* epistemic discontinuity, not the repo's: the counts did not
move, the meaning behind the executor did. If the error profile shifts, the seam
is findable. Base hash re-verified `cd7a22e688df`; escrow seal re-verified
`5d385586e174ddc4`; build green (3743 jobs); guards block exactly where they
should.

**Instrument note, logged because it is the post-compaction failure mode.** The
first `proportion.go` run exited 4 with an empty escalation body — I had run it
without the Lean env exports the loop prompt specifies. The audit did its job;
the operator did not. Fluent shallow compliance, precisely as the re-entry
protocol predicted.

**The blessing task.** Eleven certified reasons, columns 1–3 only, own
categories before opening `E.md`. Sealed `460ccd415bc031e1`; comparison in
`forensics/tri_read_comparison.md`. The axis is **coupling**: `FUSED`
{1,2,4,7,8,9} · `SLACK` {3,6,10} · `SHORTFALL` {11} · verdict error {5}.
Circularity is not its own class here but the limiting case of fusion.

**What three independent axes agree on, and it is a short list.**
Co-classification across P (plane), F (Fable blind) and M (context v2) leaves
exactly two clusters: `{4,7,8}` and `{6,10}` — *what the functional cannot see*
and *what the class cannot exceed*. **X and the ceiling, and nothing else.**
Three readers, three axes, one amnesiac, and they recover only the two objects
the project already treats as primitive.

**And the plane column is half-measurable after all.** 5 of 6 `crystal` entries
sit in a stable cluster; **0 of 4** `cascade` entries do. The mechanism is in
the reasons: stable ones are statements about a *fixed object*, disputed ones
are statements about an *argument's fate*. Only object-statements are
census-gradeable. Candidate rule held, not adopted — doctrine is frozen for
three cycles.

**The blind leaked again, and I found it before the dispatch did.** A
schema-learning `grep` rendered rows 1–2 with their plane column; the compaction
summary carried E20's plane, the T3(b) verdicts, and cause-language for
`#24`/`#25`/`#27`. Genuinely blind subset: **3–8**. `{4,7,8}` lies wholly
inside it, so the headline cluster passed a *harder* test than the sealed file
claimed; `{6,10}` is half-clean; "`#11` is `sui generis`" downgrades to
hypothesis-aware. The sealed file was **not** edited — the hash outranks the
wording. Generalisation: **orientation is an exposure channel.** You cannot
learn how a corpus is shaped without seeing some of it.

**W28 drafted cold** (`246745bcc293b648`), before opening `E.md`, from
`Basic.lean` and `Program.lean` and the two model checks. `ZeroData` is the
functional equation and nothing else, so Davenport–Heilbronn *is* a `ZeroData`
— indictment and asset at once. Two disjoint bundles, M and S, with
`savingShape` as a field so `#27`'s mismatch becomes a type error at the
interface. **The draft's new exhibit is a second counterexample pointing the
other way:** Beurling generalised prime systems (Diamond–Montgomery–Vorhauer)
have the whole multiplicative nature and RH is false for them. D–H kills "the
functional equation suffices"; Beurling kills "the Euler product suffices". Not
previously in the registers — E.md stops at E20 and the atom program lives only
in the dispatch stream, which is itself a drift worth naming.

**Might-mean:** the arithmetic input that `#27` failed to buy was never one
route among three — the two counterexamples bracket the program from both sides
and leave the bilinear field mandatory, so the corridor, the census and the
atom program are not competing for cycles but queueing for the same purchase.


# SESSION 033 — the blindness cluster becomes a specification, and the ledger turns out to be the theorem

**Queue item (1) done.** `Riemann/Blindness.lean` — 14 declarations, sorry-free,
axiom-free (`propext`/`Classical.choice`/`Quot.sound` only, verified by
`#print axioms` on all eight headline names). Build green, 3744 jobs. The
tri-read's stable cluster `{4,7,8}` — the one thing three independent
classifiers agreed on — is now formal.

**What was actually proved is stronger than the cluster.** Define
`MuInvariant B := ∀ D D', D.ordinates = D'.ordinates → (B D ↔ B D')`. Then no
`μ_T`-invariant hypothesis, of any strength, makes `NscStd` or `N_off` an
ordinate functional, provided it admits either half of the gauge pair. The
inability is not a property of the axioms currently assumed; **it survives
adding any hypothesis of the class.** `#4` is now proved *uniformly in the
depth* — `depthPair a` and `doubleZero` share `μ_T` for every `a ≠ 1/2`, so
there is no limit to take and no small-parameter story: it is an identity.

**The positive form is the deliverable.** A hypothesis that determines `NscStd`
from `μ_T` must **exclude** one of two legitimate reflection-symmetric
configurations. Bundles do not compute the missing coordinate; they rule out
the world in which it is ambiguous. And the exclusion is exhibited:
`OnLine D := ∀ p ∈ D.Z, p.1 = 1/2` is proved **not** `μ_T`-invariant, and under
it the two ledger rows coincide. The specification this yields is **narrow, and
the loose version is false**: non-μ-invariance is necessary to compute `NscStd`
or `N_off` from `μ_T` *exactly* — it is **not** necessary to be useful, since an
effective Fujii constant is μ-invariant and would move both rows. This is also
the certified form of "RH is outside the certificate class" — a property of the
predicate, not a remark about technique.

**Wildcard, kill condition stated first (R12):** *if even one axiom of the
trusted base is visibly non-`μ_T`-invariant, the sweeping claim "the whole base
composes with the blindness" dies.* **It fired — three do.**
`levinson_montgomery` reads `N_off`; `baseline_przz` and `baseline_zeta23` read
`NscStd` via `ProportionStd`. The other four (`zetaNonempty`,
`fujii_ineffective`, `fujii_closePair_bookkeeping`, `zeta23_xiPrime`) read only
`N`, `N⊛`, `Nsc` and are μ-invariant.

**And the corpse is worth more than the claim.** The ledger *currently*
realises the split: row `NscStd` = 67.25% is carried **entirely** by the three
non-μ-invariant imports. Row `Nsc` = 0.00% is **not** empty for a visibility
reason — `Nsc` is the μ-*visible* quantity — but for a **supply** reason, no
effective `C`. So the correspondence is contingent and has a breakage
condition: the day OPEN 0 lands, a μ-invariant axiom feeds both rows and the
coincidence ends, without touching the theorem. Recording it now so that day is
not misread as a refutation.

Flagged not done under the freeze: `audit/Declarations.lean` should gain the
eight new names.

**Might-mean, unhedged:** this program manufactures β-information freely in
inequality form — `on_line_of_H_eq_one`, `odd_Hr_inhabited`, `prop1` all pull
on-line content out of ordinate data — and cannot manufacture a single
β-*identity*, which is why every identity-grade number on the certified row was
bought; the atom program's assignment is therefore the narrow one of producing
one non-`μ_T`-invariant statement of our own, and `Blindness.lean` is now the
acceptance test for whether a candidate qualifies.


# SESSION 034 — the crowded locus is a theorem, and rung 1 becomes real independence

**`Riemann/Fiber.lean`** — 10 declarations, sorry-free, axiom-free. claude.ai's
correction to my equality/inequality boundary was right and is now formal. The
boundary is not equality-ness; it is **solitude**. `on_line_of_H_eq_one` *is* a
β-equality manufactured from ordinate data — what it consumes is an atom of
mass one.

* `config k j a` generalises all four gauge witnesses at once
  (`triple = config 3 0`, `haunted = config 1 1`, `doubleZero = config 2 0`,
  `depthPair = config 0 1`).
* `config_ordinates_eq`: the whole fiber over a mass is **one gauge orbit** —
  `μ_T` sees `m = k + 2j` and nothing else, at any depths.
* `Noff_eq_zero_of_simple`: **sighted** on the simple locus.
* `blind_at_every_crowded_mass`: **blind at every mass `≥ 2`**, uniformly in the
  depth. Mass one is the sharp threshold; the blindness is supported *exactly*
  on the crowded atoms.
* `Discriminates Φ a := Φ (config 2 0 a) ≠ Φ (config 0 1 a)` — the acceptance
  test, now mechanical, with both directions proved.

**Sharpening returned to the dispatch:** the gauge pairs' equal parity is not a
choice, it is forced (`config_parity`: `k ≡ m (mod 2)` for every fiber state).
There is no unequal-parity pair to exhibit, which is exactly why parity is the
μ-visible part and `j` is the whole residue.

**W34a done, and it was not decorative.** Translating rung 1 into the
logicians' dialect exposed a discontinuity the ladder metaphor hid: rungs 0–1
are *semantic* blindness (quantified over hypotheses), rungs 2–ω are
*proof-theoretic* independence (quantified over proofs), and the passage
requires the class to be **closed under deduction**. For `μ_T`-invariance it is
— `MuInvariant.and/.or/.not/.imp` (a Boolean subalgebra) and
`MuInvariant.forall` (arbitrary conjunction, so a whole *theory* of μ-invariant
axioms is itself one). Hence `no_muInvariant_theory_computes_NscStd`. **Rung 1
is a genuine independence result, not merely a blindness result**, and it is
proved rather than asserted.

**E23 filed**, logic checked and endorsed including its honesty clause: RH is
`Π₁`, systems are `Σ₁`-complete, so unprovability of `¬RH` gives RH — in the
metatheory, as truth in `ℕ`, and at a cost at least that of RH itself. One
precision added: the payoff is a theorem about the world, not a certificate we
could ship.

**Repository packaging in flight** (Joop): everything to a private GitHub with
`METHOD.md` and `VERIFYING.md` so the claims are independently checkable —
which is W34e arriving from the practical side rather than the doctrinal one.
Delegated to a subagent to keep the loop clean.

**Might-mean, unhedged:** the project's instruments are exactly sighted on
solitary ordinates and exactly blind on crowded ones, with mass one the sharp
threshold, so E15's rooming rule has acquired its converse — one voice per
pitch is not merely what RH asserts, it is the precise condition under which we
can hear at all, and the entire problem is now formally the question of whether
the part we cannot see is empty.


# SESSION 035 — the quarry says "shape, not range", and the acceptance test gets its first passing functional

**Queue item (2), the quarry** — `forensics/quarry.py`, three experiments, guard
DAG **not** edited (the freeze holds; the script imports the lint and evaluates
its rules, and any node it needed that the guard lacks lives in a clearly
labelled local experiment table as a *proposal*).

**Wildcard, kill condition stated first:** *if some `θ > 0` satisfies
`X^θ ≪ (log X)^{A+1}` asymptotically, the gate is a threshold in `θ` and the
"shape not range" reading dies.* **It did not fire.** For every `θ > 0` the left
side is a power and the right a log-power, so `#27` fails uniformly in `θ`. The
axis the field has advanced on for thirty years — Mikawa `1/3` → MRT `8/33` — is
**orthogonal to the requirement**. Improving the shift range moves the crossover
and never crosses it.

**And the quantitative half is the actual find: the failure is purely
asymptotic.** Crossover `log X` runs 31 (Mikawa, `A=2`) to 1545 (MRT, `A=50`) —
`X` from `10^13` to `10^671`. **No numerical experiment at any feasible height
could have seen this obstruction, and none could ever have warned us.** `#27`
survived a hand computation and died to a shape check; the invisibility radius
is now measured.

**Corridor, honest limit:** CMR is CIRCULAR at *every* window scale
(`0.3 … 3.0`), and the scales where it is scale-valid are ones our window never
reaches. The corridor is not under-fuelled from that node — it is
**unfuellable** from it. **Depth stratification:** 8/11 unconditional, 3/11 RH,
**0/11 GRH** — the GRH tier is empty, which is a recruitment criterion.

Census **annotated, not extended**. Inflating the count would be the Goodhart
move the doctrine forbids; the quarry's yield is sharper reasons, not more
deaths.

**Second piece, from claude.ai's dispatch, and it is the headline:
`landau_discriminates` is proved.** `landau x D := Σ_ρ x^β`; on the mass-two
fiber states it is `2·x^(1/2)` against `x^a + x^(1−a)`, and the strict
arithmetic–geometric mean inequality separates them for every `x > 1` and every
depth. Composed with `not_factors_of_discriminates`, the kernel checks that
`landau 2` **does not factor through `μ_T`**. The atom program's assignment — one
non-`μ_T`-invariant statement of our own — is discharged.

**Honesty clause at full size:** this certifies the *functional* discriminates,
not that we can *evaluate* it on `ζ`'s zeros to the needed precision. That is
W16's separability problem, untouched (census #1). What changed is that the test
now has a known-passing calibration input.

**`FRAMING.md` filed** — the companion document from the other side of the seam,
with a verification appendix of mine: nine claims checked against the repo, one
corrected (per-theorem axiom cones are auditable by running `#print axioms`, not
"via the logged digests" — the log carries the base digest, axiom names and the
sorry count), and two claims explicitly marked not-checked.

**Might-mean, unhedged:** the discrimination that a century of pair-correlation
machinery provably cannot make is performed by an inequality older than the
Hypothesis, so the open content is no longer a vision problem but an evaluation
problem — and evaluation problems, unlike vision problems, have a price system.


# SESSION 036 — a second calibration family, and a test-design rule bought by building an invalid test

**The suite gains family 2** (`Riemann/Fiber.lean`, axiom-free). Family 1 lives
at a single ordinate, so every zero shares `e^{iγ log x}` and the test exercises
only functionals reading the `β` multiset. Family 2 adds a **spectator**: the
mass-two gauge pair at height `0` plus a simple on-line zero at height `γ`.
`spectator_gauge_pair` — same `μ_T`, different `N_off`, ordinate measure spread
over two heights. `landau_discriminates₂` — the Landau weight passes it too, at
every `x > 1`, depth and spectator height; the spectator's `x^(1/2)` cancels and
strict AM–GM does the rest. `not_discriminates₂_of_factors` — nothing factoring
through `μ_T` passes, as it must be.

**And the cycle's real yield came from a family that failed to be a test.** The
obvious third family is the **swap**: `(2,0)` at `0` with `(0,1)` at `γ`, against
the two exchanged. It looks sharper — same `μ_T`, genuinely different phase
structure — and the real Landau weight does not discriminate it
(`landau_swap_invariant`).

That is not a defect. `swap_not_a_gauge_pair`: the swap agrees on **every target
count** — same `μ_T`, same `N_off`, same `NscStd`. It is a *symmetry* of the
configuration space, and every functional ought to agree on it. Rule, filed
before anyone reads a failure there as evidence:

> **A calibration input is two configurations agreeing on `μ_T` and disagreeing
> on a target.** Same-`μ_T` pairs that also agree on the targets are symmetries,
> and discriminating them is not a virtue.

**Correction to the incoming dispatch, and to my own next step.** The phase
caveat was correct as a caveat but its proposed fix does not do what it says: I
built the two-height family expecting it to force the phase channel, and it does
not. No family built from configurations at *any* number of heights forces
phase, because the targets (`N_off`, `NscStd`) are themselves ordinate-blind in
the relevant sense. **Whether the phase channel is necessary remains open**, and
the honest statement is that family 2 broadens the test without deciding it.

**E24 filed** — the oldest inequality performs the newest discrimination; E16's
`cosh` annotated as AM–GM's excess, `x^a + x^(1−a) = 2x^(1/2)cosh((a−1/2)log x)`.

**S gains a number** — the invisibility radius. `#27`'s gate is false for every
`θ > 0` but only *visibly* false past `X` between `10^13` and `10^671`. Below
`10^13` every hand computation agrees with a false statement. It is the
project's largest measured silence that could not have been broken by looking,
and the specimen for why shape checks outrank numerical ones: the conserved
quantity is the error's *shape*, decidable in one line without evaluating
anything.

**`FRAMING.md` appendix updated**: the wildcard hit-rate moves from "not checked"
to "asserted by its owner with a tally", with the tally recorded and the note
that I have not recounted it.

**Might-mean, unhedged:** the cycle's most valuable object was a test that
turned out not to be a test, because discovering that a same-`μ_T` pair can be a
symmetry rather than a gauge pair is exactly the distinction that separates a
calibration suite from a collection of examples — and we would have shipped the
collection.


# SESSION 037 — night cycle 1: the audits catch up, and W16 becomes a price

**Post-freeze housekeeping, both safe, both done.** (a) `audit/Declarations.lean`
gains 26 names from `Blindness.lean` and `Fiber.lean`, and `audit/PrintAxioms.lean`
six — the existence audit and the axiom audit now cover the week's theorems.
(b) ISSUES #28(b) closed: the doc comment in `Assumptions.lean` reworded so no
line begins with `axiom`, and `grep '^axiom' Riemann/Assumptions.lean` now
returns **9**, matching the tool.

**R17 witness for that green light:** the base statement hash did **not** move
(`cd7a22e688df`) across a comment-only edit. That is the positive object — the
detector fingerprints axiom *statements*, so a prose change must leave it fixed,
and it did. A hash that had moved would have meant the fingerprinter was reading
comments.

**The piece: W16 re-priced** (`forensics/w16_price.py`). Vision is closed, so
what does evaluation cost? Coordinate `x = T^c`, depth `δ = 1/log T`, which makes
`δ log x = c` exactly.

**Wildcard, kill condition stated first:** *if the crossover `c` at a height
where zeros are known (`T ≲ 10^13`) is `≤ 1`, the unpaid range is unaffordable
everywhere feasible and the Landau route is dead outright.* **It did not fire.**

* The per-pair excess is `2x^{1/2}(cosh c − 1)` — **a fixed fraction of the
  chorus term, set by `c` alone.** The signal is scale-free in this coordinate;
  it does not fade with `T`.
* Aggregate **unphased** margin against Landau–Gonek's error crosses 1 at
  `c ≈ 1.386` for `T = 10^12`, `κ = 0.01`. The window `c ∈ (1, ≈1.39]` is
  **nonempty at a height where zeros have actually been computed**; it opens at
  `T ≈ 10^7.6` and widens to `(1,2)`.
* **So the binding constraint is the phase, not the magnitude.** Landau–Gonek
  supplies the *phased* sum, one unknown `e^{iγ log x}` per zero; the
  discriminator wants the unphased one; second moments in `x` are the
  phase-killer and are paid only to the diagonal. **The price of the Landau
  route is the price of exactly one phase-removal.** Census #1 said this in
  words; the column says it with a number and locates the unpaid stretch.

**And the asymptotics lie in the opposite direction from `#27`.** The exponent
promises every `c < 2`; at `T = 10^12` the crossover is `1.39`, and `c = 1.9`
needs `T ≳ 10^50`. `#27`'s asymptotics were crueller than its numerics; here
they are kinder. Both times the honest statement needed the crossover computed
rather than the exponent read — filed beside `S`'s invisibility-radius entry as
the general lesson.

**Caveat carried in the open, because the conclusion leans on it:** identifying
"paid" with `c ≤ 1` assumes the dictionary between this coordinate and the
pair-correlation support parameter. That is **[RECALL, UNVERIFIED]** — the same
`h ↔ α` check already open. If the truth is `c ≤ 2`, the unpaid window is empty
and the second reading collapses. It is now the cheapest high-value
verification on the board.

**Might-mean, unhedged:** the Landau route's entire remaining bill is one
phase-removal over a stretch of `c` that is affordable at heights we have
already computed, so the question stopped being whether the value channel can
see and became whether anyone will pay to look between `c = 1` and `c = 1.4`.


# SESSION 038 — night cycle 2: the guard learns depth, and three decades get one verdict

**Piece: the guard change** (`forensics/provenance_lint.py`).

**Kill condition stated first:** *if generalising `RH_CONDITIONAL` from a bit to
a hypothesis-depth order changes the T3(b) answer away from 3/11, the change has
altered a published result rather than refined it, and it reverts.* **It did not
fire.** `HYPOTHESIS_DEPTH = {RH: 1, GRH: 2}`, `RH_CONDITIONAL` retained as the
`depth ≥ 1` set so every existing caller keeps its meaning. Changers
`[9,10,11]`, 3/11, unchanged; tiers 8 unconditional / 3 RH / **0 GRH**.

**R17 witness, and it is the reason the deletion was safe.** `quarry.py`'s local
experiment table and the guard's new `depth()` are two independent
implementations of the same stratification, and they agreed exactly (8/3/0)
*before* the swap. The local table is now gone and the guard is the authority —
the agreement is what licensed removing the second implementation, not a
preference for tidiness.

**The progress axis is now a node family.** `Mikawa_third`, `BBMZ_theta`,
`MRT_8_33`, all supplying `log-power`. Fed to `GM_bridge` they yield **three
identical QUALITY verdicts** — thirty years of exponent improvements, one
rejection reason, printed by the guard rather than argued in prose. Experiment D
added to the quarry to exhibit it.

Full suite green afterwards: `lemma1_guard` self-test passes (D=4 correctly
flagged as violating Lemma 1), `lake build` 3745 jobs, `proportion.go` clean,
base hash `cd7a22e688df` unmoved.

**Snag, bin 2 (worth naming because it nearly cost the guard).** My first patch
attempt asserted on five exact string matches and the fourth failed on a
whitespace difference — the file was left **untouched** because every write
happens after every assertion. That is the correct failure mode and it was luck
of construction rather than design: an edit script that writes incrementally
would have left the guard half-generalised and still green. Filed as a habit to
keep: patch scripts assert everything first, write once.

**Might-mean, unhedged:** a guard that can print the same rejection for Mikawa,
BBMZ and MRT is no longer a bookkeeping device but a claim about the field's
own history, and the claim is that its measured axis of progress has never once
been the axis its intended consumer bills for.


# SESSION 039 — night cycle 3: the ladder audited, and rung 0 turns out to be borrowed

**Piece: W34d, the ladder audit**, with the criterion made mechanical on
purpose — an entry has a rung iff a **machine-checked** statement exists saying
no member of a named class decides the target. Certificate existence is a
`#print axioms` check; only class-naming is judgement, and it is marked.

Two genres separated, and the distinction is load-bearing: **two-model** (the
forcing shape — exhibit two structures agreeing on what the class sees) and
**capacity** (the LP/extremal shape — bound the class's optimum below the
target).

**Certified rungs: 4 of 11.**

* `#4`, `#7`, `#8` — **rung 1**, class `μ_T`-invariant hypotheses, certificates
  in `Blindness.lean`/`Fiber.lean`. All three were built this week.
* `#6` — **rung 0**, class bandwidth-one certificates, certificate
  `Zeta23.PairCeiling.ceiling_law256`. I verified it axiom-free tonight; note it
  is **not reachable from our root** — `import Riemann` does not see it, and it
  had to be imported directly from the dependency.

**Registered prediction, scored.** Filed in SESSION 034 before the run:
has-rung/no-rung would roughly reproduce crystal/cascade. **Confirmed in
direction** — all four certified rungs are crystal, **no cascade entry has
one**. **No p-value quoted and none available:** sample of 10, and the
class-naming half was done with the prediction in hand, which is the exact
contamination R19 exists for. The certificate half is mechanical and is what
carries the direction. `#9` defects here as it did in the tri-read — unstable
under every classifier we own.

**The unpredicted finding, and it is the uncomfortable one: rung 0 is borrowed
and our own rung-0 claim is uncertified.** `#10`'s LP-duality collapse — listed
in the ladder brief as *owned* — exists here as **prose**. There is no Lean
statement that `{F on [0,1], F ≥ 0}` + positivity fails to decide the target.
The only capacity certificate we can actually run arrived with zeta-23. Filed as
`SURPRISES` S19 (class `process`): I relayed "owned" without checking, and the
audit's own criterion caught it.

**Snag, bin 2:** `ceiling_law256` is cited across four registers as *our*
ceiling and is not imported by `Riemann.lean`. Nothing false was published — the
theorem is real and axiom-free — but a reader following `import Riemann` cannot
reach it. Cheap fix available; not done tonight (it changes the root's import
surface, which is a build-shape decision).

**Next rung-0 item, cheap and Lean-reachable:** formalise the LP collapse as a
capacity statement about a convex program — "no `F` supported in `[0,1]` with
`F ≥ 0` beats Montgomery's `2/3`". That is not a theorem about `ζ` and needs no
arithmetic input, so it sits in the same tier as the combinatorial core.

**Might-mean, unhedged:** the ladder we have been describing as a staircase has
exactly one step we built and one step we borrowed, and the audit that revealed
this was the first instrument in the project aimed at our *claims of ownership*
rather than at our mathematics.


# SESSION 040 — night cycle 4: the rung-0 debt, paid down to its skeleton

**`Riemann/Capacity.lean`** — 7 declarations, sorry-free, axiom-free. It
mentions neither `ζ` nor pair correlation, which is precisely why it was
reachable tonight without any arithmetic input.

**Kill condition, stated before the file existed:** *if the statement cannot be
made without assuming the LP duality it is meant to establish, it dies and the
debt is permanent.* **It did not fire** — and the reason deserves its own line:
**no duality theorem is used at all.** The census entry's certified reason reads
"Lemma 1 + LP duality"; the capacity half needs neither. The infimum is computed
directly, by exhibiting the adversary's move. The register's mechanism was
heavier than the fact.

* `pinned_value_is_floor` + `pinned_value_attained` — with `K ≥ 0` outside the
  known set, the guaranteed value is **exactly** the pinned sum.
* `unbounded_below_of_neg_outside` — with `K < 0` anywhere outside, the program
  is **unbounded below**; for every target there is an admissible `F` beneath
  it, so the certificate proves nothing.
* `value_eq_pinned` — both halves as one `IsGreatest`.
* `no_gain_past_known` — multipliers agreeing on `known` guarantee the **same
  value**, however wildly they differ beyond it.

Extension is *worthless* when nonnegative outside and *fatal* when not. Never
profitable.

**And then the audit's own criterion came back for me.** The class certified
here is `{F pinned on a finite `known`, F ≥ 0 outside}`. The class `#10` names
is `{F on [0,1], F ≥ 0}` — an integral program over a continuum, not a `Finset`
sum. **Those are different classes**, and last cycle's criterion demands a
machine-checked statement about the class actually named. So rung 0 goes from
*uncertified* to **partial**, not to certified. Filed as `SURPRISES` S20: I
expected the formalisation to discharge the rung and it discharged its skeleton.

That is the criterion working as intended one cycle after being written — the
first time an instrument here has been turned on the output of the cycle that
built it.

**What remains is bookkeeping, not mathematics:** the map from a bandwidth-one
certificate to this program, and the passage from `Finset` to integral. It is
now a well-posed Lean task rather than an argument.

Audits extended to the six new names; build green (3746 jobs); base hash
unmoved.

**Might-mean, unhedged:** the honest ladder now reads one rung we built, one we
borrowed, and one whose skeleton is ours and whose flesh is still prose — and
the reason we know that precisely is that we wrote down what "having a rung"
means *before* trying to claim another one.


# SESSION 041 — night cycle 5: rung 0 certified over the continuum, and the regress stopped on purpose

**Kill condition, stated before the section existed:** *if the integral
machinery forces a side-condition that is itself the disputed content, the
instantiation dies and rung 0 stays partial.* **It did not fire.** The only
side-conditions are `MeasurableSet A` and integrability — facts about whether
the symbols denote anything, not about whether extension helps. Nothing is
imposed on `K` outside `A` beyond the theorem's own sign hypothesis.

`Riemann/Capacity.lean` gains a `Continuum` section, axiom-free, sorry-free:
`pinned_value_is_floor_integral`, `pinned_value_attained_integral`,
`value_eq_pinned_integral`, `no_gain_past_known_integral`. For **any measurable
`A`** — `[0,1]` included — the guaranteed value is exactly the pinned integral,
and two multipliers agreeing on `A` guarantee the same value however wildly they
differ outside it.

**The class now matches the one `#10` names**, which was precisely the objection
the ladder audit raised against last cycle's `Finset` version.

**And here is where I stopped, deliberately.** What is still unformalised is the
*modelling map*: bandwidth-one certificate `↦` multiplier `K`, proportion bound
`↦` program value. I could have filed that as a third layer of debt and gone
around again. I did not, because it is **not a new debt — it is the project's
existing boundary**, the same species as the nine constants in
`Assumptions.lean`, the place where our mathematics meets the literature's
setup. Treating it as an open rung item would start an infinite regress in which
nothing is ever certified.

So: **rung 0 is ours, at exactly the standard everything else on the certified
row is held to** — no better, and explicitly no worse.

Snag, bin 1 (build environment, not mathematics): the obvious import
`Mathlib.MeasureTheory.Integral.SetIntegral` does not exist at this Mathlib rev;
the set-integral lemmas live in `Mathlib.MeasureTheory.Integral.Bochner.Set`.
Found by the build, cost one cycle-minute. Worth noting only because it is
another instance of ISSUES #28(a)'s theme: we are pinned to a rev whose module
layout we do not control.

Audits extended; build green (3746 jobs); base hash unmoved.

**Might-mean, unhedged:** the ladder's ground floor is now certified, and the
thing that let it finish was deciding — in writing, before the next objection
arrived — where the standard of proof stops and the trusted base begins.


# SESSION 042 — night cycle 6: the fatal half, and census #10 closes

**The gap I left open last cycle, closed.** The continuum section proved
extension *useless*; it never proved it *harmful*. That asymmetry mattered:
"useless" alone would have made `#10` a shrug rather than a warning.

`unbounded_below_of_neg_outside_integral`, axiom-free, sorry-free.

**Kill condition, stated first:** *if stating it requires a hypothesis that
already assumes the conclusion, it dies and "harmful" stays `Finset`-only.*
**It did not fire.** The hypothesis is `∫_E K < 0` on some measurable
`E ⊆ Aᶜ` where `K` is integrable — "there is a place outside the pinned range
where the multiplier is negative on average". That is the situation being ruled
out, not the ruling. The witness is explicit and constructive: pin `F` on `A`,
add a constant bump `t` on `E`, and the value is `P + t·∫_E K → −∞`.

**Census `#10` is now fully in the kernel:** extension past the known range is
**useless** when the multiplier is nonnegative outside and **fatal** when it is
negative on average anywhere outside. Never profitable. Both halves hold for any
measurable `A`, and neither mentions `ζ`.

**Consolidation, per the queue's fallback:** all guards re-run green —
`provenance_lint` (changers `[9,10,11]`, 3/11, tiers 8/3/0 unchanged),
`lemma1_guard` self-test, `surprises.py` (20 entries, no new row this cycle
because nothing went against a stated expectation — an unstated one is just a
fact learned). Build 3746 jobs, base hash `cd7a22e688df` unmoved, audits
extended.

**Snag, bin 1:** two `simp … ; ring` branches failed opposite ways — `ring`
had no goals in the `if_neg` case and was needed in the `if_pos` case. Cost two
build cycles. The habit that fixes it is the one filed in SESSION 038 in a
different guise: prefer `simp only` with the exact rewrite, so the tactic's
behaviour does not depend on what the default simp set happens to close.

**Might-mean, unhedged:** the difference between "extension buys nothing" and
"extension destroys the certificate" is the difference between a dead end and a
trap, and only the second one explains why the `0.809` episode cost a headline
rather than an afternoon.


# SESSION 043 — night cycle 7: a second docstring promoted, and the linter finds a superfluous hypothesis

W19 and the GRH tier both need literature values the registers do not hold, so
per the standing constraint I took an in-repo item instead — and the ladder
audit's standard, turned on our own prose, found another instance of the disease
it was built for.

**`Gauge.lean` claimed, in a docstring, that `prop1` is LP-optimal in `(N, N⊛)`:
that no `Nsc ≥ αN + βN⊛` beats `(2,−1)`.** Only a single tightness witness was
ever proved. `Riemann/Optimal.lean` (axiom-free, sorry-free) proves the claim.

**Kill condition, stated first:** *if two test configurations do not suffice —
if some `(α,β)` satisfying both constraints still beats `2 − C` somewhere in the
regime — prop1's optimality needs more constraints and the docstring is
downgraded.* **It did not fire.** Two suffice:

* a single simple on-line zero (`N=1, N⊛=1, Nsc=1`) forces `α + β ≤ 1`;
* the lone mirror pair (`Gauge.pairOnly`: `N=2, N⊛=4, Nsc=0`) forces
  `α + 2β ≤ 0`.

A two-case split on `β ≷ −1` then gives `α + βC ≤ 2 − C` on `1 ≤ C ≤ 2`, with
equality at `(2,−1)`.

**And the certified statement is stronger than the prose it replaces.** I wrote
`β ≤ 0` into the theorem as an obviously-needed precondition and justified it in
the docstring. **Lean's unused-variable linter reported that the proof never
touches it.** Optimality holds for *every* `(α,β)` in the class. Filed as
`SURPRISES` S21 — corrected by tooling, and by a linter whose job is style,
which found a superfluous *mathematical* hypothesis.

So the register's standing consequence now rests on a theorem rather than an
assertion: **improving Proposition 1 requires leaving the two-moment world** —
a third moment `Σ m³`, [OPEN D]'s currency. The reduction and the ceiling want
the same missing input.

`Gauge.lean`'s docstring now points at the theorem instead of making the claim.
Audits extended; build green (3747 jobs); base hash unmoved.

**Might-mean, unhedged:** two of this project's load-bearing "the class cannot
do better" claims turned out to live in docstrings, and both were true — which
means the risk was never that we believed false things, but that we could not
tell which of our beliefs a reader was entitled to check.


# SESSION 044 — night cycle 8: the sweep, and the disease turns out to be cured

**Kill condition, stated first:** *if the sweep finds no further uncertified
class-impossibility claims beyond the two fixed this week, the "pattern" was two
coincidences and must not be generalised into doctrine.*

**It fired, in the informative direction.** Every impossibility claim in the
Lean docstrings is backed by a theorem. `Fujii.c0_lower_bound` ("Route I cannot
do better than `c₀ ≈ 0.16`") is a real proof, and `Gauge.offline_le_tight`
backs "the `(C−1)` cannot be improved to `(C−1)/2`" with a saturating witness. I
expected at least one of those to be prose. Filed as `SURPRISES` S22.

**`CLAIMS.md` filed** — the inventory, with three grades:

* **A — certified**: a machine-checked statement over the named class. **Ten
  entries**, including all five of this week's new ones.
* **B — certifiable but prose**: the disease. **Now empty.**
* **C — class undefined**: the claim quantifies over something informal. **Two
  entries** — W7's "cheap invariants" and the "post-1974 extremal technology"
  claim — plus E20's plane, already marked statistically unsupported.

**And that grade-C/grade-B distinction is the cycle's actual finding.** The two
remaining uncertified claims are *not* theorems-in-waiting. Promoting them would
require first **defining** "cheap invariant" and "post-1974 technology", which
is a research question, not a formalisation task. They cannot be cured by
proving them; they can only be **marked**.

So the pattern does not become doctrine. What survives is narrower and more
usable: a standing inventory plus one rule — **anything cited as a bound must be
grade A**. Added to `README.md` so an outside reader can check any bound we
quote against the file that says whether we are entitled to quote it.

One caveat carried forward rather than resolved: the ceiling (`0.6818287`) is
grade A but its certificate is **imported and not reachable from `import
Riemann`** — already parked for Joop.

Guards green, build 3747 jobs, base hash unmoved.

**Might-mean, unhedged:** the sweep that was supposed to find more sloppiness
found instead that the sloppiness was bounded, and the genuinely uncertifiable
claims are the ones whose *class* we never defined — which relocates the
project's remaining vagueness from its proofs to its vocabulary.


# SESSION 045 — night cycle 9: "cheap invariants" gets a definition, and grade C loosens

**Kill condition, stated first:** *if the class "cheap invariant" cannot be
defined without smuggling in the Euler product, it stays grade C permanently and
that is the finding.* **It did not fire**, and the reason is the whole cycle:
every constraint in the cheap family has **one shape** — an upper bound on
horizontal multiplicity — and that shape is pure counting, with no multiplicative
input anywhere.

`BoundedMult M D := ∀ γ, D.H γ ≤ M`. That is the class. Then
`Optimal.prop1_LP_optimal_cheap` (axiom-free): a linear bound entitled to assume
**any** multiplicity bound `M ≥ 2` still cannot beat `2 − C`. The two binding
configurations (`single`, `Gauge.pairOnly`) have `H ≤ 2`, so the cheap
invariants are satisfied by construction and cannot bind.

That is `FAILURES.md` `#3`'s certified reason — *"cheap invariants are satisfied
by construction; only the Euler product bites"* — restated as a theorem for the
two-moment LP.

**Scope, stated plainly and not quietly widened:** this certifies the vacuity of
**multiplicity bounds** for **this** extremal problem. The wider W7 claim, that
no classical invariant of any kind tightens `C`, quantifies over a class still
undefined and **stays grade C**. `CLAIMS.md` now carries both rows.

**And the cycle corrected the file it was following.** `CLAIMS.md` asserted one
cycle ago that promoting a grade-C claim "would require defining the class
first, which is a research question rather than a formalisation task". For W7 it
took one cycle. Filed as `SURPRISES` S23, and the guidance is revised in place:
**grade C means the class has not been defined yet, not that it cannot be** —
and when a C entry's claims all share one shape, that shape is usually the
definition.

Audits extended; build green (3747 jobs); base hash unmoved; 23 surprises, still
65% found by something that is not me.

**Might-mean, unhedged:** the vocabulary problem I diagnosed last cycle as the
project's residual vagueness turned out, on first contact, to be mostly a
naming delay — the informal classes were informal because nobody had needed them
precisely, not because they resist precision.


# SESSION 046 — night cycle 10: a fourth grade, and the first reproducibility defect

**Kill condition, stated first:** *if "post-1974 extremal technology" collapses
into the bandwidth-one class already certified by `ceiling_law256`, the entry is
a duplicate of an existing grade-A row rather than a new class.* **It did not
fire** — the registers are explicit that the `0.28pp` gap up to the
bandwidth-one ceiling "does not live in window shape", so the `v` slot is a
strict subclass.

**The class is definable, and the grading scheme was missing a bin.** The
claim's support is not a proof (A), not prose (B), not an undefined class (C).
It is a **numerical optimisation** — `N = 160` midpoint quadrature over windows
at `λ = 1`, giving `0.6725126` against Montgomery–Taylor's `3/2 − ϑ cot ϑ`.
`CLAIMS.md` gains **grade N: class defined, evidence numerical.** Cite with
"numerically" attached; never as a bound.

**Verified:** `3/2 − (1/√2)cot(1/√2) = 0.6725007036794116`, matching the
register to every quoted digit, with the reported optimiser `1.19 × 10⁻⁵` above
it — consistent with the stated quadrature error. So the *identification* is
sound as a numerical statement.

**And the finding that outweighs the grade: the optimisation's code is not in
this repo.** `forensics/` holds five scripts and none of them is a window
optimiser. `LEADS.md`'s table and `E.md`'s `18.18pp` "constants are properties
of the instrument" claim both rest on a computation a reader cannot re-run —
and neither can we. Filed as `ISSUES` #29, the first **reproducibility** defect
found here (as opposed to a mathematical one).

**Deliberately not repaired tonight, and this is the judgement of the cycle.**
Reconstructing the variational problem from memory would produce a script that
computes *something*, and presenting it as the original computation would be a
fabricated provenance — exactly the disease `provenance_lint.py` was built to
catch. The honest repair needs the source in hand. Until then the claim carries
grade N with an explicit "code not in repo" mark.

`SURPRISES` S24: I expected the last grade-C entry to either promote to A or
stay C. It did neither, and the scheme had to grow.

Guards green, build unchanged, base hash unmoved.

**Might-mean, unhedged:** the project has been careful about which of its claims
are *proved* and careless about which of its numbers are *re-runnable*, and the
two most-quoted numbers in the registers turn out to sit on the wrong side of
that second line.


# SESSION 047 — night cycle 11: the quantitative audit, and a retraction that sat below its own numbers

**Kill condition, stated first:** *if `#29` is the only unreproducible number,
the defect is isolated and the sweep says so rather than inflating it.*
**It fired for its stated scope.** Every computed figure in the registers traces
to a Lean theorem, an exact closed form, a declared axiom, or a marked
retraction — except the window optimisation, which remains the sole
missing-computation defect.

Traced and confirmed sound: `0.6818287` (zeta-23 Lean), `0.6725007` (closed
form, verified exactly), `5.035` (`= 1 + 6 × 0.6725`, and `nsc_row_opens`
carries it), `2.345` (`= 1 + 2 × 0.6725`), `19/27 = 0.703704`, `1.3275`
(`Fujii.Cbound_lt_record`), `0.85838` (declared axiom). The two ledger
thresholds being one-line consequences of the baseline was the reassuring part —
they are not free parameters anyone chose.

**But the sweep found a different species of defect, and it is the cycle's
finding.** `PRICES.md` carried the retracted `c`-table at lines 165–176 with the
retraction banner at line **183** — *below* the numbers. A reader scanning the
tables meets `c ≤ 7.995` before meeting the sentence that voids it. **Nothing
false was written; it was badly ordered**, which in a register meant to be
quoted from is the same hazard reached by a different route.

Fixed this cycle: a warning now sits immediately above both tables, naming
`ISSUES` #24 and #25 and saying plainly not to cite any figure below it.
**Standing rule added to `CLAIMS.md`: a retraction must appear *above* the
material it retracts, not merely somewhere in the same file.**

`SURPRISES` S25 — I expected the sweep to find more missing-code defects. It
found none, and found a category I had not been looking for.

Guards green, build unchanged, base hash unmoved.

**Might-mean, unhedged:** we have been auditing whether our claims are true and
whether our numbers are re-runnable, and this cycle adds a third axis nobody had
named — whether a reader meets the correction before or after the thing it
corrects, which is a property of *layout* and not of truth at all.


# SESSION 048 — night cycle 12: the ordering sweep, and a stale figure two hundred lines from its correction

**Kill condition, stated first:** *if `PRICES.md` was the only misordering, the
defect is isolated and the sweep says so rather than manufacturing more.*
**It did not fire.** A second instance exists — same species, different shape.

`LEADS.md` stated at lines 72 and 125 that L9's payoff window is **`+0.93pp`**.
The correction — that `0.93pp` is the *total* gap to the bandlimited ceiling, of
which CGdL 2020 already took `0.65pp`, leaving **`0.28pp`** — sat at line 284
and in `E.md`, **two hundred lines below the framing it corrects**.

This one is subtler than the `PRICES` case and worth the distinction: **both
figures are arithmetically true.** `0.93pp` really is the gap from `0.6725` to
`0.68183`. What was stale is the *framing* — calling it a "payoff window" when
two thirds of it is already spent. A reader asking "what is left to win" met the
wrong number first. Fixed by carrying the correction up to both points of use,
with the total/remaining distinction stated inline.

**And the sweep found the pattern done right, which I am naming as the
template.** `LEADS.md`'s W4 heads with *"RESURRECTED. The autopsy below reached
the wrong verdict; read the correction first"*, puts the correction immediately
under it, and keeps the superseded autopsy below and labelled. `E.md`'s E20m
does the same for the withdrawn `10/10`/`11/11` statistics — the withdrawal
precedes the inventory that reports them. **Verdict in the heading, correction
next, superseded material last and marked.**

**No `SURPRISES` row this cycle.** The kill condition was posed as a genuine
question rather than a prediction, so its not firing overturned nothing I had
stated. Recording the reasoning because the discipline is only worth having if
it visibly declines to manufacture entries.

Tally: two instances, both fixed; one model example. Guards green, build
unchanged, base hash unmoved.

**Might-mean, unhedged:** the two ordering defects were opposite in kind — one
was a false number correctly retracted too late, the other a true number framed
stalely — which means the axis that matters is not whether a statement is
right but whether the reader's *first* encounter with it is the current one.


# SESSION 049 — night cycle 13: X characterised from the other side

Back to mathematics after three hygiene cycles, and the item was the one that
needed no external inputs.

**Kill condition, stated first:** *if `NscStd` cannot be expressed through the
on-line counts alone — if some further feature of the configuration enters —
the sufficiency direction fails and `j` is not the whole residue.* **It did not
fire.**

`Riemann/Fiber.lean`, four new theorems, all axiom-free:

* `onAt` / `offAt` — the `k` and `2j` of the fiber, defined pointwise;
* `H_eq_onAt_add_offAt` — the decomposition;
* `count_eq_onAt` — on the line, a zero's *multiplicity* **is** the on-line
  count at its ordinate (all on-line zeros at one ordinate are the same point);
* `NscStd_eq_onAt_functional` — **`NscStd` reads `onAt` and nothing else**;
* `Nsc_reads_total` — `Nsc` reads `H` and nothing else.

**The pair is the finding.** The two ledger rows differ by exactly which part of
the fiber decomposition they consult: `Nsc` reads the total mass, which `μ_T`
supplies; `NscStd` reads the on-line part, which it does not. ISSUES #13's
two-row gap stops being a bookkeeping convention and becomes a consequence of
where each row looks.

Together with `Blindness`'s necessity this brackets X: **withhold the fiber
coordinate and no `μ_T`-invariant theory recovers the target; supply it and the
target is determined pointwise.**

**What is not proved, and I am naming it rather than rounding up:** the packaged
form — "same `μ_T` *and* same `offAt` everywhere ⟹ same `NscStd`" — needs a
counting step (each qualifying ordinate contributes exactly one zero to the
filter) that is not in the file. Sufficiency is **pointwise only** until that
lands. After three cycles spent emptying grade B, adding a fresh grade-B claim
tonight would have been the worst possible trade.

No `SURPRISES` row: the kill condition was a question, not a prediction.

Build green (3747 jobs), guards green, base hash unmoved.

**Might-mean, unhedged:** the ledger's two rows were never two conventions for
counting the same thing — they are two different queries against the same
decomposition, and the whole unconditional gap is the price of the query that
looks at the part `μ_T` throws away.


# SESSION 050 — night cycle 14: X is bracketed, globally

**Kill condition, stated first:** *if the counting step needs a hypothesis
beyond `(ordinates, offAt)` — a nodup, a finiteness condition, anything not
already in `ZeroData` — then the residue is larger than `j` and that is the
finding.* **It did not fire.** The theorem carries exactly the two stated
hypotheses and nothing else.

`NscStd_determined : D.ordinates = D'.ordinates → (∀ γ, offAt D γ = offAt D' γ)
→ D.NscStd = D'.NscStd`, axiom-free.

The route: `onOrd D`, the ordinates of the **on-line** zeros with multiplicity.
Its count at `γ` is exactly `onAt γ` (`count_onOrd`); `NscStd` is a functional of
it (`NscStd_eq_onOrd_functional`); `onAt` is determined by `μ_T` and `offAt`
(`onAt_determined`, straight from the fiber decomposition); and a multiset over
`ℝ` is determined by its counts. Four small lemmas, one conclusion.

**So the characterisation of X is complete, and global rather than pointwise:**

> **Withhold the fiber coordinate and no `μ_T`-invariant theory recovers the
> target. Supply it and the target is determined.**

Necessity is `Blindness.no_muInvariant_theory_computes_NscStd`; sufficiency is
`Fiber.NscStd_determined`. Between them the residue is pinned exactly — not
"at most", not "essentially", exactly.

Last cycle's LEADS entry said sufficiency was "pointwise only" and named the
packaging as the next item. **That text is corrected at its own location**, per
the ordering rule adopted two cycles ago — the update sits where the stale claim
was, not two hundred lines below it.

No `SURPRISES` row: the kill condition was a question and it did not fire; I
predicted the step was well-posed and closable, and it was.

Build green (3747 jobs), audits extended, base hash unmoved.

**Might-mean, unhedged:** the project spent a day proving what its instruments
cannot see and one cycle proving what would suffice, and the second was the
cheaper half — which suggests the hard part of an impossibility result is never
the impossibility, it is knowing exactly which coordinate to name.


# SESSION 051 — night cycle 15: the complete X theorem

**Kill condition, stated first:** *if any ledger quantity needs more than
`(μ_T, offAt)`, the characterisation is incomplete and that quantity is the
finding.* **It did not fire.** All five are determined, with exactly those two
hypotheses.

`ledger_determined` (axiom-free): `D.ordinates = D'.ordinates` and
`∀ γ, offAt D γ = offAt D' γ` give
`N = N' ∧ N⊛ = N⊛' ∧ Nsc = Nsc' ∧ NscStd = NscStd' ∧ N_off = N_off'`.

The split inside it is the content: **`N`, `N⊛` and `Nsc` need only `μ_T`** —
they were already known to factor through it — **while `NscStd` and `N_off` need
the fiber coordinate as well, and nothing beyond it.** `Noff_determined` goes
through `card_onOrd_add_Noff`, the on-line/off-line partition, so the off-line
count is `N` minus the on-line ordinate multiset's size, both determined.

Along the way `onOrd_determined` was lifted out of last cycle's proof into a
standalone lemma, which is what made the `N_off` argument a three-line
consequence rather than a repeat.

**So the exact statement of what the certificate class is missing is now a
theorem:** the ordinate measure, plus **one bounded natural number per crowded
atom**, and nothing else at all. Necessity from `Blindness`, sufficiency from
`Fiber`, and the sufficiency now covers every quantity the ledger reports rather
than the one row it was originally asked about.

Last cycle's LEADS entry is updated **at its own location** per the ordering
rule.

No `SURPRISES` row: the kill condition was a question and did not fire.

Build green (3747 jobs), audits extended, base hash unmoved.

**Might-mean, unhedged:** the two rows of the ledger were the visible half of a
cleaner fact — three of the five counted quantities live entirely inside `μ_T`
and two live entirely outside it, so the project's whole unconditional gap is
the price of exactly two numbers, and one of them is a difference of the other.


# SESSION 052 — night cycle 16: the residue is an upper bound, and I overclaimed it last cycle

**Kill condition, stated first:** *if the Landau weight turns out to determine
`offAt`, the evaluation problem is smaller than `w16_price.py` claims and that
pricing needs revisiting.* **It did not fire — the weight cannot.**

`landau_cannot_determine_offAt` (axiom-free): the swap pair — one atom of mass
two in each fiber state, at two distinct heights, exchanged — agrees on the real
Landau weight at **every** `x` and differs in `offAt` at `0`. So no amount of
sampling `Σ_ρ x^β` recovers the fiber coordinate. What distinguishes the pair is
*which ordinate carries the crowd*, which is exactly what the phase
`e^{iγ log x}` carries and the real weight discards. Census `#1`'s separability
problem, restated as a determination failure, and consistent with
`w16_price.py`'s verdict that the binding constraint is the phase.

**And asking that question exposed an overclaim of mine from last cycle.**
SESSION 051 said `(μ_T, offAt)` is *"the exact statement of what the certificate
class is missing… and nothing else at all."* **It is sufficient, not minimal.**
`offAt_not_minimal`: the same swap pair has the **same ledger** and **different
`offAt`**. So `ledger_determined` gives an *upper bound* on the residue, some
coarsening of `offAt` would also suffice, and **the minimal residue is not
identified**.

Filed as `SURPRISES` S26, and the stale text is corrected **at its location** in
`LEADS.md` and `CLAIMS.md` — not appended below, per the ordering rule. The
correction was found by asking the next question rather than by re-reading, which
is the standing observation of that register holding for the twenty-sixth time.

Two new grade-A rows in `CLAIMS.md`; audits extended; build green (3747 jobs);
base hash unmoved.

**Might-mean, unhedged:** "we know exactly what is missing" survived one cycle
before becoming "we know something that would suffice", and the gap between
those two sentences is the entire remaining research question — because a
coarsening of `offAt` that still determines the ledger would be a cheaper thing
to go looking for than `offAt` itself.


# SESSION 053 — night cycle 17: the residue narrowed, and an overclaim declined

**Kill condition, stated first:** *if relabelling ordinates can change any
ledger quantity, the residue genuinely depends on ordinate identity and the
profile idea dies.* **It did not fire.**

`ledger_relabel_invariant` (axiom-free): for **any injective** `σ`, relabelling
the ordinates leaves all five ledger quantities unchanged. Six supporting
lemmas — `relabel_N`, `relabel_H`, `relabel_count`, `relabel_Nstar`,
`relabel_Nsc`, `relabel_NscStd`, `relabel_Noff` — each a short `filter_map` /
`count_map` argument.

**So ordinate names are provably not part of the residue**, and last cycle's
swap pair is revealed as one instance of a general theorem rather than a lucky
example.

**And here is what I did not write.** The tempting sentence is "therefore the
residue is the profile — the multiset of `(mass, off-line mass)` pairs". That
does not follow: invariance under relabelling is weaker than determination by
the profile, because two configurations can share a profile without being
related by any relabelling. **`SURPRISES` S26 is one cycle old and records
exactly this species of overreach**, so the register says invariance and stops
there.

The minimal residue remains unidentified. What is now known: it lies below
`(μ_T, offAt)`, and it is relabelling-invariant.

No `SURPRISES` row — the kill condition was a question and did not fire, and the
overclaim was declined rather than made and retracted.

Build green (3747 jobs), audits extended, base hash unmoved, one new grade-A row.

**Might-mean, unhedged:** the discipline earned its keep tonight in the negative
— the cycle's most valuable output was a sentence I was able to see coming and
chose not to write, which is the first time the surprise register has prevented
an entry rather than recorded one.


# SESSION 054 — morning: four rulings executed, and the gate that patrols prose

Joop ruled "fix what needs fixed". All four items discharged.

**ISSUES #28(a) — the lakefile pin, fixed.** `rev` moved from `"main"` to the
manifest's exact commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, with the
reason in the file: a floating rev makes the dependency a trusted input carrying
someone else's uptime *and* someone else's content, and a `lake update` would
silently retarget every axiom-free claim here. Build green afterwards.

**`PairCeiling` imported from the root.** `Zeta23.PairCeiling.ceiling_law256` is
now reachable from `import Riemann` and verified axiom-free from there. Base
hash `cd7a22e688df` and axiom count `2` both unmoved — correct, because
importing a *proved* theorem changes reachability, not trust. The ceiling was
cited across four registers as ours; now a reader following our root can get to
it.

**R20 and R21 adopted into `LOOP.md`.** R20: hygiene cycles cap at three
consecutive, and any audit-of-an-audit needs new object-level input — the
standing form of the ad-hoc patch that stopped cycles 8–12. R21: a rung is a
blindness result **plus** a closure certificate for its class (W34a).

**ISSUES #29 — resolved, and it was my error.** Covered in SESSION 053's commit:
the specification was in `LEADS.md` three lines above the table.
`forensics/window_opt.py` reproduces all seven digits. `SURPRISES` S27.

**And the new instrument: `forensics/claims_gate.py`.** The night's error
profile — `tooling 9 / self 11`, every new entry self-caught — says the guards
are **saturated**, not failing: circularity/scale/quality stopped occurring
because instruments exist, and the error mass migrated to the unguarded surface,
which is the exactness of our own sentences. The gate scans for exactness /
uniqueness / completeness language and requires a converse witness; with none it
**rewrites** rather than blocks ("exact" → "sufficient", "the" → "a", "cannot" →
"is not known to").

Calibrated on both known failures: `S26`'s *"nothing else at all"* and `S27`'s
*"cannot be reproduced"* are both caught, and both corrected forms pass. This is
the first instrument here that patrols **prose** rather than mathematics — which
is where `S` always said the bugs live.

**Honest limit, per R17.** The gate flags 6 sentences in `CLAIMS.md`, 26 in
`LEADS.md`, 10 in `E.md`. **I have not triaged those 42.** Some are certainly
false positives — `E.md` is deliberately written in the language of felt
necessity. The counts are a to-do, not a verdict, and quoting them as a defect
rate would be the very error the gate exists to catch.

**Might-mean, unhedged:** the guards stopped catching things not because they
got worse but because they worked, and the useful reading of a silent instrument
is never "we are clean" but "the errors have moved somewhere it cannot see."


# SESSION 055 — the profile, partly read; and the pin's second half

**Stale-prompt note.** The loop fired with the overnight prompt, which still
listed four items as needing a ruling and said "overnight discipline applies
until he speaks". Joop had spoken and all four were discharged. Ran under day
discipline and re-armed corrected.

**`#28(a)`'s second half, which nearly got missed.** Pinning the lakefile made
`lake` warn that the manifest was out of date and suggest `lake update zeta23`
— **which is exactly the failure mode the pin exists to prevent.** Fixed by
editing the manifest's `inputRev` to the same commit by hand. Now
`lakefile.rev = manifest.inputRev = manifest.rev`, warning gone, build green on
the same revision. The "someone else's uptime" half is still open: there is no
vendored copy.

**The profile question, and the kill condition did not fire.** *If the
construction needed a finiteness or decidable-support fact unavailable for an
arbitrary `ZeroData`, the question was not answerable at this generality.* `Z`
is a `Multiset`, hence finite, so `ordinates.toFinset` exists classically with
no extra hypothesis.

`profile D` — the multiset of `(H γ, offAt γ)` pairs, one per distinct ordinate,
heights discarded. Two of the five ledger quantities are now read off it,
axiom-free:

* `N_from_profile` — `N` is the total mass;
* `Noff_from_profile` — `N_off` is the total off-line mass, via `offOrd` and
  `count_offOrd`, with the support inclusion handled by `Finset.sum_subset`.

**Three remain: `N⊛`, `Nsc`, `NscStd`.** They need the regrouping of a sum over
zeros into a sum over distinct ordinates, which `N` got for free from
`Multiset.toFinset_sum_count_eq` and the others do not. **Named, not claimed** —
the profile question is *partly* answered, and whether the profile determines
the whole ledger is still open.

No `SURPRISES` row: the kill condition was a question and did not fire.

Build green (3757 jobs), base hash unmoved.

**Might-mean, unhedged:** the pin's warning was a small trap of exactly the
project's favourite shape — a correct fix that makes a tool suggest the
incorrect one — and the only reason it was not walked into is that the reason
for the pin had been written down in the file rather than kept in a head.


# SESSION 056 — the profile determines the ledger

**Kill condition, stated first:** *if the regrouping needs a hypothesis beyond
`ZeroData`'s own finiteness, say so and leave the profile question partly
answered rather than adding hypotheses until it works.* **It did not fire.**
`Finset.sum_multiset_map_count` needs only `DecidableEq`, which is classical.

All five ledger quantities are now functionals of `profile D` — the multiset of
`(H γ, offAt γ)` pairs, one per distinct ordinate, **with the heights
discarded** — and all five are axiom-free:

* `N_from_profile` — total mass;
* `Nstar_from_profile` — sum of squared masses;
* `Nsc_from_profile` — count of mass-one atoms;
* `NscStd_from_profile` — count of atoms whose on-line part is one, using
  `onAt = H − offAt`, which is a function of the profile entry;
* `Noff_from_profile` — total off-line mass.

**So the residue is at most the profile**, strictly coarser than `(μ_T, offAt)`:
`ledger_relabel_invariant` and the swap pair already showed the heights carry
nothing, and this makes that concrete.

One lemma unlocked three of the five, exactly as predicted when the item was
queued — the regrouping of a sum over zeros into a sum over distinct ordinates
was the whole obstacle.

**Whether the profile is minimal is not proved and is not claimed.** A coarser
sufficient statistic may exist and nothing here rules one out. `CLAIMS.md`'s new
row says "sufficient; minimality not claimed" in those words, and the dispatch
was run through `claims_gate.py` before sending.

Build green (3757 jobs), audits extended, base hash unmoved.

**Might-mean, unhedged:** the object the certificate class is missing has now
been named three times, each coarser than the last — `offAt`, then
relabelling-invariant `offAt`, now the profile — and every narrowing came from
asking what the *previous* answer contained that the ledger never reads.


# SESSION 057 — first heartbeat cycle: the gate measured, and it found ordering violations

**First cycle under the cron heartbeat** (`e05114b3`, `23,53 * * * *`) rather
than self-rearming. The scheduler fired without me remembering it, which was
the entire point of the change.

**Kill condition, stated first:** *if `claims_gate`'s true-positive rate on
`CLAIMS.md` is zero, the gate is noise on live registers and needs its wordlist
narrowed before it can be cited at all.* **It did not fire: 3 of 6.**

**The three true positives were all stale text with a correction living
elsewhere in the same file** — the grade-C definition still asserting
unpromotability after `S23` falsified it, "a category that was never curable by
formalisation" after W7's was cured in one cycle, and "filed as #29 rather than
repaired tonight" after #29 was resolved. Fixed at their locations, per the
ordering rule. `CLAIMS.md` now reports **zero** unwitnessed flags.

**The finding worth keeping:** a wordlist scan for exactness language and a
retraction-ordering audit are completely different instruments, and they
converged on the same three defects. That is the closest this project has come
to independent confirmation about its own prose — and it suggests stale claims
and misplaced corrections are the same disease seen from two angles.

**The three false positives were two mechanical shapes**, both now excluded
without weakening the wordlist: *directives* ("Never cite as one") and *denied
quotations* ("not *that the class cannot be defined*"). Both calibration cases
`S26` and `S27` are still caught after the narrowing — checked, not assumed.

**Explicitly untriaged and still not a defect rate:** `LEADS.md` 25, `E.md` 10.

No `SURPRISES` row — the kill condition was a question and did not fire.

**Might-mean, unhedged:** the instrument built to stop me overclaiming spent its
first live run correcting three claims I had already been told were wrong, which
means the failure it actually guards against is not making a false statement but
leaving a corrected one standing.


# SESSION 058 — the third moment is on the visible side: two axes, not one

**Kill condition, stated first:** *if `Σ m³` is not `μ_T`-visible, it sits on
the blindness side and the registers' framing stands.* **It did not fire.**

`thirdMoment_determined`, `moment_determined` — axiom-free, and the proof is one
line each: `H γ = ordinates.count γ`, so every moment of the mass distribution
is a functional of `μ_T`.

**W35 made this visible one cycle after being filed.** Identifying `Σ m³` as the
level-3 coincidence-diagonal invited the obvious next question — which side of
the blindness is it on? — and the answer separates two things the registers had
been carrying together:

* **more moments of `μ_T`**: inside the class's *reach*. The gap is a theorem
  supplying the value, not an inability to see it.
* **the fiber coordinate**: not a functional of `μ_T` at any order, so no
  quantity of higher-moment information reaches it.

**Improving `prop1` therefore does not require breaking the blindness.** One of
the project's two open directions is an impossibility result; the other is an
ordinary missing theorem. They had been priced as the same kind of thing.

**Stated honestly: this is an addition, not a correction.** Nothing on file
asserted the contrary — the distinction simply had never been drawn, and I am
not manufacturing a retraction to make the finding look sharper.

Build green (3757 jobs), audits extended, base hash unmoved, one new grade-A row.

**Might-mean, unhedged:** the project has spent a day proving what cannot be
seen and priced its remaining work in that currency throughout, and it turns out
half of that work was never on the far side of the wall at all.


# SESSION 059 — minimality was ill-posed; the visibility split is the result

**Kill condition, stated first:** *if the minimality question is trivially
answered — the ledger being a sufficient statistic for itself — it is ill-posed
as asked and the finding is the reframing, not a minimal object.* **It fired.**

The ledger is five numbers; anything equal to it is trivially sufficient for it.
So "the minimal sufficient statistic" is the ledger, and asking for it teaches
nothing. Recording that as the answer rather than quietly switching to a
different question.

**The question with content is what shape the ledger has.** Every quantity is a
sum over atoms of one of five basis functions of `(m, j)`: `m`, `m²`, `[m = 1]`,
`[m − 2j = 1]`, `2j`. So the target is a **five-dimensional linear image of the
atom distribution**, and the visibility split is **3 : 2** — three basis
functionals read the mass alone and sit inside `μ_T`; two require the fiber
coordinate and are provably outside it.

`ledger_visibility_split`, axiom-free. **Every entry of that table was already
proved**, scattered across `Basic.lean`, `Blindness.lean` and `Fiber.lean`. The
work was the assembly, and the assembled statement is the clearest thing this
development has to say about its own position.

Combined with SESSION 058: of the two open directions, higher moments feed the
*visible* three and the fiber coordinate feeds the *invisible* two — so the
`3 : 2` split is also the split between "missing theorem" and "impossibility".

No `SURPRISES` row: the kill condition fired as one of its stated branches, and
nothing I had asserted was overturned.

Build green (3757 jobs), audits extended, base hash unmoved.

**Might-mean, unhedged:** three of the five things this project counts were
always readable by the instruments it inherited, two never were, and every
constant it has failed to move lives on the wrong side of a line that is four
lines of Lean to state.


# SESSION 060 — the three-moment LP is unbounded, and that localises the defect

**Kill condition, stated first:** *if the three-moment optimum is still `2 − C`,
the third moment buys nothing and W35 dies cheaply.* **It neither fired nor was
answered**, and the reason is worth more than either branch.

claude.ai registered a hand derivation before the run, flagged
`[HAND DERIVATION, UNVERIFIED, the LP decides]`. **Their algebra is exactly
right** — verified in exact rationals, not floats. The family
`(a,b,c) = (2−2s, 3s−1, −s)` gives `a + mb + m²c = (2−m) − s(m−1)(m−2)`,
feasible against every single-atom test for all `s ≥ 0`, with objective
`(2−C) + s(3C − 2 − C₃)`.

**Following it through certifies 175% of the zeros simple.** At `C = 3/2`,
`C₃ = C²`, `s = 5` the value is `7/4`, from a feasible point. That is
impossible, so a hypothesis is wrong — and the algebra was checked, so it is not
the algebra.

**The defect is the input region.** `(−2, 3, −1)` is a recession direction, so
the program is unbounded whenever `3C − 2 > C₃`. `C₃ ≥ C²` is necessary and far
from sufficient over **integer** masses: equality forces all atoms to share one
mass `C`, so `C = 3/2` is not realizable by *any* configuration. The LP was
being asked to price inputs no configuration can present.

**My own first attempt was worse and I am recording that.** I wrote a vertex
enumerator, and it returned values *below* `2 − C` — impossible, since
`(2, −1, 0)` is feasible and attains it. The numerics were wrong before the
mathematics was interesting. The exact-rational check found what floating-point
vertex enumeration had buried. Filed as `SURPRISES` S29.

**W35 is now neither alive nor dead, with its next step named:** the realizable
region of `(C, C₃)` over integer masses — a **W7-shaped realizability problem**,
this project's own genre.

`prop1_LP_optimal` is untouched: it quantifies over the two-moment class and is
proved from two configurations that are both realizable.

**Might-mean, unhedged:** an unbounded LP is not a failed computation but a
detector — it says the constraint set and the input set disagree about which
world they describe, and this one found that disagreement in a quantity two
instances had already agreed to price.


# SESSION 061 — W35 dies with a certificate: the third moment cannot help

**Kill condition, stated first:** *if the three-moment optimum is still `2 − C`,
the third moment buys nothing and W35 dies cheaply.* **It fired.**

Last cycle left the LP unbounded and named the missing piece: the realizable
region of `(C, C₃)` over integer masses. Computing it answers the whole question
in one identity:

> `3N⊛ − 2N − Σm³ = − Σ_atoms m(m−1)(m−2)`

and `m(m−1)(m−2) ≥ 0` for every natural `m`. So `Σm³ ≥ 3N⊛ − 2N` for **every**
configuration; the improvement term `3C − 2 − C₃` is never positive; the LP
optimum sits at `s = 0`, which is `prop1` unchanged.

`three_Nstar_le_thirdMoment_add_two_N`, axiom-free, with `N_eq_sum_H` and
`Nstar_eq_sum_H_sq` as the two regrouping lemmas it needed.

**The route is dead, not deferred.** No supplier can change an inequality true
of all configurations — RS, Fujii and Tsang are equally irrelevant to it. And
the pricing cost one cycle while the literature fetch it pre-empted would have
cost a session: **the inward-pricing-before-outward-reading ordering paid on its
first use.**

**The obstruction is the project's own `6`.** `m(m−1)(m−2)` vanishes at `m ≤ 2`
and equals `6` at `m = 3` — the same `6` as `six_mul_NscStd_le`. The third
moment sees atoms of mass `≥ 3` and nothing else, and sees them in the direction
that costs. The `/6` census result and this obstruction are two readings of one
polynomial, which is the first time two of this project's results have turned
out to be the same fact.

**Live remainder, stated so the death is not overread:** this kills the level-3
diagonal's use as a third moment in a *linear bound on `Nsc`* — the only
consumer W35 named. The level-3 correlation may matter to some other consumer;
that consumer would need its own pricing.

No `SURPRISES` row: the kill condition fired as stated and nothing I asserted
was overturned.

**Might-mean, unhedged:** the quantity that would have improved the bound is
identically the quantity that measures crowded atoms, so the route asked the
zeros to be simple by paying attention to exactly the places they are not.


# SESSION 062 — List F filed, and F4 died on arrival by its own kill condition

claude.ai's fourth register: **fictions**, derivations narrated as if they
existed, each naming the cast that would have to be hired. Filed as `F.md` with
the protocol intact — never killed, converted to a rung when a cast is proven
impossible.

**F4 arrived flagged "may not be fiction" and its kill condition fired
immediately, twice, without a paper.**

The fiction: the gate's power-requirement is an artifact of sharp cutoffs, so
Cesàro-weighted shift averages would drop amplification from `h` to `h^ε`.

1. **The premise is already false in our own record.** `ISSUES` #27 states the
   weight as `Σ_{|k|<h}(h−|k|)`. **That is the Fejér/Cesàro weight.** The
   smoothing the fiction proposes adding was in the derivation from the start.
2. **And no shape helps.** With per-shift absolute bounds `|E_k| ≤ E`, the total
   error is `Σ w_k|E_k| ≤ E·Σw_k`, and the main term fixes `Σw_k ≈ h²` for every
   admissible weight. Checked for Fejér, flat and Gaussian: same total mass,
   same `h²E`, whatever the sup or profile.

**So `#27` strengthens from *"MRT is too weak"* to *"no reweighting of the GM
identity can be strong enough"*** — annotated at its own location, per the
ordering rule. Per the F-protocol, F4 converts to a rung: a ceiling theorem for
the class of shape-modified GM bridges.

**The live remnant is not smoothing but cancellation.** The one escape left is
correlated control across shifts rather than per-shift absolute bounds — which
is precisely F5's existing cast (a large-sieve inequality for Landau sums). F4's
remnant is absorbed there rather than kept as a separate item.

**Scope, stated:** this argues from the *recorded* derivation, which is itself
`[RECALL]` from Goldston's survey §9. If that is misrecorded, the conversion
inherits the error. Not a Lean theorem.

Two other annotations while filing: F1's hardest cast member has a proved
special case (`landau_discriminates` is the one-point off-line evaluation), and
F2 should be read against `SESSION 061` — the third moment provably cannot help,
so F2 asks whether the full moment sequence does what no finite prefix can.

**Might-mean, unhedged:** a register of things that are not true earned its keep
in the hour it was created, because narrating a route one theorem past its
terminus is the fastest way to discover the terminus was load-bearing.


# SESSION 063 — F4's rung gets its certificate; second shelf filed; F15 corrected

**Kill condition, stated first:** *if the worst-case total were not attained for
every weight, shape could matter and F4's conversion would be premature.* **It
did not fire** — the attaining adversary is explicit.

**F4's rung now has its R21 certificate.** Last cycle converted F4 to a rung on
a prose argument, which quietly created exactly the grade-B claim the standing
rule forbids. `Capacity.reweighting_worst_case`,
`weighted_sum_le_mass_mul` and `equal_mass_equal_worst_case` (axiom-free) close
it: the worst case `(Σw)·E` is **attained** by the adversary who sets every
error to `E`, so equal-mass weights admit equal worst cases and shape is
irrelevant. Grade **A**.

Same move as `unbounded_below_of_neg_outside` — find the class's limit by naming
what the adversary does, not by estimating.

**Second shelf F11–F18 filed**, with the sober-shadow field intact.

**And F15's cast analysis is wrong, by our own theorem.** It argues that
finiteness of off-line zeros is *"immune to the blindness theorem because
finiteness is not a `μ_T` statement."* But finiteness is a statement about
`N_off`, and `N_off` is **one of the two ledger components proved not to be a
`μ_T` functional** (`ledger_visibility_split`). The weaker goal does not dodge
the obstruction; the obstruction applies to it at full strength.

**That makes F15 harder than advertised, not easier** — and its second half
(Bombieri's exactness clause converting finiteness to zero) survives untouched,
which is the part the census has genuinely never treated as a target's second
half. Recorded in `F.md` rather than only in a reply, because a cast member
found *missing* is still a cast annotation.

Two shadows flagged as near-certainly already employed, per the shelf's own
exemption: **F12** (period-finding and the explicit formula share one
exponential sum — a dictionary no census entry has priced) and **F17** (Siegel
mining Riemann's Nachlass into the Riemann–Siegel formula is the field's proof
that negative literature contains positive theorems).

Build green (3757 jobs), one new grade-A row, base hash unmoved.

**Might-mean, unhedged:** the second shelf's job is to mark where the vocabulary
runs out, and the first thing it marked was a place where *ours* had already
run out in the opposite direction — F15 assumed a weaker target escapes the wall
when we had proved, three cycles ago, that the wall is built exactly there.


# SESSION 064 — the moment wall generalises to every order

**Kill condition, stated first:** *if the extremal witnesses had a nonzero
factorial moment at some order `≥ 3`, that order's constraint could exclude them
and the wall would be only at three.* **It did not fire.**

claude.ai scored its own prediction against last cycle's identity and saw the
generalisation, which is stronger than what I proved:

> both configurations that force `prop1`'s optimum have **every** descending
> factorial moment of order `≥ 3` equal to zero.

`single` has mass 1, `Gauge.pairOnly` has mass 2, and `m(m−1)⋯(m−k+1)` vanishes
for `m ≤ 2 < k` — more factors than the mass has room for.
`Optimal.moment_route_walled` and
`Blindness.factMoment_eq_zero_of_masses_le_two`, axiom-free.

**A moment inequality cannot exclude a configuration on which it is tight.** So
no moment constraint of any order — third, fourth, or the whole sequence —
removes the binding witnesses, and a constraint that cannot exclude them cannot
move the bound. **The moment route is walled at every order**, with last cycle's
`Σm(m−1)(m−2) ≥ 0` revealed as the `k = 3` case of a general fact.

**F2 answered at inequality grade, and re-filed at the grade that survives.**
Its question — *does the full sequence do what no finite prefix can* — is
answered **no**. What remains is equality-grade: recovering the mass
distribution needs asymptotic *identities*, not bounds. Annotated in `F.md` at
F2's own location.

**Accepted from the dispatch without independent check, and marked as such:**
that admissible weights *are* autocorrelations (`w = W ⋆ W`), so `Σw = (ΣW)²`
is forced by positivity rather than chosen. That would make F4's rung the same
theorem as the two-sided-window episode. It is a structural reading of a
`[RECALL]` derivation and I have not verified it; the rung's certificate does
not depend on it.

**And the residue they name is worth recording as filed:** after stripping
circularity, scale, quality, shape and now moments, the irreducible remainder is
**cancellation** — which is analytic number theory's founding difficulty,
unchanged. Read as evidence the instruments are flush against the real wall
rather than as disappointment.

**Might-mean, unhedged:** two days of removing every removable obstruction has
returned the project to the exact difficulty the field named at the start, which
is what success looks like when the thing you are subtracting is your own
confusion.


# SESSION 065 — W32 run: the atom bundles classify 3 of 11

**Kill condition, stated first:** *if every census entry needs both bundles, the
test has no discriminating power and W32 dies.* **It did not fire** — and what
happened instead is more informative than either branch.

**Tally: M = 2 (#1, #3), S = 1 (#11), neither = 8. No entry needs both.**

**The test discriminates, and it classifies only 3 of 11.** The atom bundles
sort *supply* failures; eight elevenths of this census is information limits,
capacity limits and logic defects — not supply. **Five of those eight are
theorem-backed** (`no_muInvariant_theory_computes_NscStd`, `ceiling_law256`,
`ledger_visibility_split`, `two_le_Hr_of_off_line`,
`no_gain_past_known_integral`), which is why this attribution is defensible
where the earlier plane-classification was not: it is mostly not judgement.

**The consistency check was unplanned and is the cycle's real find.** This
`3 : 8` split matches T3(b)'s `3 : 8` (RH-consuming vs unconditional) and sits
alongside `ledger_visibility_split`'s `2 : 3`. **Three independent
classifications of the same eleven objects agree on where the line falls** —
entries needing an arithmetic bundle are the entries consuming a hypothesis;
entries needing neither are those whose obstruction is a property of the
instrument.

**Consequence for W28, stated plainly:** an `Atom` structure supplying M and S
addresses `2/11` and `1/11` of the recorded difficulty. The interface is worth
having for what it makes *statable* — the D–H and Beurling counterexamples
bracket it — but it was never a route to the census's main mass, and saying so
now is cheaper than discovering it after building the thing.

Per R19 this is a per-entry attribution rather than a pattern-claim; the three
judgement rows are marked, no p-value is quoted, and none is available.

**Might-mean, unhedged:** the project has now sorted its own failures three
times by three unrelated criteria and got the same partition every time, which
is either a very robust fact about the census or a very stable fact about the
sorter — and the five theorem-backed rows are the only reason to believe the
first.


# SESSION 066 — E24: the fourth approach, and one correction at the point of use

Joop's question *"why are the zeros not bothered?"*, pursued literally, turns
out to name a proof shape: **rigidity** — that the moduli space of objects like
`ζ` is a point. Filed as **E24**, with the E22/E23 merger it forces.

**And it is the only shape that has ever killed a Riemann Hypothesis.**
Weil/Deligne did not locate the Frobenius eigenvalues; the geometry **forced**
the weights. The *why* was the proof.

**Two cast members are already theorems** `[RECALL, UNVERIFIED]`: Hamburger 1921
(`ζ` determined by its functional equation plus analytic conditions) and
Kaczorowski–Perelli (Selberg degree `0 < d < 1` empty, degree `1` exactly `ζ`
and shifts). **The negative control is ours and it is in the repo:**
`Blindness.lean` opens by stating that **Davenport–Heilbronn *is* a
`ZeroData`** — so functional equation plus counting is provably *not* rigid, and
D–H is promoted from testbed column to the programme's **anti-rigidity
control**.

**⚠️ One correction, made at the point of use.** The dispatch attributes to W7
the certified claim that *"the Euler product is the only expensive
constraint."* **It is not certified.** `CLAIMS.md` carries W7 in two rows: the
precise part — multiplicity bounds are vacuous — is grade **A**
(`prop1_LP_optimal_cheap`); the general claim is grade **C**, its class still
informal, explicitly **not a bound**. It remains the best candidate answer to
*what leaves no room*; it is not a proved one, and that difference is the entire
subject of `CLAIMS.md`.

**The substantive upgrade: the constitutive criterion.** E22 asked for axioms
*sufficient* for RH; E24 asks for axioms that are **constitutive** — sound,
**characterising** (Hamburger-style), and forcing. `(1)+(3)` certifies;
`(1)+(2)+(3)` explains, and the cash-out is not aesthetic: **explanatory proofs
transfer.** A constitutive set forcing RH would be a schema for the Selberg
class, as Deligne's argument covered every variety while Weil positivity covers
nothing beyond its own equivalence.

**The merger.** The atom is the *why* as axioms; the ladder is the *why* as the
impossibility of everything why-less — each rung certifies its class **leaves
room**. One approach, two directions, meeting at the constitutive axiom set.

**And W32, one cycle old, sharpens what the new column can be worth.** The atom
bundles classify `3/11` of the census; the other eight are information, capacity
and logic limits. A constitutive axiom set would have to speak to the eight, and
nothing in M or S does — **so rigidity is not a refinement of the bundles but a
different demand on them**, and W28's whiteboard hour should treat it that way
rather than as an extra checkbox.

**Might-mean, unhedged:** the project spent two days proving what its
instruments cannot see, and the answer to *why the zeros are not bothered* is
that nothing was ever asking them — which reframes every impossibility on the
board as a report about the asker.


# SESSION 067 — anti-rigidity certified, and the two strengths kept apart

**Kill condition, stated first:** *if anti-rigidity genuinely requires
Davenport–Heilbronn, the claim rests on `[RECALL]` literature and must be graded
that way rather than certified.* **It did not fire.**

E24 promoted D–H to the programme's anti-rigidity control on the strength of a
docstring. The content that actually matters — *the axiom set leaves room* —
needs only a witness, and the repo already had two.

`zeroData_not_rigid` and `zeroData_admits_both`, axiom-free: `Gauge.pairOnly` is
a lawful `ZeroData` with **every** zero off the critical line, and
`config 1 0 (1/4)` is one with **none**. So functional-equation symmetry plus
counting is silent on position in *both* directions — which is precisely what
"leaves room" means, and it needs no literature at all.

**And the two strengths are now kept apart in the register, because they are not
the same fact.** `pairOnly` shows the **combinatorial** axioms have room. D–H
shows that room is **occupied by a genuine analytic object** with a Dirichlet
series and a functional equation. The first is certified here; the second stays
`[RECALL]` — and the second is the one that makes the control interesting.
Quoting them interchangeably would be exactly the conflation `CLAIMS.md` exists
to prevent, so E24's paragraph now carries both at their own grades.

One `Optimal.single` reference had to become `config 1 0 (1/4)`: `Optimal`
imports `Fiber`, not the reverse, and the witness had to live on the right side
of that edge. Noted because it is the second time this week the import direction
decided where a theorem goes.

Build green (3757 jobs), one new grade-A row, base hash unmoved.

**Might-mean, unhedged:** the anti-rigidity control the fourth approach wanted
was sitting in `Gauge.lean` from the second day, built for an entirely different
purpose, which is what it looks like when a project's early instruments turn out
to have been aimed at the right object before anyone could say why.


# SESSION 068 — tiering adopted; the S-file gets its capstone

A filing cycle, and the filing is substantive.

**claude.ai proposed tier-1 anti-rigidity in a dispatch that arrived after it had
been proved here.** They suggested `depthPair` as witness; the compiled version
uses `Gauge.pairOnly` and `config 1 0 (1/4)`. **Two instances reached the same
next step from opposite ends of the seam inside one hour** — recorded because
the seam's whole justification is that the two sides do not converge, and this
is a case where they did.

**Their tiering is better than my phrasing and is adopted:**

* **Tier 1** — the bundle `{reflection symmetry, counting}` admits models with
  off-line zeros. **Certified, D–H-free.**
* **Tier 2** — anti-rigidity persists among *genuine analytic objects*.
  **`[RECALL]` until Davenport–Heilbronn 1936 is read.**

D–H upgrades rather than disappears, and tier 2 can wait **precisely because
tier 1 carries E24's immediate claim**. `CLAIMS.md` and E24 both re-worded.

**The S-file gains its capstone, and it is their reading.** W32 located
empirically what `S.md` drew conceptually on day one: the census is **3/11 about
`ζ` and 8/11 about the mirror**. Constitutive axioms speak of the object; the
eight speak of askers. **So the eight can never be corollaries of any
constitutive axiom set** — a constitutive proof would discharge the three and
leave the eight standing forever as true theorems about instruments. It would
not refute our impossibility results; it would walk around them.

That makes E24's kept line exact rather than decorative: **every question we
have certified as unanswerable was a question about the questioner.**

**They also accepted the W7 grade correction and proposed the obvious symmetric
fix** — running `claims_gate`'s wordlist over outgoing dispatches at *their*
outlet too. The gate caught their overclaim one seam-crossing late, which is the
gate working at the wrong station.

**Might-mean, unhedged:** the instrument that proves the axioms leave room is a
configuration built to prove we are blind, which means this project's
impossibility results and its constructions are the same objects read in
opposite directions — and that is probably why the census keeps sorting `3 : 8`
no matter who sorts it.


# SESSION 069 — the seam measured, and it is not yet measurable

**Kill condition, stated first:** *if the correction record shows the two
instances mostly agreeing rather than correcting each other, the seam has
already converged and its value claim is stale.* **It did not fire** — and the
measurement does not confirm the claim either.

`FRAMING.md` asserts the asymmetry is maintained *"because two instances of one
model will otherwise converge, and convergence destroys the check."* Last
cycle's tier-1 convergence made that worth counting rather than repeating.

**Mechanically countable:** claude.ai → VPS, **2** (`S18`, `S27`); VPS →
claude.ai, **2** (E24's W7 grade correction; F15's cast analysis, corrected by
`ledger_visibility_split`); convergence, **1**.

**At `n ≈ 5` that is consistent with almost any underlying rate.** The seam's
non-convergence is **not yet measurable**, and the design rationale's honest
status is *unverified*, not *confirmed*. Filed in `FRAMING.md`'s appendix — the
main document is claude.ai's, and this is a measurement of its claim, so it
belongs in the half that is mine.

**I had been about to write the reassuring version** — "corrections flow both
ways, the seam is earning its cost" — and the count does technically support
that. It does not support the stronger sentence the design rests on. The
difference between "not falsified" and "confirmed" at `n = 5` is exactly the
gap `CLAIMS.md` was built to police, and it applies to our methodology as
readily as to our mathematics.

What the record *does* support: corrections travel in both directions, so the
two sides are at least not producing identical output. `SURPRISES` says the same
from another angle — `tooling 9 / self 12 / Fable 3 / c.ai 2 / source 2 /
Joop 1`.

Per R19 no rate is quoted and none is available.

**Might-mean, unhedged:** the project has spent a day proving that its
instruments cannot see certain things, and the first time it turned that
standard on its own methodology the answer was the same — the seam's central
claim is currently an article of faith with five data points, which is precisely
the epistemic position we refuse to accept from a certificate.


# SESSION 070 — I measured the wrong convergence; the right one is worse

**Kill condition, stated first:** *if "who endorsed before the catch" is not
determinable from the record for most entries, the protocol starts from now and
the historical rate is unmeasurable.* **It fired partially** — for most entries
the question does not arise (claude.ai never saw the claim), but the two that
matter are fully determinable.

**The distinction I lacked**, from claude.ai's audit: **proposal convergence is
not the failure mode the seam exists to prevent.** Two instances handed
identical inputs and converging on the obviously-right next move is
*replication* — a confirmation signal. The seam's claim was never "we will
propose different things"; it is **"we will not miss the same things."**

**So the quantity is correlated error, and on that metric the record is worse
than SESSION 069's table:**

* **S5** — E20's `11/11`: claude.ai supplied the plane framing, I classified
  with the hypothesis in hand. **Shared priming.** Caught by a *blind Fable
  agent*.
* **S6** — T3(b)'s answer: I disclosed the sealed predictions, claude.ai
  endorsed after reading them. **Anchoring on disclosure.** Caught by
  *`provenance_lint`*.

**Correlated misses: 2. Rescued by the seam: 0.** I counted the flows that
happened rather than the stops that did not.

**`FRAMING.md`'s main text is amended to the stronger claim**, proposed by
claude.ai about its own document: the seam's error-independence is a **design
hope with two failures and two successes**, and the system's *measured* safety
property is **checker heterogeneity** — kernel, lint, blind agents, escrow, the
operator, sources. Every doctrine addition since day one increased heterogeneity,
not asymmetry. That sentence is supported at current `n`; the old one was not.

**Protocol pre-registered** in `SURPRISES.md`: new entries carry `endorsed-by`
(`VPS`/`c.ai`/`both`/`neither`) and `caught-by class`. **Kill condition: if after
twenty further entries the `both` rate exceeds the single-instance rate, the
seam is negative-value as a check and its budget reallocates to more
heterogeneous layers.** `surprises.py` now reports the correlated count.

**Might-mean, unhedged:** the seam was sold as an independence guarantee and is
actually a replication engine with a weak checking side-effect, and the only
reason the project did not compound its two shared errors is that it kept
building instruments that share nothing with either instance.


# SESSION 071 — a false identity of my own, caught two cycles late

**Kill condition, stated first:** *if `m(m−1)` and `m(m−1)(m−2)` agree for all
`m ≥ 3`, the "one polynomial" claim stands and there is nothing to correct.*
**It did not fire.**

SESSION 061 and `LEADS.md` both say the `/6` census result and the third-moment
obstruction are **"two readings of one polynomial"**, and that the shared `6`
**"is not a coincidence"**. **Both sentences are wrong.**

* `six_mul_card_le_Nstar_sub_N` runs on `N⊛ − N = Σ m(m−1)`.
* The third-moment obstruction runs on `Σ m(m−1)(m−2)`.

They agree at `m = 3` — `3·2 = 6` and `3·2·1 = 6` — **and nowhere else**: `2`
against `0` at `m = 2`, `12` against `24` at `m = 4`. **The shared `6` is
exactly the coincidence I declared it not to be.**

What survives, and it is worth keeping: both bounds become active at `m = 3`,
because that is where crowding starts. **The threshold is shared; the polynomial
is not.**

Filed as `SURPRISES` S30, and the meter marks it **self-caught LATE** — only the
second such entry after `S2`. Late is the expensive kind, and two cycles is
late: the claim was quoted onward in a dispatch before it was checked.

**One convention question this raised, resolved explicitly.** The ordering rule
says corrections go at the location of the stale text; `LOOP.md` says
`SESSION.md` is append-only. Resolution: **SESSION entries are a log of what was
believed at the time and are not rewritten; the live registers are.** The
correction sits in `LEADS.md` at the error's own location, `SURPRISES` carries
the scoring, and this entry is the pointer for anyone reading 061 forward.

**And the class of error is one no current instrument covers.** `claims_gate`
scans for exactness language; *"two readings of one polynomial"* has none — it
is an assertion of **identity between two objects**, which is a shape neither
the lint (typed inputs), the gate (exactness wording), nor the kernel
(unstated claims) checks. **Fourth error class, fourth instrument gap**, and
this one was caught only by re-reading with a specific suspicion.

**Might-mean, unhedged:** the pleasing sentence — two results turning out to be
one — is the exact shape this project keeps getting wrong, because a claimed
unification is an exactness claim wearing the costume of an insight.


# SESSION 072 — the identity detector, and W38 filed

**Kill condition, stated first:** *if identity patterns fire so broadly that the
true-positive rate is near zero, the class is not lintable and the finding is
that it needs a human check instead.* **It did not fire — the rate is ≈ 3/7**,
comparable to the original gate's 3/6 at first measurement.

**The instrument was purchased by exactly one failure**, which is the house
rule: S30, where *"two readings of one polynomial"* was false and had been
quoted onward before checking. `claims_gate` gains an `IDENTITY` wordlist, on
the principle that **an identity claim is an exactness claim wearing the costume
of an insight**.

Both of S30's false sentences are caught; the corrected form passes. The one new
`CLAIMS.md` flag is a **false** positive — *"the same hazard by a different
route"* is metaphorical. `S.md`'s six run roughly 3 true, 3 false.

**The false positives cluster on one shape — definitions and file premises**, and
I left the exemption **unbuilt on purpose** so the rate above measures the
instrument as it actually stands rather than as I would like it to.

**W38 filed: the equivalence atlas.** Every *proven* RH-biconditional classified
by face, with crossings as the payload. The definition that carries the weight:
a crossing must connect the faces **without routing through "zeros on the line"**
— the classifier checks the **proof's route**, not the statement pair, because
every entry trivially crosses through RH itself.

**And the brief's blinding is designed against the failure mode the seam has
actually exhibited.** After `S5` (shared priming) and `S6` (anchoring on
disclosure), W38 puts one instance on faces, the other on proof routes, and
sealed hashes with Joop. **First W-item built against our measured correlated
misses rather than against the imagined one** — two cycles after that
measurement existed.

Both outcomes pay: a crossing is cross-plane certification in theorem form; no
crossing makes **RH the unique articulation point of its own equivalence
graph**, a finding about the literature independent of `ζ`, which hands the
fourth approach its sharpest constraint — the constitutive axioms must **be** the
junction.

**Might-mean, unhedged:** the atlas is a map of every road to one city, valuable
precisely because the roads were built by a century of travellers who never
arrived — and if the map shows no road connecting two districts except through
the city, that is a theorem about the city nobody has to enter to prove.


# SESSION 073 — the shadow has a size: `⌊m/2⌋ + 1` per atom

**Kill condition, stated first:** *if two distinct fiber states shared the same
`N_off`, the orbit would be smaller than claimed and the ambiguity count wrong.*
**It did not fire** — `N_off = 2j` separates them, so `j` indexes the orbit
faithfully.

Since W28 the registers have called the missing datum *"one bounded natural
number per crowded atom"* and never said **how** bounded. It is `⌊m/2⌋`:
the states over mass `m` are `(m − 2j, j)` for `0 ≤ j ≤ ⌊m/2⌋`, all sharing one
`μ_T`, all separated by `N_off`. So at an atom of mass `m` the certificate class
cannot tell **`⌊m/2⌋ + 1`** configurations apart — one alternative at `m = 2`
and `3`, two at `4` and `5`, and **the shadow grows linearly in the mass**.

`gauge_orbit_size`, `fiber_states_share_ordinates`,
`fiber_states_distinguished` — axiom-free.

**And the formula's boundary case is its own R17 witness.** At `m = 1` it gives
orbit size **1**: a simple atom is unambiguous. `Noff_eq_zero_of_simple` says
the same thing by a completely different route, proved four cycles ago. Two
independent paths to one fact, and I did not arrange it — the formula produced
it as the `m = 1` case.

That is the difference between this and `S30`'s false unification, and worth
naming while both are fresh: **there I asserted two results were one and they
were not; here two results agree at a point and I am claiming only the
agreement.** The check is whether the identity is *derived* or *declared*.

Build green (3757 jobs), one new grade-A row, base hash unmoved.

**Might-mean, unhedged:** the blindness is not a wall of fixed height but one
that rises with the crowd — every additional pair of zeros at an ordinate adds
exactly one configuration the instruments cannot exclude, so the harder a place
is to see into, the more there is in it to miss.


# SESSION 074 — the shadow is not everywhere: it lives on the odd atoms

`SESSION 073` counted the orbit; this cycle asks **which of its members the
invisible row can even reach**, and the answer localises the blindness by half.

**Kill condition, filed before the section was written:** *if some even-mass
fiber state contributed to `NscStd`, the localisation would fail and the
blindness would not be confined to odd atoms.* It did not fire.

`config_NscStd` (new, axiom-free): a fiber state `config k j a` contributes
`if k = 1 then 1 else 0` to `NscStd`. The on-line part is `k` copies of one
point, so `onAt = k`; the off-line points are excluded by position. Both
directions are then immediate:

* **`even_mass_NscStd_zero`** — over an even mass every `k = m − 2j` is even,
  so no state contributes. And `m`'s parity is `μ_T`-visible
  (`config_parity`), so at an even atom `NscStd`'s contribution is not merely
  constant across the orbit — it is **determined by `μ_T` alone**.
* **`odd_mass_NscStd_ambiguous`** — the converse, so the localisation is
  witnessed both ways: for odd `m ≥ 3`, `config m 0 a` and
  `config 1 ((m−1)/2) a` share their ordinates and disagree on `NscStd`.

So of the `⌊m/2⌋ + 1` states counted last cycle, the ones that matter for the
invisible row are confined to **odd masses `≥ 3`**. At `m = 1` there is one
state and it contributes `1`; at every even mass the contribution is `0` and
visibly so; the entire `NscStd` shadow is the odd crowd.

Build green (3757 jobs), one new grade-A row, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** half the crowded places were never dark — the
certificate class can already see that an even pile-up contributes nothing to
the standard-simple count, and every question about what it cannot see should
be asked about odd atoms only.


# SESSION 075 — the profile is not minimal, and the question was the wrong shape

Queue item 3: *is the profile minimal — is there a coarser sufficient statistic
for the ledger?*

**Kill condition, filed before construction:** *if the ledger separates every
realisable pair of distinct profiles, minimality stands unrefuted and I report
the question open rather than answered.* **It fired.**

`twoAtom_profile` (new): the two-atom configuration with mass `k₁+2j₁` at
height `0` and `k₂+2j₂` at height `γ` has profile
`{(k₁+2j₁, 2j₁), (k₂+2j₂, 2j₂)}`. Built on `configAt`, `superpose`,
`offAt_configAt_self/other` — all already in the file.

`profile_not_minimal` (new, axiom-free): exchange the off-line mass between the
two atoms.

| | atom at `0` | atom at `γ` | profile |
|---|---|---|---|
| `A` | mass `4`, `2` off-line | mass `2`, on-line | `{(4,2),(2,0)}` |
| `B` | mass `4`, on-line | mass `2`, `2` off-line | `{(4,0),(2,2)}` |

Distinct profiles; `N = 6`, `N⊛ = 20`, `Nsc = 0`, `NscStd = 0`, `N_off = 2` on
both. Every ledger equality is proved *through* last week's `*_from_profile`
theorems — the profile computation is done once and the five ledger values fall
out as arithmetic on two explicit multisets. That is the first time the profile
theorems have been used as instruments rather than stated as results.

**What the finding actually is.** `profile → ledger` is not injective, so the
ledger is a strictly coarser sufficient statistic and the profile is not
minimal. But that is cheap: *any* target is its own minimal sufficient
statistic, so the queued question is degenerate as posed. Re-posed in `LEADS.md`
under two restrictions that are not degenerate — minimal among
`μ_T`-augmentations, and minimal among ordinate-*local* statistics. The
counterexample above is unavailable under locality, because it works by moving
data between ordinates; so the local form is genuinely open and is the one the
blindness programme actually wants.

Build green (3757 jobs), one new grade-A row, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the ledger cannot tell which crowd the off-line zeros
are hiding in, only how many there are in total — so any instrument that reads
the ledger alone is blind to the *distribution* of off-line mass across the
crowds, and that is a second blindness, distinct from the fiber one.


# SESSION 076 — the guard against unwitnessed claims was exempting any sentence that named a file

Queue item 1: triage `claims_gate`'s `CLAIMS.md` flags and report the
true-positive rate honestly.

**Kill condition, filed first:** *if all flags are false positives, the gate
measures nothing on this register and I should stop quoting its count rather
than keep it.* It fired on the letter and not on the substance — see below.

**Seven flags, not six** (the standing note counted only the unwitnessed ones).
Hand-graded one by one in `CLAIMS.md`'s new triage section: **0/7 true
positives.** That number is stated plainly and it is not a verdict on the gate.
`CLAIMS.md` has been triaged and cleaned twice already; a near-zero rate on a
clean register is the expected reading. The gate's rate has still never been
measured where it matters, on the untriaged registers.

**What the triage actually found were two mechanical defects, and the important
one runs the other way.**

1. **Filename false-witness.** The converse-witness pattern `Namespace.name`
   also matches `FAILURES.md`, `LEADS.md`, `S.md`, `Gauge.lean`. **Three of the
   four *passing* sentences passed on a filename alone.** A guard whose entire
   job is to catch unwitnessed claims had been silently exempting any sentence
   that mentioned a file. That is a false-*negative* generator, and no flag
   count could ever have shown it — flag counts only report what fires.
2. **Quoted material.** Three of seven flags triggered on text the sentence was
   quoting *in order to retract it* (`S30`'s false identity, S23's "never
   curable by formalisation") or listing as vocabulary (the gate's own
   `IDENTITY` wordlist, quoted in `CLAIMS.md`).

Both fixed. `forensics/*.py` is now admitted as a witness by name — a script
that reproduces the digits is a converse witness in this project, and
`window_opt.py` is what resolved `ISSUES` #29.

**The measurement, decomposed:**

| register | baseline | +quoted only | +filename only | both |
|---|---|---|---|---|
| `CLAIMS.md` | 3 | 1 | 5 | 2 |
| `LEADS.md` | 47 | 45 | 50 | 48 |
| `E.md` | 16 | 14 | 16 | 14 |
| `FAILURES.md` | 16 | 16 | 17 | 17 |
| **total** | **82** | **76** | **88** | **81** |

`−6` and `+6`. The headline moves by one. Reporting only the aggregate would
have read as "nothing changed" while both error modes were repaired — logged as
`S32`. No meaning is claimed for the cancellation; two independent effects came
out the same size, and after `S30` I am not calling that anything else.

Two sentences in `CLAIMS.md` were reworded anyway to drop known false-positive
triggers, and the earlier triage note's "next refinement is definitional
sentences" is corrected at its location: that was the wrong next refinement.

No Lean changed; build re-run green (3757 jobs), base hash `cd7a22e688df`
unmoved, ledger row unchanged. This is hygiene cycle 1 of the R20 cap of three.

**Might-mean, unhedged:** a guard that reports how often it fires cannot report
how often it should have fired and did not, so every instrument in this project
needs a hand-triage of its *passes*, not just of its flags — and none has had
one.


# SESSION 077 — the profile is minimal after all, once the question is asked properly

`SESSION 075` answered the queued minimality question in the negative and said
the question was degenerate: any target is its own minimal sufficient statistic.
It re-posed the question under locality and filed that as open. This cycle
answers it.

**Kill condition, filed first:** *if some non-injective per-atom coarsening still
determines the ledger on all realisable configurations, the profile is not
minimal even locally and the re-posed question dies with the original.* It did
not fire.

`profile_minimal_among_local` (new, axiom-free): let `g : ℕ × ℕ → S` be any
per-atom coarsening such that the multiset of `g`-values determines `N` and
`N_off`. Then `g` is **injective** on realisable atoms.

The proof is three lines and needs no crowded configuration at all. Two atoms
with the same `g`-value but different mass are separated by `N`; with the same
mass but different off-line mass, by `N_off`. Single-atom configurations
(`configAt_profile`, new: `profile (configAt γ k j a) = {(k+2j, 2j)}`) are the
entire witness set.

**Two things worth naming about the shape of the answer.**

*Only two of the five ledger rows are used.* `N⊛`, `Nsc` and `NscStd` play no
part — the two *additive* rows already pin the per-atom entry completely. The
three harder rows are, for minimality purposes, free riders.

*The two results are not in tension.* `profile_not_minimal` (global) and
`profile_minimal_among_local` (local) are answers to different questions, and
the difference is exactly the locality restriction: the global counterexample
works by moving off-line mass *between* two ordinates, which is precisely the
move a local statistic cannot see and cannot exploit. Stated explicitly because
"not minimal" and "minimal" on the same object one cycle apart is the kind of
pair `S30` taught me to spell out rather than leave to a reader.

Build green (3757 jobs), one new grade-A row, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the certificate class's residue has a floor — there is
no cleverer bookkeeping that records less per crowd and still adds up to the
ledger, so any future gain has to come from reading *across* crowds, which is
the one thing the counterexample shows the ledger itself already fails to do.


# SESSION 078 — both additive rows are load-bearing, and the queue is three items stale

Intended W32 (queue item 2). **It is already run**: `FAILURES.md` carries the
table, the kill condition recorded as not fired, tally **M = 2, S = 1,
neither = 8**. Items 1 and 3 were discharged in `076` and `075`/`077`. Three of
the cron prompt's five queue items are stale — logged as `S33`, and the finding
is procedural: the heartbeat text is fixed and ages while the disk moves, so
`S27`'s discipline (check the register before reconstructing) applies to the
queue itself, not only to computations.

Took instead the sharp complement to `077`. That theorem forces injectivity from
`N` and `N_off` *together*, and I had noted the three harder ledger rows are
free riders. The unasked question was whether the two survivors are both
needed.

**Kill condition, filed first:** *if either single row already forces
injectivity, the "two rows" reading is wrong and `profile_minimal_among_local`'s
hypothesis can be weakened.* It did not fire.

* `mass_only_not_sufficient` — the coarsening `(m, off) ↦ m` cannot see
  `N_off`: two atoms of mass `2`, one wholly on-line, one wholly off-line.
* `off_only_not_sufficient` — the coarsening `(m, off) ↦ off` cannot see `N`:
  two wholly on-line atoms of masses `2` and `4`.

Both axiom-free, both witnessed by single atoms. So the minimality result rests
on **exactly two** of the five ledger rows and on no fewer: `N⊛`, `Nsc` and
`NscStd` are dispensable, `N` and `N_off` are not.

The three-cycle arc is now closed. The profile is not minimal outright
(`075`), is minimal among ordinate-local statistics (`077`), and that local
minimality is driven by precisely the two additive rows (`078`).

Build green (3757 jobs), one new grade-A row, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the entire minimality of the certificate class's
bookkeeping comes from two counting facts and neither of the two subtle rows,
which means the class's residue is fixed by how much there is rather than by
anything about where it sits — and the rows that carry the actual difficulty
carry none of the rigidity.


# SESSION 079 — the class cannot compute `NscStd`, but it can compute an interval containing it

`no_muInvariant_theory_computes_NscStd` is a statement about a *point*: no
`μ_T`-invariant theory pins the invisible row. `074` then showed even atoms
contribute `0` and odd atoms at most `1`. Those two facts together suggest the
class is not blind but *low-resolution* — it should see a bracket.

**Kill condition, filed first:** *if `NscStd` can exceed the odd-atom count, the
interval reading is wrong and the section dies.* It did not fire.

Three new axiom-free results:

* `even_offAt` — off-line mass at an ordinate is even, in general and not just
  for `config`. The functional equation pairs `β` with `1 − β` and `β ≠ 1/2`
  makes the pairing fixed-point-free. This had existed only as a fact about the
  fiber states; it is now a theorem about arbitrary `ZeroData`.
* `NscStd_le_oddAtoms` — an atom contributes only when its on-line part is `1`,
  and with even off-line part its mass is then odd.
* `bracket_muInvariant` — **both endpoints are `μ_T` functionals**, `Nsc` by
  `Nsc_eq_ordinate_functional` and `oddAtoms` because `H` is the ordinate count.

Hence `NscStd_bracketed`:

> `Nsc ≤ NscStd ≤ #{odd atoms}`, both endpoints visible to the class.

**Why this is a sharpening and not a restatement.** The impossibility theorem
says a `μ_T`-invariant theory cannot output `NscStd`. It says nothing about how
badly it fails, and read alone it invites the reading that the row is entirely
dark. It is not: the class localises `NscStd` to an interval whose endpoints it
computes, and the whole content of the blindness is *which point in that
interval*. `even_offAt` is what makes the upper endpoint sharp — without the
parity of the off-line mass the bound would be the atom count, not the odd-atom
count.

**Not claimed:** that the interval is tight — i.e. that every value in it is
realised by some configuration with the given `μ_T`. That is the obvious next
question and it is not proved.

Build green (3757 jobs), one new grade-A row, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the certificate class is not blind to the standard
simple count, it is short-sighted — it reads the answer to within a window whose
width is the number of odd crowds, so every unit of the ledger's uncertainty is
attributable to one specific odd atom rather than to the configuration as a
whole.


# SESSION 080 — the bracket is tight, and the interval is a product of independent choices

`079` proved `Nsc ≤ NscStd ≤ #{odd atoms}` and explicitly declined to claim the
bracket was tight. This cycle discharges that.

**Kill condition, filed first:** *if some value in the interval is unattainable
at fixed `μ_T`, the bracket is not tight and the resolution reading overstates
what the class is missing.* It did not fire.

`bracket_tight_two_atoms` (new, axiom-free): two atoms of mass `3` at heights
`0` and `γ`. Each is independently either wholly on-line (`k = 3`, contributing
nothing to `NscStd`) or carrying an off-line pair (`k = 1`, contributing one).
`μ_T = {0,0,0,γ,γ,γ}` in all cases, `Nsc = 0`, `#{odd atoms} = 2`, and the three
configurations realise `NscStd = 0, 1, 2` — **both endpoints and the interior
point.**

`oddAtoms_from_profile` (new) is what made this cheap: `oddAtoms` is now
computable from the profile like the five ledger rows, so the whole witness is
arithmetic on explicit multisets.

**Scope, stated and not implied.** This is tightness on one family. Tightness
for an arbitrary `μ_T` is **not** proved. `LEADS.md` records exactly what the
general theorem needs — an arbitrary-arity builder and its profile lemma — and
that nothing in it is conjectural, only unbuilt.

**What the interior point is worth.** Attaining the endpoints would be routine
and nearly vacuous; attaining the *middle* is the content, because it shows the
interval is not two extreme scenarios with a gap between them but a genuine
range. The reason is structural: an odd atom of mass `≥ 3` is an independent
binary choice, mass-`1` atoms are forced to contribute, even atoms are forced
not to. The interval is a **product of independent per-atom choices**, which is
why every value is hit and why the width is exactly the count of free atoms.

Build green (3757 jobs), one new grade-A row, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the certificate class's ignorance about the standard
simple count is not diffuse but itemised — one undetermined bit per odd crowd of
mass at least three, and nothing else — so the blindness has an exact
information content rather than merely a direction.


# SESSION 081 — the builder, and tightness at every width

`080` proved the bracket tight on two atoms and filed the general case as
"nothing conjectural, only unbuilt". Built.

**Kill condition, filed first:** *if the profile of the fold needs a hypothesis
beyond distinctness of the heights, the general statement is not reachable this
way and I say so rather than adding hypotheses until it works.* **It did not
fire, and the answer was cleaner than the question** — disjointness of the
ordinate *supports* is the only hypothesis, and it is exactly what the
construction supplies for free.

Four new axiom-free pieces:

* `profile_superpose_disjoint` — **profiles add over superpositions with
  disjoint ordinate supports.** This is the reusable core and the part worth
  having beyond this cycle; every future multi-atom construction can now read
  its profile compositionally instead of by hand.
* `chain` — the builder. A configuration from an arbitrary list of fiber states,
  atom `i` placed at height equal to the length of the remaining tail. The
  heights come out `n−1, …, 0`, so distinctness is automatic rather than
  hypothesised — which is why the kill condition never had anything to catch.
* `chain_profile` — the builder's profile is exactly its list of atoms. Only
  hypothesis: every atom nonempty.
* `bracket_tight_chain` — for every `t ≤ n`, `n` atoms of mass `3` realise
  `NscStd = t` with `Nsc = 0` and `#{odd atoms} = n`, at a `μ_T` that does not
  depend on `t` (`chain_ordinates_congr`).

So the interval `[Nsc, #{odd atoms}]` is attained at **every** value and at
**every** width, not just at width 2. The scope caveat written into `080` and
into `LEADS.md` is discharged, and the discharge is recorded at the location of
the caveat rather than only here.

Build green (3757 jobs), one new grade-A row replacing the width-2 claim, base
hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the certificate class's uncertainty about the standard
simple count is exactly `#{odd atoms of mass ≥ 3}` independent bits and the
count of those atoms is itself visible to the class — so the class can compute,
from `μ_T` alone, precisely how much it does not know.


# SESSION 082 — the other invisible row, bracketed the same way

`ledger_visibility_split` names two rows the certificate class cannot read:
`NscStd` and `N_off`. Sessions `079`–`081` bracketed the first exactly. This
cycle does the second, and the symmetry holds.

**Kill condition, filed first:** *if `N_off` can exceed `N − #{odd atoms}`, the
analogous bound is wrong and the symmetry between the two invisible rows fails.*
It did not fire — an odd atom must keep at least one zero on the line, and that
one zero per odd atom is the entire gap.

Three new axiom-free results:

* `Noff_even` — `N_off` is even, being a sum of the per-ordinate off-line masses
  each of which `even_offAt` makes even. A parity constraint the class gets for
  free from the functional equation.
* `Noff_add_oddAtoms_le_N` — **`N_off + #{odd atoms} ≤ N`**. Stated in additive
  form deliberately, to avoid truncated subtraction carrying the content.
* `Noff_tight_chain` — on `n` atoms of mass `3`, `N_off = 2t` for every `t ≤ n`
  at a `t`-independent `μ_T`, with `N = 3n`. So `N_off` ranges over **all** even
  values from `0` to `2n`, and at `t = n` the inequality is an equality
  (`2n + n = 3n`).

**The two invisible rows are now bracketed by the same mechanism**, and it is
the same mechanism in a precise sense rather than a rhetorical one: both bounds
come from the per-atom decomposition `H = onAt + offAt` with `offAt` even, both
have `μ_T`-computable endpoints, and both are attained on the *same* family of
mass-`3` atoms built by `chain`. I am saying this having been wrong about a
claimed unification before (`S30`); the check that distinguishes this case is
that the shared object — `even_offAt` — appears by name in both proofs rather
than being asserted after the fact.

Build green (3757 jobs), one new grade-A row, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the certificate class knows exactly two things about
the off-line zeros it cannot count — that there is an even number of them and
that each odd crowd shelters at least one zero from them — and those two facts
are the whole of what the functional equation contributes to the ledger.


# SESSION 083 — the two invisible rows are not independent

`079`–`082` gave each invisible row an exact bracket. A reader could take that
to mean the class's ignorance is two free unknowns. It is not, and this cycle
says by how much.

An atom contributes to `NscStd` only when its on-line part is `1` — that is, only
at **maximal** off-line mass. Pushing `NscStd` up therefore drags `N_off` up
with it, and the exchange rate is the haunted count.

**Kill condition, filed first:** *if a haunted atom can exist with fewer than
two off-line zeros, the coupling is looser than `2 : 1` and the bound is wrong.*
It did not fire — on-line part `1` with mass `≠ 1` forces off-line mass `≥ 1`,
and `even_offAt` upgrades that to `≥ 2`.

* `two_mul_NscStd_le_Noff_add_two_mul_Nsc` — **`2·(NscStd − Nsc) ≤ N_off`**,
  written additively so truncated subtraction carries none of the content.
  `NscStd − Nsc` is the haunted count already named in `Basic.lean`, so the
  theorem reads: **every haunted zero costs at least two off-line zeros.**
* `coupling_tight` — and the rate is exact, on the same mass-`3` family that
  made both brackets tight: `NscStd = t`, `Nsc = 0`, `N_off = 2t`, equality at
  every `t ≤ n`. It cost four lines because `bracket_tight_chain` and
  `Noff_tight_chain` already had the values; that reuse is the return on
  `081`'s builder.

**What this changes about the blindness picture.** The class cannot read either
row, but it *can* rule out the joint hypothesis "many haunted zeros and few
off-line zeros" — the configuration a reader might have thought was the worst
case is arithmetically unavailable. The ignorance is two-dimensional but the
admissible region is a wedge, not a rectangle.

Build green (3757 jobs), one new grade-A row, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** RH-adjacent bad news comes in a fixed exchange rate —
you cannot have a zero that merely *looks* simple without paying for it with two
zeros that are visibly off the line, so the hardest case for the certificate
class is also the most expensive one for the counterexample.


# SESSION 084 — the `Nsc` row is not zero; it is 50.875%

Seven cycles of blindness theorems, none of which had touched the ledger. This
cycle asked what they bought, and the answer was the largest single movement the
project has recorded.

**Kill condition, filed first:** *if the derived route needs any hypothesis
beyond the coupling itself, it is a wish and not a route, and I say so.* It
needs none.

**The chain.**

1. `two_mul_NscStd_le_Noff_add_two_mul_Nsc` (`083`) — every haunted zero costs
   two off-line zeros.
2. Sharpened here: a haunted atom has on-line part `1` and mass `≠ 1`, so its
   off-line part is even and nonzero, so its **mass is at least 3**. It consumes
   three zeros of `N` and contributes one to `NscStd`. Hence
   **`3·NscStd ≤ N + 2·Nsc`** (`three_mul_NscStd_le_N_add_two_mul_Nsc`),
   unconditional, axiom-free.
3. `proportion_of_proportionStd` transports it: `ProportionStd κ` gives
   `Proportion ((3κ − 1)/2)` with **no star bound**.
4. `certified_nsc_unconditional` instantiates at the baseline:
   `(3 × 0.6725 − 1)/2 = 0.50875`.

**What was wrong before, and where the error lived.** `certified_nsc`'s
docstring said the row was *honestly* zero because no unconditional `(★)` exists
at any constant, so neither Proposition 1 (`2 − C`) nor the baseline route
(`0.6725 − (C−1)/2`) can be evaluated. **Both premises are true. The conclusion
does not follow.** The docstring enumerated the bridges from `NscStd` to `Nsc`
and the enumeration was not exhaustive — it assumed every bridge passes through
`(★)`. `Gaps.nscStd_le_nsc_add` and `Gaps.offline_le` are both `(★)`-conditioned,
which is presumably why. The correction is written at the location of the
docstring, and `Proportion 0` is kept as a true statement and as the record of
what was believed.

**Verification, because a result this size needs more than a green build.**

* `#print axioms` on the combinatorial step: `[propext, Classical.choice,
  Quot.sound]` — axiom-free.
* `#print axioms certified_nsc_unconditional`: `[propext, Classical.choice,
  Quot.sound, baseline_zeta23, zetaNonempty]` — **no axiom beyond the ledger's
  existing trusted base; the count is unchanged at 2.** (Stated carefully: the
  `NscStd` row's declaration `certified_std` is definitionally `baseline_zeta23`
  and so consumes one; `zetaNonempty` enters through the family's nonemptiness.
  The honest claim is about the base, not about a per-declaration match.)
* Independent brute force: 200 000 random configurations, **zero violations** of
  `3·NscStd ≤ N + 2·Nsc`.
* Tightness: `s` simple atoms and `h` haunted mass-`3` atoms give
  `NscStd/N = (s+h)/(s+3h)` and `Nsc/N = s/(s+3h)`; the constraint binds, and at
  `NscStd/N = 0.6725` it returns exactly `0.50875`. The bound is not merely
  valid, it is attained.

**Ledger: `Nsc` 0.00% → 50.88%.** Axiom count unchanged at 2, base hash
`cd7a22e688df` unmoved, sorries 0. Build green (3757 jobs).

Logged as `S34`, and it is the register's most expensive entry: the belief was
not a guess, it was a docstring I had read many times and accepted, and what
made it visible was asking what the blindness thread had bought the ledger —
the question I had gone seven cycles without asking.

**Might-mean, unhedged:** the project's own bookkeeping was the binding
constraint, not the mathematics — half the zeros were already certified simple
in the strong sense and nobody had multiplied the inequality out.


# SESSION 085 — the bridge's constants are optimal, and what that leaves open

`084` moved the `Nsc` row to `50.875%` via `3·NscStd ≤ N + 2·Nsc`. The
immediate risk is a future cycle burning itself trying to improve the constants,
so this cycle settles them.

**Kill condition, filed first:** *if some configuration permits `c > 3`, or
`c = 3` with `d < 2`, the pair is not optimal and the claim must be weakened.*
It did not fire.

`bridge_optimal` (new, axiom-free): any unconditional bridge
`c·NscStd ≤ N + d·Nsc` valid on all `ZeroData` has `c ≤ 3`, and `c = 3` forces
`d ≥ 2`. Two **single-atom** witnesses do all the work:

* a haunted atom of mass `3` — `NscStd = 1`, `Nsc = 0`, `N = 3` — forces
  `c ≤ 3`;
* a simple atom — `NscStd = Nsc = N = 1` — forces `c ≤ 1 + d`.

So `(3κ − 1)/2` cannot be improved by any inequality of that shape, and
`0.50875` is the most the baseline yields through it.

**The scope is stated and it is not vacuous.** `bridge_optimal` quantifies over
bridges in the *triple* `(NscStd, N, Nsc)`. The proof of `(3,2)` discards a real
piece of information — a non-contributing **even** atom has mass `≥ 2`, not just
`≥ 1` — and `oddAtoms` is `μ_T`-visible (`bracket_muInvariant`). A bound in the
four quantities is therefore **not** excluded by this theorem. `LEADS.md` records
it as the cheapest open item on the board, and it is pure combinatorics.

I am being explicit about the gap because `084`'s lesson was precisely a
non-exhaustive enumeration of routes stated as if it were exhaustive. The
correction is not to stop enumerating; it is to name the quantifier.

Build green (3757 jobs), one new grade-A row, ledger unchanged at
`NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash `cd7a22e688df` unmoved.

## Wildcard, same cycle: the four-quantity bridge — **kill condition fired**

`LEADS.md` had barely recorded direction 1 as the cheapest open item when it
became cheap enough to run.

**Kill condition, filed first:** *if the four-quantity bound reduces to `(3,2)`
with no gain, it does not improve the row and I say so.* **It fired.**

`two_mul_atomCount_add_oddAtoms_le`: `2·A + #{odd atoms} ≤ N + 2·Nsc`, where `A`
is the atom count (`atomCount`, the number of distinct ordinates — a `μ_T`
functional). Per atom this is `2 + [odd] ≤ mass + 2·[mass = 1]`, tight at masses
`1`, `2` **and** `3`, so it is genuinely finer than `(3,2)`: it uses that a
non-contributing even atom has mass `≥ 2`.

And it collapses. `A ≥ NscStd` and `#{odd atoms} ≥ NscStd`, so substituting
recovers `3·NscStd ≤ N + 2·Nsc` exactly — `three_mul_NscStd_le_of_four` proves
the old bound *from* the new one. The finer inequality has nothing to spend,
because the literature input supplies a proportion for `NscStd` and nothing for
`A` or `#{odd atoms}`. It becomes useful only given a lower bound on the atom
count — equivalently an upper bound on average multiplicity, which is `N⊛`
territory and therefore back to `(★)`.

That is a clean negative and it was worth the twenty minutes: the direction I had
just filed as most promising is closed, and closed by a theorem rather than by a
guess.

**Might-mean, unhedged:** every additional point of the literature's
standard-simple proportion is now worth one and a half points of the project's
own row, so the cheapest thing the project can buy is no longer a theorem about
zeta but a better reading of the theorems that already exist.


# SESSION 086 — pointing an old instrument at a new surface

`S34`'s defect was an unscoped enumeration in a **docstring**. `claims_gate` had
only ever patrolled the markdown registers, so the surface where the project's
most expensive prose error lived had never been swept.

**Kill condition, filed first:** *if the gate on `.lean` files produces only
false positives, the instrument does not transfer to code comments and I say
so.* It did not fire.

69 flags across `Riemann/*.lean`; 14 in the load-bearing files, all hand-graded
in `CLAIMS.md`. **One true positive** — and it is the one being hunted:

> `Program.lean:84` — *"This is the only arrow that survives:
> `DensityNearLine F M` ⟹ `NarrowBoxExc F δ (M δ)`."*

The next two theorems in the same file, `routeIII_with_narrowBox` and
`routeIII_via_A''`, are two more arrows. The docstring is not mathematically
wrong — the intended reading is "the only arrow with no hypothesis beyond
`DensityNearLine`", and the other two each buy their arrow with an extra
assumption. But the scope was unstated, which is exactly what made `certified_nsc`'s
docstring cost the project half a ledger row. Corrected at the location, with
the scope written out and the reason named.

**One true positive in fourteen is a low rate, and the yield is not low.** The
gate's value here was not its precision but its *reach*: it looked somewhere I
had not, and the one thing it found was in the route-table file, the document
that tells future cycles which directions are closed. That is precisely where an
unscoped absolute does the most damage — `S34` is what happens when one sits
there long enough.

`Fiber.lean`'s 36 flags are almost entirely my own prose from the last twelve
cycles and are **untriaged**; per `R17` they are not a defect rate and must not
be quoted as one. Triaging them is a real item, not a formality — the file now
carries more new prose than any other.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. Logged as `S35`.

**Might-mean, unhedged:** the project's guards were all pointed at the registers
because that is where claims are *published*, but the claims that actually steer
the work live in docstrings next to the theorems, and those had never been read
by anything but me.


# SESSION 087 — Route II priced: 9.29 points sitting behind two pieces of plumbing

`085` closed the combinatorial directions for the `Nsc` row. The remaining ones
were "a better `κ`" and "a star bound", both expensive. This cycle found a third
the register had not enumerated — which is now twice in four cycles that the
route list was short.

**Kill condition, filed first:** *if the transfer needs a hypothesis not
currently available, it does not move the row and I say so.* **It fired**, and
the value of the cycle is that it fired *with a number attached*.

**The instrument.** `proportion_of_offLineImport` (axiom-free): `ProportionStd κ`
plus `N_off ≤ (β + o(1))·N` gives `Proportion (κ − β/2)`. **Every point of
off-line control is worth half a point of the project's own row.** At the
trivial `β = 1` it reproduces `084`'s `0.50875` exactly, which is the check that
it is the right generalisation.

**The route.** `offLineImport_of_derivative`: a `Proportion κ'` for the
*derivative* family yields `β = 1 − κ'`, because that family's simple on-line
zeros crowd out its off-line ones (`Nsc_add_Noff_le_N`, new, axiom-free). zeta-23
already gives `ξ'` the value `0.85838` — a number the project has held since the
import and has been using only for Route II's `(★)` question. Through this route
it means `β = 0.14162` and

> `Nsc ≥ 0.6725 − 0.07081 = 0.60169`.

**Why the ledger did not move, and this is the honest part.** Two hypotheses are
missing, both carried as `Prop`s in `Gaps.lean` and neither asserted:

* `OffTransfer` — `levinson_montgomery` is `|N_off' − N_off| ≤ c·log T`;
  absorbing `log T` into `o(N)` is Riemann–von Mangoldt, absent from the
  registers.
* `NzComparable` — **`xiPrimeFamily` is an opaque axiom.** Nothing relates its
  zero count to `zetaFamily`'s; the consistency model in `Assumptions.lean` even
  sets the two families equal, which is precisely why no such relation can be
  assumed for free.

Adding either as an axiom would raise the certified proportion by assumption,
which `Assumptions.lean` forbids outright. So the row stays at `50.88%` and the
gain is filed in `PRICES.md` as **the cheapest nine points on the board** —
needing no new theorem about `ζ`, only the plumbing that says `ξ'` has about as
many zeros as `ζ`.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the project has been holding a 9-point improvement for
as long as it has held the `ξ'` import, and what stood between them was not
mathematics but the fact that nobody had written down that the two families
count comparably many zeros.


# SESSION 088 — the exhaustive audit, and a redundant axiom

`S34` and `087` were both "the route list was short". The response to a
recurring enumeration failure is an enumeration that **can** be exhaustive, and
the axiom list is finite. All nine audited; the table is in `PRICES.md`.

**Kill condition, filed first:** *if every axiom's ledger value is already
realised or provably nil, the audit yields nothing and I say so.* **It fired on
its own terms** — there is no unclaimed ledger value in the axiom list, and the
one live item (`zeta23_xiPrime`, 9.29 points) was already priced last cycle.

Two things worth having anyway.

**`fujii_ineffective` is nil for a reason I checked rather than inherited.** The
register said "no effective `C` exists"; I read `Cbound` instead of trusting the
note. `Cbound c₀ λ = λ + log(2+λ)/(π²λ) + c₀·√(log(2+λ))/λ` grows with `c₀` and
its minimum over `λ` is unbounded in `c₀`, so no numerical constant is
extractable. Same conclusion, now with a witness.

**`baseline_przz` is redundant, and that is a real result.**
`Family.ProportionStd.mono` (new, axiom-free): `ProportionStd` is monotone in its
constant — so two `ProportionStd` axioms about the same family are *never*
independent, the weaker is always a theorem. `przz_of_zeta23` derives PRZZ's
`0.4162` from zeta-23's `0.6725`, and `#print axioms` confirms it consumes only
`baseline_zeta23`. Nothing in the development consumes the axiom today.

This does not move a proportion. It shrinks what has to be believed, which the
project's own doctrine values independently of the number — and it is the first
time an axiom has been shown *derivable* rather than merely unused.

**A literature probe saved.** `STATEMENTS.md` records `baseline_przz` as stated
on `NscStd` per Joop's `ISSUES #13` ruling. Whether PRZZ's `41.62%` is a simple-
zero proportion or an on-line proportion is **[RECALL, UNVERIFIED]** and I am not
resolving it — the redundancy makes it moot, since nothing rests on the axiom
either way. Recorded so a future cycle does not spend a probe on a question that
cannot change a number.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`, base
hash `cd7a22e688df` unmoved. The declared axiom count is still 9 pending Joop's
ruling on deletion.

**Might-mean, unhedged:** the trusted base was never nine independent
assumptions, and nobody had checked which of them the others already imply.


# SESSION 089 — the retraction that never reached the text it retracted

Three rulings are parked with Joop, so this cycle took the item I owed rather
than one that raises a fourth: the 36 untriaged `claims_gate` flags in
`Fiber.lean`, all of them my own prose from twelve cycles.

**Kill condition, filed first:** *if the triage finds no true positives in my own
prose, the gate has nothing to say about my writing and I should stop running it
there.* It did not fire.

**2 true positives in 36**, and they are the same claim in two places:

> `onOrd_determined` — *"**The residue is exactly the fiber coordinate.** …
> Nothing beyond `(μ_T, offAt)` is needed."*
> `NscStd_eq_onAt_functional` — *"the fiber coordinate really is the whole
> residue."*

The forward direction is those theorems. The converse is **false** —
`offAt_not_minimal` refutes it, `(μ_T, offAt)` is sufficient but not minimal.
That is `SURPRISES` S26, which I filed **twelve cycles ago**, one cycle after
making the claim.

**And the retraction never reached the text.** It was written at
`offAt_not_minimal`, 150 lines below both docstrings. The R-rule says a
retraction must appear above what it retracts; I had recorded the correction in
the register and at the *new* theorem, and left the original sentences standing.
I then wrote five more theorems in that file, past those sentences, without
seeing them.

Logged as `S36`. The lesson is not "I overclaimed" — that was S26 and it is
priced. It is that **filing a retraction is not the same as landing it**, and the
gate is what found the difference, on a surface I had deferred four times as
"my own writing, low yield".

The other 34 flags are false positives of four mechanical shapes, all documented
in `CLAIMS.md`. The dominant one — sentence-splitting across a docstring/theorem
boundary — is a parser issue, not a wordlist issue; named, not built.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`, base
hash `cd7a22e688df` unmoved. No new ruling raised.

**Might-mean, unhedged:** a project that records its corrections in a register
and not in the text will read correctly to its historians and incorrectly to
itself.


# SESSION 090 — a third certified row, and the `Nsc` row confirmed by a second route

`Gaps.offline_le` extracts `N_off ≤ (C−1)·N` from a star bound, and its docstring
calls that "already a nontrivial unconditional zero-density statement". It is —
but it needs a `C`, and none is proved. **No `C` is needed.**

**Kill condition, filed first:** *if `N_off + NscStd ≤ N` fails — if some
standard-simple zero could be off the line — the bound is wrong.* It cannot:
`NscStd` requires `β = 1/2` by definition, so the two multisets are disjoint.

* `Noff_add_NscStd_le_N` (new, axiom-free) — sharper than
  `Nsc_add_Noff_le_N` since `Nsc ≤ NscStd`.
* `offLineImport_of_proportionStd` — a `ProportionStd κ` is *itself* an off-line
  import at `β = 1 − κ`.
* `certified_offline` — at the baseline: **`N_off ≤ 0.3275·N`. At most 32.75% of
  the zeros of `ζ` lie off the critical line**, with no star bound and no new
  axiom (`#print axioms`: `baseline_zeta23`, `zetaNonempty` — the same two).

This is the shape of statement Route III's narrow box and `offline_le` were
trying to buy. A weak form of it was available from the baseline the whole time,
and nobody had turned the literature's row around to face that direction.

**And it closes an `R17` loop on `084`.** Feeding `certified_offline` back
through `proportion_of_offLineImport` gives `0.6725 − 0.3275/2 = 0.50875` —
`certified_nsc_via_offline`, which lands on `certified_nsc_unconditional`'s
number by a route sharing no step past the baseline. The `Nsc` row now has two
independent derivations that agree exactly. After `S34` that is worth having;
`084` was a large claim resting on one chain, and it no longer does.

**Not added to `tools/metric.json`, deliberately.** The ledger takes the maximum
over rows as "best", and an *upper* bound on off-line zeros is not commensurate
with a *lower* bound on simple ones — adding it would report `32.75%` as though
it were a certified proportion of simple zeros. Recorded in the registers
instead. No ruling raised.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the project already owned a zero-density theorem and
had been shopping for one, because the literature's result was filed as a
statement about simple zeros and nobody read it as a statement about the zeros
it excludes.


# SESSION 091 — the same move once more: what the baseline does and does not buy

`090` read the baseline as a zero-density statement. The obvious next question is
whether it also caps `N⊛`, because that would hand the program its star bound for
free — the thing four routes have been trying to buy.

**Kill condition, filed first:** *if `ProportionStd κ` also caps `N⊛`, the star
bound is free and everything else should stop.* **It fired: the answer is no**,
and now there is a witness instead of an intuition.

`no_starBound_from_proportionStd` (axiom-free): for every `B` there is a
configuration with

> `4·NscStd = 3·N` — a standard-simple proportion of `3/4`, above the baseline —
> and `N⊛ > B·N`.

The family is `3m` simple atoms beside a single atom of mass `m`: the proportion
is `3/4` for every `m`, while `N⊛/N = (3 + m)/4` grows without bound. **No
`ProportionStd` hypothesis at any constant below `1` yields a star bound**, and
the reason is visible: one arbitrarily crowded ordinate is invisible to a
proportion of *simple* zeros. Built on `081`'s `chain`, which has now paid for
itself three times.

**What the same move does buy.** `NscStd_le_atomCount`: distinct standard-simple
zeros sit at distinct ordinates, so `ProportionStd κ` forces at least `κ·N`
**distinct ordinates** — `atomCount_ge_of_proportionStd`. At the baseline: at
least `67.25%` as many ordinates as zeros, i.e. **mean vertical multiplicity at
most `1/0.6725 ≈ 1.487`**.

So the baseline turned around gives two statements and refuses a third:
zero-density (`090`), mean multiplicity (here), and **not** `N⊛`. That refusal is
the useful part, because `N⊛` is exactly what the program keeps trying to reach
and the failure was never priced before.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the second moment is invisible to any proportion of
simple zeros, because a single sufficiently crowded ordinate can carry unbounded
`N⊛` while every other zero stays simple — so the program's central quantity
cannot be bought from the literature's central quantity at any price.


# SESSION 092 — the other wall: `(★)` is a size-biased mean, not a supremum

`091` proved a proportion of simple zeros cannot bound `N⊛`. That is one wall.
This cycle builds the other, so the program's central hypothesis is bracketed
rather than merely unreached.

**Kill condition, filed first:** *if a max-multiplicity bound gives a useful star
bound (`C < 2`), then `(★)` reduces to multiplicity control and the route table
is missing an entry.* **It fired**, and the way it fired is the finding.

`Nstar_le_of_multiplicity_le` / `starBound_of_multiplicity_le` (axiom-free): a
supremum bound `H ≤ M` gives `StarBound M`. The constant is `M` itself — and
`prop1` needs `C < 2`, which over the naturals is `M ≤ 1`: every ordinate carries
at most one zero. That is the conclusion the program is trying to reach, not a
hypothesis it can assume.

**So `(★)`'s constant is neither of the project's cheap neighbours.**
`Nstar_eq_sum_H_sq` says what it is: `N⊛/N = Σ H² / Σ H`, the **size-biased mean
multiplicity**. The two walls locate it exactly —

> unreachable from a proportion of simple zeros (`091`), and strictly weaker than
> a multiplicity supremum (here).

That is worth having written down because the route table describes `(★)` as a
second-moment estimate, which is true and does not say what kind of object the
constant is. It is an average, weighted by the thing being averaged, and both
neighbouring notions fail for opposite reasons: the proportion is blind to one
crowded ordinate, the supremum charges for it at full price.

*Candour about `multiplicity_bound_useless`: it is `omega` on `M < 2 → M ≤ 1`.
The content is the framing, not the lemma, and the lemma is there so the framing
cannot drift.*

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the program's whole difficulty is that it needs an
average that one bad ordinate can ruin and no supremum can afford, which is why
every route reaches for a second moment and every cheap substitute fails at one
end or the other.


# SESSION 093 — the wall is not about the threshold

`091` showed a proportion of *simple* zeros cannot bound `N⊛`. The obvious repair
is to ask for a proportion of zeros at ordinates of multiplicity `≤ k` for some
larger `k`, and that repair is the first thing a future cycle would try.

**Kill condition, filed first:** *if some `k` makes the low-multiplicity
proportion sufficient, then the `k = 1` negative was special and the wall is not
general.* **It fired: no `k` works.**

`no_starBound_from_lowMult` (axiom-free): for every threshold `k ≥ 1` and every
`B`, a configuration with `4·lowMult k = 3·N` — three quarters of its zeros at
*simple* ordinates, so the count is `3/4` of `N` for **every** `k` at once — and
`N⊛ > B·N`.

**One witness family kills the whole class**, because the family's good part is
as good as it gets: the `3m` atoms are simple, so they lie in `lowMult k` for
every `k ≥ 1`, and raising the threshold cannot help a statistic that is already
counting them all. Raising `k` only ever *adds* the crowded atom, which is
exactly what a proportion statement is allowed to ignore.

**The lesson generalises past the counterexample.** A proportion counts the good
part and says nothing about the arrangement of the remainder; `N⊛` is dominated
by the remainder. So no statistic of the form "at least `α` of the zeros are
nice" can reach `(★)`, whatever "nice" means, as long as `nice` is closed under
being simple. `LEADS.md` records the narrowing: a surviving statistic must
constrain how the **non-good** zeros are arranged.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the program cannot be reached by any theorem of the
form "most zeros are well-behaved", because its central quantity is decided
entirely by the zeros that are not.


# SESSION 094 — proving the generalisation `093` asserted

`093` closed the low-multiplicity thresholds and then wrote: *"no statistic of
the form 'at least `α` of the zeros are nice' can reach `(★)`, whatever 'nice'
means, as long as being simple qualifies."* That sentence was an **assertion from
a witness**, which is precisely what `S30` cost. This cycle proves it.

**Kill condition, filed first:** *if the general statement needs a hypothesis
beyond "simple atoms count as good", the generalisation is wrong and gets
downgraded at its location.* It did not fire — that one hypothesis is all it
takes.

`no_starBound_from_goodness` (axiom-free): let `good` be **any** predicate on
atoms whatsoever, subject only to `good (1, 0)` — a simple on-line atom counts as
good. Then for every `B` there is a configuration with

> at least three quarters of its zeros at good atoms, and `N⊛ > B·N`.

`good` ranges over predicates on the profile entry `(mass, off-line mass)`, which
`profile_minimal_among_local` established is the finest local data there is. So
the theorem is not about a convenient family of statistics; it is about all of
them.

**And the subsumption is a theorem, not prose.** `lowMult_eq_goodCount` proves
`lowMult D k = goodCount D (·.1 ≤ k)`, so `093`'s result is a genuine instance
rather than an analogue, and `091`'s is the instance `good q ↔ q.1 - q.2 = 1`.
Writing that lemma was the point of the cycle: "subsumes" is exactly the kind of
word the gate exists to catch.

**What the proof shows about *why*.** The hypothesis used is only that the good
class contains the simple atom. Nothing else about `good` matters, because the
witness makes its good part maximally good and hides everything else in a single
atom. A proportion bounds the good part from below and leaves the remainder
unconstrained; `N⊛` is decided by the remainder. The mechanism is now visible in
the statement rather than in a comment.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

> ⚠️ **The might-mean below outran the theorem, and `095` closed the gap rather
> than downgrading it.** `no_starBound_from_goodness` fixes the good proportion
> at `3/4`, which does not exclude a hypothesis at `99%`.
> `no_starBound_from_goodness_at_any_level` now covers every level below `1`, so
> the sentence stands as written — but it did not, when written.

**Might-mean, unhedged:** every "positive proportion" theorem in this subject is
structurally incapable of reaching the second moment, and the barrier is not the
strength of the proportion but the shape of the sentence.


# SESSION 095 — the might-mean outran the theorem by a factor of four

`094` proved that no goodness proportion bounds `N⊛`, with the good proportion
fixed at `3/4`. Its might-mean said *"every 'positive proportion' theorem in this
subject is structurally incapable of reaching the second moment"*. **A `3/4`
witness does not exclude a hypothesis at `99%`** — the sentence was one
quantifier wider than the theorem under it.

I noticed on re-reading rather than through the gate, which does not flag
quantifier drift.

**Kill condition, filed first:** *if the witness cannot be pushed past some
`α < 1`, proportions above that level are not excluded and `094`'s might-mean
must be downgraded at its location.* **It did not fire**, so the gap closed
upward instead of downward.

`no_starBound_from_goodness_at_any_level` (axiom-free): for any rational level
`p/q < 1`, any goodness predicate accepting the simple atom, and any `B`, there
is a configuration with at least `p/q` of its zeros at good atoms and
`N⊛ > B·N`. The family is `c·m` simple atoms beside one atom of mass `m`, with
`c` chosen from the level and `m` from `B` — the good proportion `c/(c+1)` goes
as close to `1` as required while `N⊛/N = (c+m)/(c+1)` still runs away.

**The level `1` case is genuinely excluded**, and that is the whole content of
the boundary: proportion `1` means every zero is at a good atom, and with `good`
the simple-atom predicate that is RH-simplicity. So the theorem is sharp — it
covers everything strictly below the conclusion the program is trying to prove.

An annotation is written above `094`'s might-mean recording that it outran its
theorem, because the sentence now stands but did not when it was written, and a
reader should not have to reconstruct which.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the barrier is not a threshold anywhere below certainty
— any theorem short of "all zeros are good" leaves room for a single ordinate to
carry the entire second moment, so the subject's whole vocabulary of positive
proportions stops exactly one step short of the quantity it needs.


# SESSION 096 — the supremum is not useless once the row is paid for

`092` priced a multiplicity supremum as worthless for `prop1`: it gives
`StarBound M`, and `C < 2` forces `M ≤ 1`, which is simplicity. That pricing is
correct for the **bare** supremum and wrong for the combination with the `Nsc`
row the ledger has carried since `084`.

**Kill condition, filed first:** *if the joint criterion cannot give `C < 2` at
any `M ≥ 2`, multiplicity control never substitutes for simplicity and `092`'s
wall is total.* **It did not fire — `M = 2` suffices.**

`Nstar_add_mul_Nsc_le` (new, axiom-free): `N⊛ + M·Nsc ≤ (1 + M)·N` for any
multiplicity supremum `M`. Per atom it is `H² + M·[H = 1] ≤ H + M·H`, equality at
`H = 1`. The content is that **a simple atom is charged `1`, not `M`** — which is
exactly what a certified `Nsc` row pays for. Dividing by `N`:

> `C ≤ 1 + M·(1 − κ)`

and at `M = 2`, `κ = 0.50875` that is `1.9825 < 2`
(`starBound_of_multiplicity_two`).

> **If no zero of `ζ` has multiplicity three or more, `(★)` holds.**

That is the first sufficient condition for `(★)` in the registers which does not
assume the conclusion — strictly weaker than simplicity, carried as a hypothesis
and never as an axiom.

**Candour about its worth.** Through `prop1` it gives `Proportion 0.0175`, far
below the `0.50875` already certified. It buys **nothing** on the headline row.
Its value is that `(★)` feeds `offline_le` and the narrow box, which the `Nsc`
row does not reach, and that Routes I and III exist entirely to produce it.

`092`'s docstring is corrected at its location: "useless" now reads "the *bare*
bound is useless", with a pointer here.

**And it connects two purchases the route table kept apart.** Every point of the
`Nsc` row buys `M` points of star constant, so improving the row and bounding
multiplicities are the same transaction from opposite ends.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the program's central hypothesis is now reachable from
a statement about multiplicities that is weaker than anything it was trying to
prove, and the reason nobody saw it is that the two ingredients were priced in
different cycles and never multiplied together.


# SESSION 097 — at `M = 2` there is nothing to estimate

`096` derived `C ≤ 1.9825` from "no zero has multiplicity `≥ 3`" by charging a
crowded atom `M·H`. At `M = 2` that is an estimate where an identity is
available.

**Kill condition, filed first:** *if the sharpened `M = 2` analysis does not beat
`096`'s constant, the loose bound was already tight and there is nothing here.*
**It did not fire, and the margin is large.**

Two exact facts, both axiom-free:

* `Nstar_add_Nsc_eq_two_mul_N` — under `H ≤ 2`, `N⊛ + Nsc = 2·N`. Per atom,
  `H² + [H = 1] = 2H` for `H ∈ {1, 2}`: an **identity**, not a bound. So
  `C = 2 − Nsc/N` exactly.
* `Nsc_eq_NscStd_of_mult_le_two` — under `H ≤ 2`, **`Nsc = NscStd`**. A
  standard-simple atom has `onAt = 1` and even off-line part; `H ≤ 2` forces
  `off = 0`. The two notions the project keeps carefully apart *coincide* under
  this hypothesis — and the literature certifies the standard one.

Together: `C ≤ 2 − 0.6725 = 1.3275`, and `prop1` returns `Proportion 0.6725`.

| from multiplicity `≤ 2` | `096` | `097` |
|---|---|---|
| star constant | `1.9825` | **`1.3275`** |
| `Nsc` row | `0.0175` | **`0.6725`** |

**`1.3275 < 4/3`.** Route III's narrow-box threshold is `4/3 = 1.333…`, so the
hypothesis clears it — the first time anything in the registers has. And the row
it returns is the *entire* literature baseline, transferred onto the project's
stronger notion at no loss, because under this hypothesis there is no loss to
suffer: the notions are equal.

`096`'s "far worse than the `0.50875` already certified" is corrected at its
location. It was true of the loose constant and is false of the sharp one.

**What is not claimed.** Multiplicity `≤ 2` is a hypothesis, carried as one and
never asserted; nothing here says it is true or reachable. The ledger is
unchanged.

Build green (3757 jobs), ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash
`cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the entire distance between what the literature proves
and what this project wants is created by zeros of multiplicity three or more, so
a single hypothesis that nobody has ever needed to state would collapse the gap
completely.


# SESSION 098 — the sharp criterion, and what `084` was really worth

`097` sharpened the `M = 2` case by finding an identity where `096` had an
estimate. The same slack is present at every `M`, and removing it weakens the
hypothesis rather than improving the constant.

**Kill condition, filed first:** *if the sharp general bound does not extend the
sufficient hypothesis past `M = 2`, then `097` already captured everything.*
**It did not fire — the hypothesis weakens to `M ≤ 3`.**

`Nstar_add_pred_mul_Nsc_le` (new, axiom-free): `N⊛ + (M−1)·Nsc ≤ M·N`. The
per-atom estimate is `H² + (M−1)·[H = 1] ≤ M·H`, with **equality at `H = 1` and
at `H = M`** — so it cannot be improved within this shape. `096`'s version is
this one weakened by exactly `N − Nsc`: it charged the simple atom correctly and
then kept a spare `H` it did not need.

Dividing by `N`: `C ≤ M − (M−1)·κ`, so `C < 2` **iff** `κ > 1 − 1/(M−1)`.

| hypothesis | threshold on `κ` | certified `κ` clears it? | constant |
|---|---|---|---|
| `M ≤ 2` | `κ > 0` | yes, hugely | `C ≤ 1.3275`, row `0.6725` |
| `M ≤ 3` | `κ > 0.5` | **yes, by `0.00875`** | `C ≤ 1.9825` |
| `M ≤ 4` | `κ > 0.6667` | no | — |

**The `M = 3` line is the finding, and it is entirely owed to `084`.** The margin
is `0.00875`. With the `Nsc` row at its pre-`084` value of `0`, the threshold
fails at every `M ≥ 2` — the criterion would be empty. `084` moved the row from
`0` to `0.50875`, and the first thing that buys, four cycles later, is a
sufficient condition for `(★)` at a strictly weaker hypothesis than `097`'s.

The two criteria are complementary rather than ranked: `M ≤ 2` returns far more
(`C ≤ 1.3275`, the full `0.6725` row) and asks more; `M ≤ 3` returns little
(`C ≤ 1.9825`, row `0.0175`) and asks less.

`096`'s inequality is marked superseded at its location.

**Not claimed:** nothing here says any multiplicity hypothesis holds or is
reachable. All are carried as hypotheses. Ledger unchanged.

Build green (3757 jobs), `NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash
`cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** a ledger row is not a score but a currency, and the
half-point `084` added has just been spent on a hypothesis nobody could have
afforded before it.


# SESSION 099 — the criterion tolerates exceptions, and the tolerance is `√N`

`097`/`098` need a supremum on **every** ordinate, which is the kind of
hypothesis analytic number theory never delivers — its theorems come with
exceptional sets. So: how large an exceptional set does the criterion survive?

**Kill condition, filed first:** *if the exceptional set can be as large as
`o(N)` rather than `o(√N)`, the square-root threshold is not the real boundary
and I have mislocated it.* It did not fire.

`Nstar_add_pred_mul_Nsc_le_except` (new, axiom-free): for any decidable set of
exceptional ordinates, with `H ≤ M` outside it and `E` zeros sitting on it,

> `N⊛ + (M−1)·Nsc ≤ M·N + E²`.

The exceptional term is `E²` and not `E·M` because the worst arrangement puts
all `E` zeros at a single ordinate, where `Σ H² = E²`. The proof splits the
per-atom estimate along the exceptional predicate: outside, the sharp
`H² + (M−1)[H=1] ≤ M·H` of `098`; inside, `H² ≤ H·E` summed to `E²`.

**So the sufficient condition is not a supremum at all.** It is

> `H ≤ M` outside a set carrying `o(√N)` zeros.

**And `√N` is sharp, not an artifact.** The `E²` is attained — one atom of mass
`E` contributes exactly `E²` by `Nstar_from_profile` — so an exceptional set of
size `c√N` shifts `C` by `c²`, which is not `o(1)`.

**Why it matters.** Every criterion in the registers so far has demanded control
of *all* zeros. This is the first with a genuine exceptional-set allowance, which
is the shape analytic results actually have. The allowance being `√N` rather than
`εN` is the honest news: it is real, and it is small.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the program can afford to be ignorant about `√N` of the
zeros and no more, which is a far more demanding standard than the exceptional
sets zero-density theorems come with, and locates precisely why those theorems do
not compose with it.


# SESSION 100 — consolidating a thread that had started superseding itself

Four cycles produced four multiplicity criteria, each correcting the last:
`096` → `097` → `098` → `099`. Every correction was written at the location of
the text it corrected, per the rule. But a reader — including a future compacted
me — now has to walk four annotations to learn which statement is current, and
that is `S36`'s defect at the scale of a thread rather than a sentence.

**Kill condition, filed first:** *if the exceptional-set inequality does not
specialise to the no-exception one, the family is not a hierarchy and they stay
separate results.* It did not fire.

`Nstar_add_pred_mul_Nsc_le_of_except` (new): the `E = 0` case of
`Nstar_add_pred_mul_Nsc_le_except` **is** `098`'s theorem. So the family is one
theorem with specialisations, and that is now checked by the kernel rather than
asserted in a comment — which is the point, since the whole failure mode being
guarded against is prose that drifts from the theorems.

`LEADS.md` gains a consolidated section: the one theorem, the one extra
ingredient (`Nsc = NscStd` under `M ≤ 2`, which is why that case is so much
stronger), the table of what each hypothesis yields, and an explicit list of what
is superseded and where its annotation lives.

**The consolidation surfaced one thing worth naming.** `097`'s advantage over
`098` at `M = 2` is *not* the sharper inequality — both give `C ≤ 2 − κ`. It is
entirely `Nsc = NscStd`, which lets the standard baseline `0.6725` be used in
place of `0.50875`. I had been carrying the two improvements as one story; they
are independent, and only one of them survives to `M = 3`.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** a result that supersedes itself four times is one
result discovered slowly, and the cost of not saying so is paid by whoever reads
the registers next.


# SESSION 101 — the criterion is one-way, and the gate check I owed

`100` consolidated the multiplicity criteria into one theorem with
specialisations. The question that consolidation raises, and that a future cycle
would waste itself on, is whether the implication reverses.

**Kill condition, filed first:** *if `(★)` with `C < 2` forces bounded
multiplicity, the criterion is an equivalence and the route table should say so.*
**It fired — `(★)` tolerates any fixed multiplicity.**

`starBound_allows_any_multiplicity` (axiom-free): for every `m`, the
configuration of `m²` simple atoms beside one atom of mass `m` has
`N = m² + m`, `N⊛ = 2m²`, hence `N⊛ < 2·N`, and contains an atom of mass `m`.
So `(★)` holds strictly below `prop1`'s threshold while a multiplicity-`m` zero
sits inside it.

> `multiplicity ≤ M` (+ a certified row) `⟹ (★)`, and **not** conversely.

Recorded in `LEADS.md` beside the consolidated statement, so nobody spends a
cycle trying to close a loop that does not close.

**And the check I owed.** `100` ended with the gate reporting unwitnessed
sentences on `CLAIMS.md` and I did not look. Looked now: **four flags, none of
them from the rows added in `084`–`100`.** Two are the known false positives
triaged in `076`; two are my own prose in the `086` triage write-up
(*"a surface the instrument had never seen"*, *"the one being hunted"*), both
accurate and both verifiable. So every claim row from the last seventeen cycles
carries its witness — which is the first time that has been checked rather than
assumed.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the second moment can be small while a single zero is
enormously multiple, so `(★)` and multiplicity control are genuinely different
hypotheses and the program has been treating one as a proxy for the other.


# SESSION 102 — why the criterion must use the weaker row, and a repo that defends itself

**Piece.** The criterion `C ≤ M − (M−1)·κ` takes `Nsc ≥ 0.50875` as input while
`NscStd ≥ 0.6725` sits right beside it — larger, better certified, and enough to
reach `M = 4` if it could be used. So: can it?

**Kill condition, filed first:** *if a positive coefficient on `[onAt = 1]` is
admissible at `M ≥ 3`, the criterion should use the stronger row and I have been
feeding it the weaker one.* **It fired — no positive coefficient exists.**

`no_NscStd_coefficient_at_three` (axiom-free): the **haunted atom of mass 3**
kills it. That configuration has `N = 3`, `N⊛ = 9 = 3·N`, and `NscStd = 1`, so
`N⊛ + b·NscStd ≤ 3·N` forces `b ≤ 0`. The per-atom estimate is already tight
there, with nothing left to spend.

This is the same object that has been doing the work all along — the haunted
atom is what separates `NscStd` from `Nsc` (`084`), what forces the `(3,2)`
constants (`085`), and now what stops the stronger row entering the criterion.
`M ≤ 2` remains the only regime where `NscStd` may be used, and `097` explains
why: there the haunted atom does not exist.

**Wildcard: the repo now defends itself against its own prompt.** Three rulings
have been parked with Joop for many cycles, and one of them — the stale STATE
line — is not inert. It once told me the `Nsc` row was "honestly zero", and that
belief survived many cycles until `084`. A compacted instance reading the prompt
rather than the disk would re-block an open row.

I cannot edit the cron job. I can put the correction where a compacted instance
reads first: `LOOP.md` now opens with a **READ FIRST** block listing every way
the heartbeat prompt is currently wrong, each with its witness, and the standing
instruction that the disk is authoritative.

That is `S33` turned from an observation into a defence. It does not discharge
the ruling — Joop should still fix the cron text — but it removes the failure
mode's teeth in the meantime.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved.

> ✅ **Checked the next cycle rather than left as rhetoric.**
> `Fiber.haunted_atom_saturates` proves this configuration attains equality in
> **seven** certified inequalities simultaneously. The sentence below stands as a
> theorem, not a flourish — which after `S37` is the standard it had to meet.

**Might-mean, unhedged:** one configuration — a simple zero on the line with an
off-line pair hiding at the same height — is simultaneously the reason the two
simplicity notions differ, the reason the transfer costs what it costs, and the
reason the better number cannot be used, so the entire arithmetic of this project
is the arithmetic of that one picture.


# SESSION 103 — the flourish, made a theorem

`102` ended with a sentence claiming the project's arithmetic *is* the arithmetic
of one picture. That is exactly the kind of sentence `S37` was logged about: it
sounded true, no instrument checks it, and nothing under it said so. It is
checkable, so this cycle checks it.

**Kill condition, filed first:** *if the haunted mass-`3` atom fails to attain
equality in any one of the project's inequalities, the "one picture" reading is
wrong and the might-mean gets downgraded at its location.* **It did not fire.**

`haunted_atom_saturates` (axiom-free): `configAt 0 1 1 a` — three zeros, one on
the line and an off-line pair at the same height — has `N = 3`, `N⊛ = 9`,
`Nsc = 0`, `NscStd = 1`, `N_off = 2`, one odd atom, one atom. And it attains
**equality** in all seven of:

| inequality | value |
|---|---|
| `3·NscStd ≤ N + 2·Nsc` (`084`, the `Nsc` row) | `3 = 3` |
| `2·NscStd ≤ N_off + 2·Nsc` (`083`, the coupling) | `2 = 2` |
| `N⊛ + (M−1)·Nsc ≤ M·N` at `M = 3` (`098`) | `9 = 9` |
| `N_off + NscStd ≤ N` (`090`, the density row) | `3 = 3` |
| `N_off + #odd ≤ N` (`082`) | `3 = 3` |
| `NscStd ≤ #odd` (`079`) | `1 = 1` |
| `2·A + #odd ≤ N + 2·Nsc` (`085`) | `3 = 3` |

Seven bounds, proved across twenty cycles for different purposes, all tight at
the same three-element configuration.

**What this is and is not.** It is not a proof that the haunted atom is the
*unique* extremal configuration, and I am not claiming that — several of these
are also tight on the simple atom.

> ⚠️ **Sharpened next cycle, and the hedge was too weak.** *All seven* are tight
> on the simple atom, not merely several. `104`'s `three_mul_NscStd_eq_iff`
> characterises the extremal family of the central bound exactly: mixtures of
> simple and haunted-mass-`3` atoms, and nothing else. It is the precise content the `102` sentence
was reaching for: the constants in this project's arithmetic are all decided by
one picture, and now that is a theorem rather than an impression.

The `102` might-mean is annotated at its location to say so.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** twenty cycles of separate inequalities turned out to be
twenty readings of one configuration's arithmetic, which means the project's
progress has been less a search over methods than a slow inventory of what a
single counterexample forbids.


# SESSION 104 — the extremal family, characterised exactly

`103` proved the haunted mass-`3` atom saturates seven bounds and hedged that it
might not be unique. Checking that hedge first was the right move: **the simple
atom saturates all seven too** — not "several", as `103` said, but all of them.
So the extremal set is a family, and the question worth answering is which one.

**Kill condition, filed first:** *if some atom shape outside "simple, or haunted
of mass `3`" also gives per-atom equality, the characterisation is wrong.* It did
not fire — `H = 2` gives `0 < 2`, `H = 3` with `onAt = 3` gives `0 < 3`, and a
haunted atom of mass `5` gives `3 < 5`.

`three_mul_NscStd_eq_iff` (new, axiom-free): for the project's central bound,

> `3·NscStd = N + 2·Nsc` **iff** every ordinate carries either one zero, or
> three with exactly one on the line.

An **iff**, not a family of witnesses. The proof runs the `084` estimate through
`Finset.sum_eq_sum_iff_of_le`, so equality of the sums forces equality at every
single ordinate, and then the per-atom arithmetic leaves exactly two shapes.

**And the family was already in the registers, unrecognised.** `084`'s tightness
argument used `s` simple atoms and `h` haunted ones because that mixture returned
the right number. It turns out that mixture is not *a* tight family but **the**
tight family — the bound's entire equality set, found by accident twenty cycles
before it was characterised.

`103`'s hedge is corrected at its location: "several of these" understated it.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the `Nsc` row is exactly `0.50875` and not a hair more
because of configurations made only of lone critical zeros and lone critical
zeros shadowed by a single off-line pair, so improving the row means excluding
that shadow and nothing else.


# SESSION 105 — the ladder out of the shadow

`104`'s might-mean said improving the `Nsc` row means excluding one shadow and
nothing else. That is quantifiable, so this cycle quantifies it.

**Kill condition, filed first:** *if excluding low-mass haunted atoms does not
improve the constant, the shadow is not where the loss lives and `104`'s
might-mean is wrong.* **It did not fire.**

`mul_NscStd_le_N_add_pred_mul_Nsc` (new, axiom-free): if every haunted ordinate
carries at least `m` zeros, then `m·NscStd ≤ N + (m−1)·Nsc`. At `m = 3` the
hypothesis is vacuous and this is `084`. Transported
(`proportion_of_noSmallHaunted`), it gives `Proportion ((m·κ − 1)/(m − 1))`,
which **increases in `m` to `κ` itself**.

| `m` | hypothesis | `Nsc` row |
|---|---|---|
| `3` | vacuous | `0.50875` |
| `5` | no haunted ordinate of mass exactly `3` | **`0.590625`** |
| `7` | none of mass `3` or `5` | `0.617917` |
| `→ ∞` | no haunted ordinate at all | `0.6725` |

**The `m = 5` rung is worth 8.2 points, and its hypothesis is oddly small.** It
does not say there are no off-line zeros. It permits off-line pairs anywhere
except shadowing a lone critical zero at mass exactly `3` — one configuration,
the one `103` showed saturates seven bounds and `104` showed is half the equality
set. Excluding it alone buys most of the distance to the literature's row.

That is a different *kind* of hypothesis from anything else in the registers:
not a density statement, not a moment bound, but the exclusion of a single local
pattern. Whether it is reachable I do not know and do not claim.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the gap between what the literature proves and what
this project certifies is held open by one picture repeated, so the cheapest
possible purchase is not a stronger theorem about zeros in general but a reason
that one arrangement of three zeros cannot occur.


# SESSION 106 — the ladder is sharp, and half its rungs were slack

`105` built a ladder of conditional rows indexed by `m`. Two questions a future
cycle would ask before using it: is the constant `m` best, and is every `m` a
real rung?

**Kill condition, filed first:** *if a constant larger than `m` is admissible
under `NoSmallHaunted m`, the ladder is not sharp and its rungs understate what
the hypothesis buys.* **It fired — at even `m`.**

* `haunted_odd` (new, axiom-free): a standard-simple ordinate carries an **odd**
  number of zeros. `H = onAt + offAt` with `onAt = 1` and `offAt` even.
* `noSmallHaunted_succ_of_even` — therefore at even `m`, "haunted mass `≥ m`" is
  *the same hypothesis* as "haunted mass `≥ m + 1`". The even rungs of `105`'s
  ladder report a worse number for the same assumption: `m = 4` would give
  `0.5633` where the hypothesis actually delivers `0.590625`.
* `ladder_sharp_at_odd` — and at odd `m ≥ 3` nothing better exists. The haunted
  atom of mass `m` is admitted by the hypothesis and has `NscStd = 1`, `Nsc = 0`,
  `N = m`, so any valid `c·NscStd ≤ N + b·Nsc` has `c ≤ m`.

**So the ladder is odd-indexed, and that is not a convention but a fact about the
functional equation.** Off-line zeros come in conjugate pairs, so a lone critical
zero shadowed by them always sits at odd mass; there is no such thing as a
haunted ordinate of even mass, and a hypothesis that pretends to exclude one is
excluding nothing.

Annotated at the ladder's location in `PRICES.md`. Sharpness at `j = 0` is
excluded and stated: mass `1` is a *simple* atom, not a haunted one, and there
the bound is `c ≤ 1 + b` rather than `c ≤ 1`.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the parity that makes the functional equation pair
off-line zeros is the same parity that makes half of this ladder illusory, so
even the shape of the project's conditional results is dictated by the one
symmetry it started from.


# SESSION 107 — where the two conditional families meet

The registers carry two ladders of hypotheses built eleven cycles apart and never
related: multiplicity (`H ≤ M`, `096`–`100`) and hauntedness
(`NoSmallHaunted m`, `105`–`106`). They meet at the top, and the meeting corrects
something.

**Kill condition, filed first:** *if "no haunted ordinates at all" fails to
deliver the full `κ` row, the ladder's limit is not attained and the two families
do not meet.* It did not fire.

* `Nsc_eq_NscStd_of_noHaunted` (new, axiom-free) — no haunted ordinate makes the
  two simplicity notions coincide, so `proportion_of_noHaunted` transfers the
  literature's row **whole**: `Proportion 0.6725`. The ladder's `m → ∞` limit is
  attained, not approached.
* `noHaunted_of_mult_le_two` — `H ≤ 2` implies it, since a haunted ordinate
  carries odd mass `≥ 3` (`106`).
* `noHaunted_not_mult_le_two` — and the converse fails: `configAt 0 4 0 a`, four
  zeros all on the line at one height, is unhaunted with `H = 4`.

**So `097` assumed more than it needed for the row.** `H ≤ 2` forbids *all*
crowding; `NoHaunted` forbids only the shadow, and permits an ordinate to carry a
hundred critical zeros. Both give `0.6725`. What the stronger hypothesis actually
buys is the star bound `C ≤ 1.3275` — which hauntedness alone does not, since an
unhaunted crowd still inflates `N⊛`.

That distinction was invisible while the two families sat in different sections
of the same file. It is the kind of thing consolidation is for, and `100`'s
consolidation did not catch it because it consolidated *within* one family.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project's strongest conditional result needs
nothing about how crowded the zeros are, only that no crowd hides a lone survivor
on the line — so the obstruction was never multiplicity but camouflage.


# SESSION 108 — the hypothesis was `ISSUES #13` all along

`107` gave the project's strongest conditional row from `NoHaunted`, and ended by
calling the obstruction camouflage rather than multiplicity. The obvious next
question is what `NoHaunted` actually *is* — whether it is an ad-hoc condition
invented to make a theorem work.

**Kill condition, filed first:** *if `Nsc = NscStd` can hold with a haunted
ordinate present, the equivalence fails and `NoHaunted` is strictly stronger than
agreement of the two notions.* It did not fire.

`Nsc_eq_NscStd_iff_noHaunted` (new, axiom-free):

> `Nsc = NscStd` **iff** no ordinate is haunted.

`Nsc ≤ NscStd` holds pointwise — a mass-one ordinate has no off-line zeros to
carry — so equality of the totals forces equality at every ordinate, and a
haunted one would break it.

**So the hypothesis is `ISSUES #13`.** That issue was opened in session 003, on
reading zeta-23's `N0simple` and noticing it counts something weaker than the
project's `Nsc`; Joop ruled on it; the two notions have been carried carefully
apart for a hundred sessions. `NoHaunted` is that distinction collapsing, written
as an equation — not a condition invented for `107`'s theorem but the oldest
open question in the registers, given a name.

**Candour, since it matters here.** With this characterisation,
`proportion_of_noHaunted` is a substitution: assume the two counts are equal and
the literature's row is the project's row. The content of this cycle is the
*characterisation*, not the transfer, and it would be dishonest to present the
transfer as the result.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project's entire conditional apparatus — the
ladder, the multiplicity criteria, the exceptional sets — is a family of partial
answers to one question asked in its third session, and the `0.50875` row is what
that question costs when it goes unanswered.


# SESSION 109 — the whole arc is one identity and one inequality

`108` found the apparatus answers one question. It also *reduces* to one fact,
and this cycle states it.

**Kill condition, filed first:** *if `NscStd = Nsc + hauntedCount` fails — if
some ordinate is counted by `NscStd` without being simple or haunted — the
identity is wrong and the reduction does not exist.* It did not fire.

* `NscStd_eq_Nsc_add_haunted` (new, axiom-free) — **an identity, not a bound.**
  Every standard-simple ordinate is simple or haunted, disjointly, so the gap
  between the literature's count and the project's is *exactly* the number of
  haunted ordinates.
* `Nsc_add_three_mul_haunted_le_N` (new) — the mass accounting: a simple ordinate
  carries one zero, a haunted one at least three.
* `three_mul_NscStd_le_of_identity` — and `084` falls out by eliminating
  `hauntedCount` between them. **Derived, not aliased**: I wrote the alias first,
  noticed its docstring claimed a corollary while its proof cited the original,
  and replaced it with the actual derivation.

`LEADS.md` gains the reduction table: `084`, `NoHaunted`, `108`'s equivalence and
the ladder are all consequences of these two lines.

**The line worth keeping.** The row is not the baseline minus an estimate — it is

> `Nsc/N = NscStd/N − hauntedCount/N`, **exactly**,

so any bound `hauntedCount ≤ δ·N` gives `Proportion (κ − δ)` at once, and
twenty-five cycles of conditional results have all been searches for such a `δ`.
The certified `0.50875` is `0.6725 − 0.16375`, and `0.16375` is precisely the
haunted density that the trivial mass accounting cannot exclude.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project's central number is a subtraction, and the
thing being subtracted has a name, a definition, and no known bound — so the work
is not to prove a proportion but to count one pattern.


# SESSION 110 — three routes, one inequality, and the end of the counting

`109` reduced the row to `Nsc/N = NscStd/N − hauntedCount/N`. So everything now
depends on bounding one quantity. This cycle states that bound in its own right
rather than as a by-product of `084`.

**Kill condition, filed first:** *if some configuration has
`2·hauntedCount + NscStd > N`, the bound is wrong and the haunted count is not
controlled this way.* It did not fire.

`two_mul_haunted_add_NscStd_le_N` (new, axiom-free): each haunted ordinate
carries at least two off-line zeros, each standard-simple ordinate one on-line
zero, and the collections are disjoint. So

> `hauntedCount ≤ (N − NscStd)/2`,

and the certified row reads off in one line: `0.6725 − (1 − 0.6725)/2 = 0.50875`.

**The finding is that this is the only bound there is.** The registers reached
the haunted count three separate ways — `083`'s coupling through `N_off`,
`109`'s mass accounting, `090`'s off-line density row — and all three collapse
to exactly this inequality. Within the counting functions
`(N, NscStd, Nsc, N_off)` there is nothing further to extract. Recorded in
`LEADS.md` so a future cycle does not spend itself looking for a fourth route.

`two_mul_haunted_add_NscStd_eq_iff` confirms coherence: the bound is attained on
precisely `104`'s extremal family, the same equality set as `084`.

**What that implies for the programme.** Any improvement to the row needs a
`δ < 0.16375` bound on the haunted density, and no such bound can come from a
relation among ζ's own counting functions — the counting is finished. It must
come from outside: `087`'s ξ′ transfer, or `105`'s exclusion of one local
pattern. Both are hypotheses, and now it is clear why they have to be.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

> ✅ **Given a provable form the next cycle.** "Nothing further to extract" was
> asserted from three coincidences. `111`'s `row_essentially_optimal` proves the
> precise version: a witness configuration caps any baseline-only argument at
> `0.50943`, and the ledger certifies `0.50875`.

**Might-mean, unhedged:** twenty-six cycles of combinatorics have extracted
everything the zero counts contain about each other, and the remaining gap is
not a gap in the accounting but the exact size of what arithmetic has not yet
been asked to say.


# SESSION 111 — how close the row is to optimal, with a witness

`110` said the counting is finished. That was asserted from three routes
coinciding — the shape `S30` and `S37` were logged about. It has a provable
form, and this cycle proves it.

**Kill condition, filed first:** *if no configuration achieves haunted density
near `0.16375` at `NscStd/N ≥ 0.6725`, then `0.16375` is only our bound and
`110`'s "nothing further to extract" must be downgraded at its location.* It did
not fire.

`row_essentially_optimal` (new, axiom-free): `1000` simple atoms beside `321`
haunted mass-`3` atoms give

> `NscStd/N = 1321/1963 ≈ 0.67295 ≥ 0.6725`,  `Nsc/N = 1000/1963 ≈ 0.50942`.

**So no argument using only `ProportionStd 0.6725` can certify an `Nsc` row above
`0.50943`.** The ledger certifies `0.50875`.

> ⚠️ **Quantifier gap, closed the next cycle.** That sentence is a `Family`-level
> claim — `Proportion` is a predicate on families — supported here by a single
> `ZeroData`. `112`'s `baseline_cap_witness` closes it: the witness placed in a
> constant family satisfies `ProportionStd 0.6725` and fails
> `Proportion 0.50944`. The claim stands; it did not, as stated, follow from
> what was proved beneath it. The remaining `0.00068` is the
discretisation of the ratio `s : h`, not slack in the method.

That converts `110`'s rhetorical claim into a measurement: the baseline is spent,
to within seven parts in ten thousand. Any further gain must come from outside
the counting functions — `087`'s ξ′ transfer or `105`'s pattern exclusion — and
that is now a fact about the problem rather than a summary of what we tried.

`110`'s might-mean is annotated at its location.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project has extracted `99.87%` of what its one
external input can give, so every remaining cycle spent on the counting is a
cycle spent on seven parts in ten thousand.


# SESSION 112 — my own lesson, applied to my own sentence

`111` proved a `ZeroData` witness and concluded that **no argument from
`ProportionStd 0.6725` certifies an `Nsc` row above `0.50943`**. That conclusion
is about `Proportion`, which is a predicate on *families*, not on single
configurations. The witness did not, as stated, support it.

This is `S37` exactly — a sentence one quantifier wider than the theorem under
it — committed two cycles after logging `S37`, and in the cycle whose entire
subject was converting an asserted claim into a proved one. I found it by
re-reading `111` before starting, which is now the only reliable detector the
project has for this defect.

**Kill condition, filed first:** *if no `Family` realises the witness at every
height, the `ZeroData` witness does not support the claim and `111`'s sentence
must be downgraded at its location.* **It did not fire** — the gap closed upward.

* `constFamily` (new) — the constant family on one configuration. `Proportion`
  and `ProportionStd` are asymptotic, so a witness only bites once it is placed
  in a family, and a constant family is the cheapest placement.
* `baseline_cap` / `baseline_cap_witness` (new, axiom-free) — the `111`
  configuration in a constant family satisfies `ProportionStd 0.6725` and
  **fails** `Proportion 0.50944`.

So: **no theorem of the form "`ProportionStd 0.6725` ⟹ `Proportion κ`" holds with
`κ ≥ 0.50944`.** The ledger certifies `0.50875`. The gap is `0.00069`, and it is
the discretisation of the `1000 : 321` witness rather than slack in the method.

`111`'s sentence is annotated at its location: it stands, but it did not follow
from what was proved beneath it when written.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project's most reliable instrument is not any of
its five guards but the habit of re-reading the previous cycle before starting
the next, because the errors that survive everything else are the ones where the
prose is one quantifier ahead of the proof.


# SESSION 113 — an instrument built, calibrated, and failed

`S38` recorded that quantifier drift has now been caught twice by re-reading and
never by an instrument. The honest response to a defect that recurs is to build
the detector, so this cycle built it.

**Kill condition, filed first:** *if the detector does not fire on `S37`'s and
`S38`'s own sentences, it does not detect the defect it was built for and I do
not ship it.* **It fired.**

`forensics/scope_gate.py` looks for the shape both failures share: a **universal**
sentence citing an **existential** theorem. An existential exhibits one object; a
universal ranges over all of them; the step between is where both errors lived.
It reads real declaration types out of `audit/Declarations.lean` via `lake`, and
refuses to report a pass when `lake` is unavailable.

**Calibration: 0 of 2.** It fires on neither sentence it was designed for.

**And the reason is the finding.** Both sentences drift *by dropping the
citation*. The prose generalises away from the theorem and stops naming it — the
name stays in an adjacent paragraph. So the signature I designed for is the one
shape the defect never has. Widening to paragraph or section scope over-fires
immediately: every session entry contains universal prose and existential
witnesses by construction.

Its single live flag — `Capacity.reweighting_worst_case`, where the prose says a
worst case is "attained" — is a false positive, and correctly so: attainment
*is* an existential claim, and saying so is not drift.

**Verdict.** The file is kept and its docstring rewritten to say it failed, why,
and not to rebuild it. It is not registered as a guard and its output must not be
quoted. The control for this defect class remains re-reading the previous cycle
before starting the next — which caught `S37` and `S38` both, and is the only
thing that has.

Logged as `S39`: I expected the defect to be lintable, and building the linter is
what showed it is not.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** a failure mode that hides by removing its own evidence
cannot be caught by looking at the evidence, which is why this project's most
effective guard is a habit rather than a script.


# SESSION 114 — the cap survives everything the baseline implies

`112` capped baseline-only arguments at `0.50944`. A cap is only worth having if
its witness also survives the facts the project has *derived* from the baseline;
if any of them excluded the witness, adjoining that fact would push the row
higher and the cap would be an artifact of ignoring our own results.

**Kill condition, filed first:** *if the witness violates any certified
consequence of the baseline, the cap is not robust.* It did not fire.

`cap_witness_respects_derived` (new, axiom-free) gives the witness's full
accounting — `N = 1963`, `NscStd = 1321`, `Nsc = 1000`, `N_off = 642`,
`hauntedCount = 321` — and checks it against every certified consequence:

| certified fact | witness | verdict |
|---|---|---|
| `certified_offline`: `N_off ≤ 0.3275·N` (`090`) | `642/1963 ≈ 0.32705` | inside, by `0.00045` |
| `N_off + NscStd ≤ N` (`090`) | `642 + 1321 = 1963` | **tight** |
| `2·hauntedCount + NscStd ≤ N` (`110`) | `642 + 1321 = 1963` | **tight** |
| `Nsc + N_off ≤ N` | `1642 ≤ 1963` | slack |

**The pattern is the reassuring part.** The witness saturates exactly the two
bounds that `104` and `110` proved are tight on simple/haunted mixtures, and sits
*inside* the one bound that is not — the off-line density row — with `0.00045` to
spare. That is what a genuinely extremal configuration should look like: tight
where the theory says tight, slack where it says slack.

So the cap at `0.50944` is not an artifact of ignoring our own results. Every
consequence the baseline has been made to yield is consistent with a
configuration whose `Nsc` row is `0.509424`.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project has proved four separate things about ζ's
zero counts and a single 1963-zero configuration satisfies all of them while
sitting at the certified floor, which means the floor is the theory's, not the
zeta function's.


# SESSION 115 — claude.ai's three answers, wired in, one audit closed negative

The `111` briefing asked three questions. All three came back. This cycle wires
them into the registers and runs the one audit they suggested.

**(i) The ξ′ blocker has a citation.** `NzComparable` — `N_{ξ'}(T) = N_ζ(T) +
O(log T)` — is **Conrey, J. Number Theory 16 (1983), 49–74**, which proves the
counting for all `ξ^(m)`; ξ's zeros are ζ's nontrivial ones. Berndt (1970) covers
ζ-derivatives if ever needed. Filed **[RECALL, UNVERIFIED]** — neither paper has
been read here, and a citation is a pointer, not a discharge. `OffTransfer`
remains open.

**The audit it suggested closes negative, and that is the honest result.**
claude.ai flagged that Conrey 1983 gives `≥ 81.37%` of ξ′'s zeros on the line,
upgraded to `82.402%` by the `θ = 4/7` mollifier, and asked whether the repo's
constant reflects the upgrade — with a possible free improvement attached.

> It reflects neither and beats both. `zeta23_xiPrime` asserts
> `Proportion 0.85838`, and `Proportion` is the **simple-and-on-line** count —
> strictly stronger than "on the line". No free points.

Checking took one `sed`; assuming would have put a wrong number in `PRICES.md`.

**(ii) The haunted density has no name, and the namelessness is explained.** It
exists only unconditionally: vacuous under RH, and provably invisible to the
classical `μ_T` quantities by our own `Blindness`. The nearest named object is
the distinct-zeros deficit `N(T) − N_d(T)`, of which it is the cross-term nobody
has separated. Recorded in `LEADS.md` for the packaging.

**(iii) The corpus provably cannot contain `105`'s hypothesis — and this is a new
instrument function.** `haunted_indistinguishable_from_triple` (new, three lines,
axiom-free): a haunted mass-`3` ordinate and an on-line triple zero are the same
`μ_T` atom. So every pair-correlation and repulsion statement excludes both or
neither, and none excludes triple zeros. Repulsion governs *distinct* ordinates;
exact coincidence is the gauge-invisible direction.

**`METHOD.md` gains the general form:** an impossibility theorem can retire a
reading task. "We searched and found nothing" is weak; "the corpus cannot contain
it, here is the theorem" is a result. Caveat stated — it prunes only corpora
whose statements are invariant in the relevant sense.

**And `LEADS.md` gains the hierarchy:** LI ⟹ all ordinates distinct ⟹ no
haunting. `NoHaunted` is the **weakest** member — milder than the standing
hypothesis of the prime-race literature. Empirically, the verified zeros to
`3×10¹²` have pairwise distinct ordinates, so haunting is absent at computed
heights exactly as off-line zeros are.

**Ruling for Joop, now concrete.** Discharging `NzComparable` means extending the
zeta-23 import or adding an axiom, and adding one would raise the certified
proportion by `+9.29`, which `Assumptions.lean` forbids. My reading is that a
counting-function comparison is a different kind of object from a proportion
axiom and may be admissible where a proportion axiom is not — but that is
doctrine, and yours.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the project's central unknown has no name because it
can only be seen from a position almost nobody has occupied — unconditional, and
looking at coincidences rather than spacings — which is either why it is
worthless or why it is available.


# SESSION 116 — certifying the hierarchy changes what it says

`115` recorded claude.ai's chain `LI ⟹ all ordinates distinct ⟹ no haunting`
with `NoHaunted` as its weakest member, framed as "milder than what the bias
literature routinely assumes". Certifying it turns up something the prose form
hides.

**Kill condition, filed first:** *if `NoHaunted` itself implies `N_off = 0`, it
is RH-in-window and worthless as a conditional hypothesis.* It did not fire —
but the **middle member of the chain does imply it**.

* `noHaunted_of_allDistinct` — the chain's second link, as advertised.
* `Noff_eq_zero_of_allDistinct` — **and distinct ordinates force `N_off = 0`.**
  The functional equation puts every off-line zero at the same height as its
  partner, so an off-line zero forces mass `≥ 2`. "All ordinates distinct" *is*
  RH-in-window.
* `noHaunted_not_imp_Noff_zero` — while `NoHaunted` does not. Witness:
  `configAt 0 0 1 a`, a lone off-line pair, whose ordinate has `onAt = 0` and is
  therefore unhaunted, with `N_off = 2`.

**So the ordering was right and the emphasis was wrong.** `NoHaunted` is not
merely the weakest member of the chain — it is **the only member that is not
already the conclusion**. `LI` presupposes RH; distinctness is RH-in-window; a
conditional row keyed to either would be conditioning on what the project is
trying to prove. A row keyed to `NoHaunted` is not, because it permits off-line
zeros and forbids only their coincidence with a lone critical zero.

That is the load-bearing fact for the packaging, and it is stronger than the
positioning claim it replaces: not "we assume less than the field does" but
"we assume something the field's hypotheses make vacuous".

`LEADS.md` is annotated at the location of `115`'s entry.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** every standard hypothesis in this neighbourhood
assumes the Riemann Hypothesis before it says anything about coincidences, so
the one condition that separates the two questions had to be invented here or
not at all.


# SESSION 117 — the chain closed, and the positioning is now a theorem

`116` proved `NoHaunted` does not imply RH-in-window. The other direction
completes the comparison and settles how the conditional row should be described.

**Kill condition, filed first:** *if RH-in-window fails to imply `NoHaunted`, the
chain breaks at its last link and the two hypotheses are not comparable at all.*
It did not fire.

* `noHaunted_of_Noff_zero` (new, axiom-free) — with no off-line zeros, a
  standard-simple ordinate has `H = onAt = 1`. The last link.
* `noHaunted_strictly_weaker_than_RH` — the link *and* its strictness in one
  statement, the witness being `116`'s lone off-line pair.

So the chain is complete and its final step is proper:

> `LI` ⟹ all ordinates distinct ⟹ `N_off = 0` ⟹ `NoHaunted`, strictly.

**The positioning statement is now a theorem.** The project's conditional row —
`Proportion 0.6725` from `NoHaunted` — is keyed to a hypothesis **strictly weaker
than RH restricted to the window**. `115` had this as "milder than what the bias
literature assumes", which was a comparison to a convention. `116` sharpened it
to "the only member of the chain not already the conclusion", which was a
comparison to a list. This is a comparison to RH itself, and it is certified.

Three cycles to get one sentence right: a convention, then a list, then the
theorem. That progression is the method working, and it is worth noting that
each step was prompted by *certifying* the previous one rather than by doubting
it.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project can now state its best conditional result
as "assume strictly less than the Riemann Hypothesis on this window and the
literature's proportion transfers whole", which is a sentence about the shape of
the problem rather than about our arithmetic.


# SESSION 118 — one conditional instrument, and a third route to the same number

Everything in the `084`–`117` arc is a conditional row of some shape, and they
have accumulated as separate theorems. `109`'s identity says they should not be
separate: the row is a subtraction, so every conditional result is a bound on the
subtracted term.

**Kill condition, filed first:** *if a haunted-density bound gives no better than
`087`'s off-line route `κ − β/2`, the direct form adds nothing.* It fired **in
the reading that matters least** — the two agree when translated — and the point
is the translation itself.

* `HauntedDensity` / `proportion_of_hauntedDensity` (new, axiom-free) —
  **`ProportionStd κ` with `hauntedCount ≤ δ·N` gives `Proportion (κ − δ)`.**
  Two lines from the identity. `NoHaunted` is `δ = 0`.
* `hauntedDensity_of_offLineImport` — and `087`'s off-line route is the special
  case `δ = β/2`, since a haunted ordinate carries at least two off-line zeros.
  So the earlier instrument is a corollary of this one, not a sibling.

**A third derivation of the certified row.** `certified_nsc_via_haunted` runs
`certified_offline` (`β = 0.3275`) through the halving and the subtraction:
`0.6725 − 0.16375 = 0.50875`. Three derivations now agree exactly — the per-atom
bound of `084`, the off-line exchange rate of `090`, and the haunted density.
After `S34` I do not think a large claim resting on one chain is safe; it now
rests on three that share only the baseline.

`LEADS.md` records the unification: **there is one conditional instrument, not
five**, and every hypothesis the project has priced is a `δ`.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project has exactly one conditional theorem and
has been discovering it in pieces for thirty-four cycles, which suggests the
right first move on any new hypothesis is to ask what `δ` it buys rather than
what route it opens.


# SESSION 119 — the ladder was the same instrument, and its `δ` is now exact

`118` unified the conditional results under `hauntedCount ≤ δ·N ⟹ Proportion
(κ − δ)` and put the mass ladder in the table with its `δ` written as
`(κ − 1/m)/…` — a placeholder I did not check. That is the kind of thing that
becomes a stale number if nobody returns to it.

**Kill condition, filed first:** *if the ladder is not an instance of the density
instrument, `118`'s unification is wrong and must be corrected at its location.*
It is an instance.

* `pred_mul_haunted_add_NscStd_le_N` (new, axiom-free) —
  **`(m−1)·hauntedCount + NscStd ≤ N`**, which is `110`'s canonical bound with
  `3` replaced by `m`. `110` is the case `m = 3`.
* `hauntedDensity_of_noSmallHaunted` — hence `NoSmallHaunted m` with
  `ProportionStd κ` gives `HauntedDensity ((1 − κ)/(m − 1))`.

**The `δ` is exact and the arithmetic checks against `105` independently:** at
`m = 3`, `δ = 0.3275/2 = 0.16375` — the ledger's; at `m = 5`,
`δ = 0.3275/4 = 0.081875` and `0.6725 − 0.081875 = 0.590625`, which is `105`'s
number reached without going through `105`'s theorem.

So the unification is complete: `NoHaunted`, the off-line import, the mass
ladder, and the certified row are four readings of one conditional theorem, and
the placeholder in `118`'s table is replaced by the certified expression at its
location.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** a placeholder written into a table survives every guard
the project owns, because nothing checks that a formula was ever derived — only
that claims cite theorems, and a table cell cites nothing.


# SESSION 120 — the sweep that looked for placeholders and found a stale grade

`119` ended by naming a gap: nothing checks that a formula in a table was ever
derived, because a table cell cites nothing. The narrow tell — an ellipsis inside
a formula — is checkable, so I swept for it.

**Kill condition, filed first:** *if the sweep finds no placeholders beyond the
one already fixed, the defect was a one-off and no guard is warranted.* **It
fired.** Every ellipsis in the registers is a legitimate use: quotation elision,
truncated commit hashes, numeric ranges. No guard built.

**But the sweep found something it was not looking for.** `CLAIMS.md`'s
provenance table graded

> `0.6725126` and the whole `λ`-sweep — **`ISSUES` #29 — code not in repo**

and `#29` was resolved about ninety cycles ago: `forensics/window_opt.py`
reproduces the sweep from the register's own specification. The grade was never
updated. `CLAIMS.md` is the register that is supposed to be the authority on what
is verified, and it was carrying a ninety-cycle-stale "not verified" on something
verified.

**Checking it properly turned up a second, smaller thing.** The script's check
list held **two** of the sweep's five rows. So "fully reproduced" would have been
an overclaim in the other direction. I ran the remaining three:

| λ | `c*` | `2 − 1/c*` |
|---|---|---|
| 1.25 | `0.8299265` | `0.7950740` |
| 1.50 | `0.8728770` | `0.8543632` |
| 2.00 | `0.8995905` | `0.8883831` |

All three reproduce to seven digits. The check list now holds all five, so the
grade cannot go stale again without the script failing.

Corrected at the location of the grade, with the staleness noted in the cell
rather than only here.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** a register that records failures faithfully will keep
recording them after they are fixed, because the discipline that files a defect
is not the discipline that closes one.


# SESSION 121 — the stale-grade sweep, and it was not isolated

`120` found a ninety-cycle-stale "code not in repo" in `CLAIMS.md`. That is the
*opposite* failure mode from the one the overclaim gate hunts: a register saying
something is **un**verified when it is verified. One instance is an accident; the
question is whether it is a species.

**Kill condition, filed first:** *if every remaining negative grade in
`CLAIMS.md` is still accurate, the `120` case was isolated and no systematic
staleness exists.* **It did not fire — two more.**

* **`0.6818287`, the bandlimited ceiling** — graded *"Lean ✓ (imported;
  unreachable from our root — parked)"*. W34a's discharge made it reachable.
  Verified this cycle rather than taken from the prompt: `#check
  @Zeta23.PairCeiling.ceiling_law256` resolves under `import Riemann`. Corrected.
* **The audit header** — *"`#29` is the sole missing-computation defect"*, true
  when written, and `#29` has since been resolved. The count is **zero**, not
  one. The audit's *conclusion* stands; its subject does not. Corrected at the
  header rather than only in the table row below it.

**Three stale negatives in two cycles, all of the same species.** The project's
guards are asymmetric: `claims_gate` patrols for claims that are too strong, the
provenance lint patrols for unsupported numbers, and **nothing patrols for
pessimism**. A grade that says "not done" is never challenged, because no
instrument is offended by understatement and no cycle is motivated to revisit a
closed-looking cell.

That asymmetry is worth naming and I am not building a guard for it — `113` and
`120` both showed what happens when I build an instrument for a defect I have
seen twice. The control is the same as for quantifier drift: when a cycle
discharges an issue, sweep the registers for *its number*, not only for its name.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** a project that grades itself honestly will drift
pessimistic, because every incentive it has built points at catching overclaims
and none at catching the moment a defect stopped being true.


# SESSION 122 — it is the headers that go stale

`121` found stale negatives in `CLAIMS.md` and named the species: nothing patrols
pessimism. `ISSUES.md` is where that costs more, because `LOOP.md` step 2 says a
cycle begins by **re-reading `ISSUES.md`** — a stale "open" there misdirects work
rather than merely misreporting it.

**Kill condition, filed first:** *if every open `ISSUES` entry is genuinely still
open, the staleness was confined to `CLAIMS.md` and the sweep is complete.* **It
did not fire — two more, and they sharpen the diagnosis.**

* **`#30`** — the loop-liveness defect. Its **body** has recorded the cron-heartbeat
  fix since `2026-08-15`. Its **header** still read `[bin 3, process] R17 was
  never applied…`, with no fixed marker.
* **`#13`** — `Nsc` vs `NscStd`. Header: *"only the axiom restatement is still
  Joop's"*. The restatement landed: `baseline_zeta23` and `baseline_przz` are
  both stated on `ProportionStd` today.

**The sharper diagnosis: it is the headers.** In both cases the body was updated
faithfully and the header was not. Bodies get edited because that is where the
new information goes; headers are navigation, and nobody edits navigation while
holding a result. A scan of headers — which is exactly what the surface scan
is — therefore sees a strictly more pessimistic project than the bodies describe.

`#13`'s correction carries a second thing worth having: it is no longer a
convention question. `Fiber.Nsc_eq_NscStd_iff_noHaunted` makes it the project's
central open quantity — the two notions coincide **iff** no ordinate is haunted.
Session 003's bookkeeping issue and session 108's `hauntedCount` are the same
object, and the header now says so.

`#30` gets a caveat rather than a claim: the heartbeat was created with a 7-day
auto-expiry and dies with its session, so *whether it is running* is live state
and `R17` forbids asserting it either way — which is the very rule `#30` exists
to record.

**Three cycles of sweeping is the R20 cap, and this is the third.** Next cycle
returns to mathematics regardless of what a fourth sweep might find.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the registers are honest in their paragraphs and
pessimistic in their titles, and since titles are what a tired reader scans, the
project has been systematically understating itself to itself.


# SESSION 123 — the fifth instance, and what `(★)` is actually for

`118` unified the conditional results and listed four instances. There is a
fifth, and it is the one that changes how `(★)` should be read.

**Kill condition, filed first:** *if the `/6` bridge is not an instance of the
density instrument, `118`'s unification is incomplete and must be scoped.* It is
an instance.

* `six_mul_haunted_add_N_le_Nstar` (new, axiom-free) — **`6·hauntedCount + N ≤
  N⊛`**. This is `Basic.six_mul_NscStd_le` read through `109`'s identity, and the
  arithmetic explains its `6`: a haunted ordinate has mass `≥ 3`, contributing
  `≥ 9` to `N⊛` and `3` to `N`, a surplus of exactly `6`.
* `hauntedDensity_of_starBound` — hence a star bound `C` gives
  `HauntedDensity ((C−1)/6)`, and the `/6` bridge is the instrument's fifth
  instance.

**And that settles what `(★)` is for, in this project's own currency.** There are
exactly three certified bounds on the haunted count:

| bound | consumes |
|---|---|
| `2·hauntedCount ≤ N_off` | the off-line count (`083`) |
| `2·hauntedCount + NscStd ≤ N` | the baseline alone (`110`) |
| `6·hauntedCount + N ≤ N⊛` | **`(★)`** |

> ⚠️ **"Exactly three" was wrong — `124` found a fourth.** The third factorial
> moment bounds the haunted count too (`six_mul_haunted_le_factMoment_three`).
> Its value is nil, which is why I did not see it: I enumerated the bounds that
> *pay* and wrote the sentence as though I had enumerated the bounds that
> *exist*. The conclusion below about `(★)` is unaffected — the fourth bound
> consumes neither `(★)` nor anything else certified.

Only the third consumes a star bound. So **`(★)`'s entire contribution to the
`Nsc` row is a bound on the haunted count** — Routes I and III exist to buy a
`C`, and what a `C` buys is a `δ`. It beats the unconditional `0.16375` exactly
when `C < 1.9825`, which is the threshold `098` reached from the multiplicity
side; the two derivations of that number were independent and I did not notice
they had to agree until now.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the second moment, the off-line count and the
literature's proportion are three different ways of paying for the same thing,
and the project's whole route table is a price list for one quantity nobody else
has named.


# SESSION 124 — "exactly three" was wrong, and the fourth is worthless

`123` wrote *"There are exactly three certified bounds on the haunted count"*.
That is an enumeration claim, which is the `S34` shape, so it gets checked rather
than trusted.

**Kill condition, filed first:** *if the third moment gives no bound on the
haunted count, "exactly three" stands and no correction is needed.* **It fired.**

`six_mul_haunted_le_factMoment_three` (new, axiom-free):
**`6·hauntedCount ≤ Σ H(H−1)(H−2)`**. A haunted ordinate has mass `≥ 3`, so it
contributes `≥ 3·2·1 = 6` to the third factorial moment. The `6` is the same `6`
as in the `N⊛` bound and for the same reason — mass `3` is the cheapest haunted
ordinate — but the two consume different inputs.

**Its ledger value is nil, and that is the interesting part.** Nothing certified
bounds `factMoment 3`, and `Optimal.moment_route_walled` proves no moment
inequality of order `≥ 3` can be made to bind. So the fourth bound exists, is
sharp at mass `3`, and buys nothing.

**Which is exactly why I missed it.** I enumerated the bounds that *pay* and
wrote the sentence as though I had enumerated the bounds that *exist*. The two
lists differ by the ones with no supplier, and a claim about what exists cannot
be assembled by thinking about what is useful. Corrected at both locations —
`123`'s session entry and the `LEADS.md` table.

`123`'s conclusion about `(★)` is unaffected: the fourth bound consumes neither
`(★)` nor anything else certified, so "only one of these consumes a star bound"
remains true with four in the list.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** an enumeration made while thinking about value will
always be an enumeration of the valuable, and the project's registers are full of
sentences whose quantifier was set by what I was looking for rather than by what
is there.


# SESSION 125 — counting the bounds was the wrong operation

`123` said three certified bounds on the haunted count; `124` found a fourth and
corrected the number. Correcting a number twice is a sign the *frame* is wrong,
so this cycle tests the frame instead of extending the count.

**Kill condition, filed first:** *if every additional bound I can write down is
weaker than the certified `0.16375`, then counting was numerically harmless and
the enumeration frame can stay.* **It fired on the numbers and not on the
frame**, which is the finding.

Two more bounds, one line each:

* `three_mul_haunted_le_N` — `3·hauntedCount ≤ N`, since each haunted ordinate
  carries three zeros. Gives `δ ≤ 1/3 ≈ 0.3333`.
* `haunted_le_NscStd` — immediate from the identity, since `Nsc ≥ 0`. Gives no
  numeric `δ` at all, because the baseline bounds `NscStd` from *below*.

Both are strictly weaker than `110`'s `δ = 0.16375`. So the count was harmless
arithmetically — and that is precisely why it was misleading. **Bounds on this
quantity are cheap.** There is no interesting number of them; six exist because I
wrote six, and a seventh is available to anyone who wants one.

**The honest statement is not a count.** It is:

> `δ = 0.16375` is the best the certified inputs support, and `111` caps any
> baseline-only argument there.

A bound is worth listing when it is sharpest on an input actually held. `123`'s
sentence and `124`'s correction were both answering "how many?", which has no
useful answer; the question is "which is sharpest, and on what?". Corrected at
the `LEADS.md` table, above `124`'s correction rather than replacing it — the
sequence of three framings is itself the record.

Build green (3757 jobs), ledger unchanged at `NscStd 67.25% / Nsc 50.88%`,
axioms 2, base hash `cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** three cycles spent counting something uncountable is
what it looks like when a register's format asks a question the mathematics does
not have, and the fix was not a better count but noticing that the column should
never have existed.


# SESSION 126 — consolidation: every guard run, and what a passing guard's alarms mean

Three cycles of corrections-to-corrections (`123`–`125`) is a spent thread, and
`125` said so itself. The remaining substantive work is blocked on literature or
on Joop's rulings, so this cycle takes queue item 5: **re-run every guard.** They
have not all been run in a long time, and I have been implicitly relying on them
each cycle while only witnessing `lake build`.

**Kill condition, filed first:** *if every guard passes, this confirms the state
and I report a quiet green rather than manufacturing a finding.* **It fired.**

| guard | exit | verdict |
|---|---|---|
| `provenance_lint` | 0 | clean; **`GM_bridge` reports `BLOCKED`** — by design |
| `lemma1_guard` | 0 | clean; **`D = 4` reports `VIOLATES RH`** — by design |
| `quarry` | 0 | DAG intact |
| `w16_price` | 0 | unchanged; its `[RECALL, UNVERIFIED]` caveat still stands |
| `three_moment_lp` | 0 | unchanged; W35 still ill-posed pending realizability |
| `window_opt` | 0 | **PASS**, all five sweep rows (extended in `120`) |
| `surprises` | 0 | 39 entries, 55% externally corrected |

**The thing worth recording is the two scary-looking passes.**
`provenance_lint` ends `=> BLOCKED — do not build the table`, and
`lemma1_guard` prints `VIOLATES RH (Lemma 1)`. Both are **designed output on
known inputs**: the first is the guard correctly refusing the `GM_bridge` (the
`#27` death, recorded), the second is the guard demonstrating its own
discriminating power on a synthetic constant `D = 4`, not a claim about `ζ`.

A future cycle — or a compacted instance — scanning these outputs would read two
alarms in a clean suite. Recorded here so that reading is available without
re-deriving it, which is the same defect class as `122`'s stale headers: the
information was in the code and not where a scan would meet it.

**`claims_gate` counts, untriaged and not a defect rate:** `CLAIMS 4`,
`LEADS 56`, `E 14`, `FAILURES 17`, `PRICES 11`, `ISSUES 38`. `CLAIMS`'s four were
triaged in `101` (all false positives of known shapes). The rest have never been
triaged and per `R17` must not be quoted as anything.

Build green (3757 jobs), ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2, sorries
0, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** a guard suite that prints its designed refusals in the
vocabulary of failure will eventually be read as failing, so the last
undocumented thing in this project was what its instruments sound like when they
are working.


# SESSION 127 — the route table triaged, and it disagreed with itself

`126` recorded `LEADS.md`'s 56 `claims_gate` flags as untriaged. That is the
register `LOOP.md` step 2 sends every cycle to, so an untriaged count there is
owed under `R17`.

**Kill condition, filed first:** *if the flags are all known mechanical shapes,
the gate has nothing to say about the route table and I stop running it there.*
**It did not fire — 2 true positives in 56.**

* **"Whether the profile is minimal is not proved and is not claimed."** Settled
  both ways in `075` (`profile_not_minimal` — the ledger *is* a coarser
  sufficient statistic) and `077` (`profile_minimal_among_local`). Fifty cycles
  stale.
* **"`L5` is the only item that could move a number without closing a box."**
  `084` moved the `Nsc` row by `50.88` points without closing a box and without
  `L5`. A session-003 board assessment, never revisited.

**And the first one was found by the second half of the same file.** Flags 45–49
are the *corrected* minimality statements, filed in a later section by `075` and
`077`. So `LEADS.md` has been carrying the claim and its refutation
simultaneously, fifty cycles apart, and the gate found the pair. That is
`SURPRISES` S36 — a retraction filed somewhere other than the text it retracts —
repeating at the scale of a register rather than a docstring.

Rate **2/56 ≈ 3.6%**. Both catches are staleness, not overclaim, which remains
the defect class no instrument patrols.

**The prompt's own RECENT block carries the same stale sentence** — *"Minimality
of the profile is NOT proved and must not be claimed"* — which `LOOP.md`'s READ
FIRST banner has corrected since `102`. Three sources now agree it is stale and
one of them is the cron text, which only Joop can edit.

Build green (3757 jobs), ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** a register long enough to contain both a claim and its
refutation will be read as agreeing with whichever half the reader reaches first,
and this one is ordered oldest-first.


## `127` follow-up — a commit message that claimed a clean gate it had not run

The leads briefing was drafted, gated, one sentence downgraded, and committed
with the message *"gate-clean"*. **It was not.** My downgrade edit did not match
the file — the sentence was line-wrapped differently from my replacement string —
so the substitution silently did nothing, the gate still reported one flag, and
I wrote the commit message from the *intent* rather than from the re-run.

Fixed: the sentence now names its witnesses (`noHaunted_strictly_weaker_than_RH`,
`Noff_eq_zero_of_allDistinct`) and scopes itself to the chain I actually checked,
with an explicit ask to claude.ai about hypotheses outside it. Gate reports `0`.

**This is `R17` on my own commit message.** Every cycle I witness `lake build`
before saying it is green; I did not witness the gate before saying it was clean.
A string replacement that fails silently is exactly the shape that needs a
witness — and the guard *did* fire, into a terminal I had already stopped
reading.


# SESSION 128 — the same stale claim in two registers

`127` triaged `LEADS.md`; `E.md` (14 flags) and `FAILURES.md` (17) had never been
done.

**Kill condition, filed first:** *if both are all known mechanical shapes, the
gate has nothing to say about these registers and I stop running it on them.*
**It did not fire — 1 true positive in 31, and it is duplicated.**

> *"The only capacity certificate we can run came in with zeta-23"*
> — `LEADS.md` 962 **and** `FAILURES.md` 275, differently worded.

`Riemann/Capacity.lean` carries eleven capacity theorems of our own, axiom-free
and in the audit. `LEADS.md` even names the repair in the next paragraph — *"next
rung-0 item, and it is cheap"* — and it was done: `no_gain_past_known` **is** that
statement. So the register is carrying a defect, its proposed fix, and no note
that the fix landed.

**The sub-species is new and worth naming: the duplicated stale claim.** A
sentence copied between registers goes stale in both, and correcting one leaves
the other. Neither `121` nor `127` would have caught this — `121` swept
`CLAIMS.md`, `127` swept `LEADS.md`, and each would have found a copy and moved
on satisfied. `METHOD.md` gains the rule: **grep the sentence, not the file.**

**And the wildcard, bought by `127`'s own slip.** `METHOD.md` also gains *assert
before replacing*: a `str.replace` that does not match is a silent no-op, which
is how `127` shipped a commit message claiming a clean gate it had not re-run.
Every scripted edit now asserts its target exists first — the assert is the
witness that the edit had somewhere to land.

Rate across the three register triages: `LEADS` 2/56, `E` + `FAILURES` 1/31,
`CLAIMS` 0/4 (`101`). **3 true positives in 91, all staleness, none an
overclaim.**

Build green (3757 jobs), ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash
`cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the guards were built when the danger was saying too
much, and the project has since aged into a state where every defect they find is
the opposite one.


# SESSION 129 — the central quantity gets a certified number

Thirty cycles of work identified `hauntedCount` as the thing the `Nsc` row is a
subtraction of, gave it a name, characterised its extremal configurations, capped
what the baseline can say about it, and placed its vanishing in the hypothesis
hierarchy. **It had never been stated as a certified fact about `ζ`.**

**Kill condition, filed first:** *if the haunted density needs anything beyond
`certified_offline`, there is no such row.* It did not fire.

`certified_haunted`: **`hauntedCount ≤ (0.16375 + o(1))·N`** — at most `16.375%`
as many haunted ordinates as zeros. `#print axioms` gives `baseline_zeta23` and
`zetaNonempty`, the same two every other row consumes. It is `certified_offline`
halved, because a haunted ordinate carries at least two off-line zeros.

**It is essentially attained.** `114`'s witness has `hauntedCount = 321` against
`N = 1963` — density `0.16352`, where the bound permits `321.44`. The slack is
**less than half a haunted ordinate**, and it is the discretisation of the
`1000 : 321` ratio rather than looseness.

**Why this was worth a cycle rather than being implicit.** The proof is four
lines and every ingredient existed. But the arc's whole conclusion is that the
project trades in `δ`, and until now `δ` appeared only inside other theorems'
proofs — the price list quoted the row and never the floor. A quantity named in
thirty cycles of registers and never stated about `ζ` is exactly the kind of gap
`121`–`128` were finding in the other direction.

Not added to `tools/metric.json`, for `certified_offline`'s reason: the ledger
maximises over rows, and an upper bound on a defect is not commensurate with a
lower bound on simple zeros.

Build green (3757 jobs), ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash
`cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** the project's central object went thirty cycles without
a number attached to it because every cycle used it as a step and none treated it
as a result.


# SESSION 130 — two more steps promoted to results

`129` closed a gap of a specific shape: a quantity used as a step in thirty
cycles of proofs and never stated as a fact about `ζ`. That shape is checkable
for the other visible quantities.

**Kill condition, filed first:** *if the `ζ` instantiations already exist, there
is no gap and I say so.* **It did not fire — neither existed.**

* `atomCount_ge_of_proportionStd` was proved in `091` as a general theorem about
  families and **never instantiated**. Now `certified_atomCount`: `ζ` has **at
  least `67.25%` as many distinct ordinates as zeros**, so its **mean vertical
  multiplicity is at most `1/0.6725 ≈ 1.487`**.
> ⚠️ **`131`: these are not two findings.** `Fiber.oddAtoms_le_atomCount` — the
> odd ordinates are a subset of the ordinates — makes the second a **corollary**
> of the first. The odd-mass statement is the result; the mean-multiplicity
> reading is its weaker shadow.

* `oddAtoms` had **no Family layer at all** — it existed only on `ZeroData`,
  despite `079`'s `NscStd ≤ oddAtoms` being one of the seven bounds the haunted
  atom saturates. Now `certified_oddAtoms`: **at least `67.25%` as many odd-mass
  ordinates as zeros**, since every standard-simple ordinate has odd mass.

Same axiom tier as every other row, and both proofs are one line given what
existed.

**The pattern behind all three of `129`/`130`'s finds.** A theorem proved to
*enable* something gets stated at the generality the enabling needed — over
families, over arbitrary `κ` — and the `ζ` instance is skipped because nothing
downstream wanted it. The project's certified statements about `ζ` are therefore
a strict subset of what it has proved about `ζ`, and the difference is invisible
because both halves are green.

That is the mirror image of `121`–`128`'s stale negatives: there the registers
understated by *not updating*; here they understate by *not instantiating*.

Build green (3757 jobs), ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash
`cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** a formal development records what was needed, not what
was true, so the list of things this project can say about the Riemann zeta
function is shorter than the list of things it has proved — and only by writing
the instantiations does the difference become visible.


# SESSION 131 — the two findings were one

`130` closed a gap by instantiating two general theorems for `ζ` and presented
them as two certified statements. Before building anything on that, the cheap
check: are they independent?

**Kill condition, filed first:** *if `oddAtoms ≤ atomCount` fails, the two are
independent and `130`'s presentation stands.* **It fired.**

`oddAtoms_le_atomCount` (new, one line): the odd-mass ordinates are a **subset**
of the ordinates. So *"at least `67.25%` as many odd ordinates as zeros"* implies
*"at least `67.25%` as many distinct ordinates as zeros"*, and `130` reported a
result and its corollary as two results.

**The correction makes the statement stronger, not weaker.** The mean-multiplicity
reading — *"at most `1.487` zeros per ordinate"* — is the shadow. What is actually
proved is that at least `67.25%` of the ordinate count is **odd**, which says
something about the *parity structure* of `ζ`'s vertical multiplicities that the
averaged form discards.

Corrected at three locations: the docstring, the `CLAIMS.md` row, and `130`'s
session entry.

**And this is the third distinct way the same audit has gone wrong.** `121`–`128`
found registers understating by not updating; `129`–`130` found them understating
by not instantiating; this is overstating by *double-counting a consequence*. All
three are the same underlying thing — the difference between what is proved and
what is written down is not tracked by anything, in either direction.

Build green (3757 jobs), ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash
`cd7a22e688df` unmoved. No ruling raised.

**Might-mean, unhedged:** counting results is as unreliable as counting bounds
was in `125`, and for the same reason — a list assembled while proving things
records the order they arrived in, not the order they depend on.


# SESSION 132 — the deficit is the currency, and the genre already exists

claude.ai answered the `127` briefing. One answer was directly actionable and is
now certified; the rest reshape the packaging.

**Kill condition, filed first:** *if the distinct-zeros conversion gives a worse
`δ` than `0.16375`, the route is not equivalent and the currency is weaker than
ours.* It did not fire — it gives **exactly** `0.16375`.

**The mathematics.** `two_mul_haunted_add_atomCount_le_N` (new, axiom-free):
`2·hauntedCount + atomCount ≤ N`. Since `N − atomCount` is the **distinct-zeros
deficit** `N(T) − N_d(T)` — a quantity the literature names — a haunted ordinate
contributes at least `2` to it, so any distinct-zeros proportion `N_d ≥ c·N`
gives `δ = (1−c)/2`.

**And the project already holds such a proportion.** `certified_atomCount` is
`N_d ≥ (0.6725 − o(1))·N` at the baseline tier — exactly the quantity the
haunting literature would have to supply — and it converts to `δ = 0.16375`
(`certified_haunted_via_distinctZeros`). Two shelves, off-line and
distinct-zeros, pay the same price, and `111` caps both. `130`'s instantiation,
written to close a bookkeeping gap, turns out to be the bridge to the named
literature.

**`OffTransfer` is Conrey 1983 — the same paper as `NzComparable`.** Both halves
of the `+9.29` route are one 1983 item. **[RECALL, UNVERIFIED]**; the ruling for
Joop is unchanged in substance and much sharper in cost.

**The genre exists and is two years old**, which is better than the alternative I
had been drifting toward. Members are location-shaped (BGST 2024),
statistics-shaped (Goldston–Suriajaya; GLSS), and density-shaped (Aryan).
`NoHaunted` is a member of a **new kind — pure coincidence** — constraining
neither where zeros are nor how they correlate. So the headline is **not** "a new
hypothesis"; it is **a classification of a young genre, with its weakest member
exhibited and its normal form proved**: every member's conclusion factors through
`ProportionStd κ + hauntedCount ≤ δ·N ⟹ Proportion (κ − δ)`.

That is a better claim than the one I was assembling, and it is smaller.

**Filed, not built:** claude.ai's expiry design for stale text — `valid-as-of:
<commit>` plus a dependency-triggered flag script. Its argument answers `113` and
`120` directly: staleness has no local signature, so detect nothing and invalidate
instead. Recorded in `METHOD.md`; the retrofit is a cycle of its own.

**Also filed:** read zeta-23's own Appendix C on responsibility before `FRAMING`'s
final form. One fetch, and a live precedent from eleven days ago.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2,
base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the quantity this project invented a name for is the
cross-term of one the literature has studied since 1993, and the conversion rate
is one-half — so the haunting problem was never unreachable, only unaddressed.


# SESSION 133 — expiry rejected before building; and the harness dispatch lands

**Kill condition, filed first:** *if the expiry design would not have caught the
defects this project actually found, it is the wrong instrument and I report that
instead of shipping it.* **It fired.**

`132` committed to building claude.ai's `valid-as-of` expiry. Tested first
against the four stale claims `120`–`128` found: **it catches none.** All four
were invalidated by something being **added** — a file created, an import added,
theorems proved — and none of them cited a dependency that moved. The
`0.6818287` row even cited its declaration correctly; what changed was
reachability, not the statement. Expiry asks "did my source move?", and the
defect is "does something now exist that I do not cite?".

Rejecting a design by analysis cost minutes; `113` and `120` each cost a cycle by
building first.

**`forensics/absence_queue.py`** instead — not a detector, a **queue**. Every
claim of absence is a standing obligation to re-check; the script lists them and
judges nothing. **Calibration 4/4.** Exit is always `0`. Its first run corrected
its own settled-filter: this project writes corrections *below* the text they
correct, so the following paragraph counts, and without that it re-flagged what
`127` and `128` had already fixed. **14 absence claims currently outstanding.**

**The harness dispatch is filed** in `LEADS.md` — six foreign-model tasks,
guards, and its own kill condition. **The plain-words rule is adopted now** and
written into `METHOD.md`: our dialect addresses the RH-primed region, and per
`E20` the grooves are where the blind spots are.

**And one escalation, because the data column cannot start.** `find` returns **no
numeric data anywhere in the repo**, and the sandbox network allowlist is
`github.com` only — Odlyzko's tables and LMFDB are unreachable. The cheapest item
claude.ai names, *"nobody has read the zero tables asking how close heights come
to sharing"*, is an afternoon's arithmetic and **none of it can begin** until the
files are on the machine.

> **Joop: widen the allowlist, or drop the tables into the repo.** This is the
> only thing blocking the flesh phase, and it is the one blocker I cannot route
> around.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2,
base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the project has spent a hundred cycles proving things
about an object it has never once looked at, and the instrument that would fix
that is a file download.


# SESSION 134 — the flesh phase starts, with no network

`133` escalated that the VPS holds no zero tables and reaches only `github.com`.
That blocks the Odlyzko items. It does **not** block `W36`: Frobenius eigenvalues
are computed by counting points, and point counts need no downloads.

**Kill condition, filed first:** *if the function-field measurement also needs
tables, the data column is wholly blocked and `133`'s escalation is total.* It
did not fire.

`forensics/function_field.py` — genus-2 hyperelliptic curves `y² = f(x)` over
`F_5, F_7, F_11`, exact integer point counts, exact rational polynomial `gcd` for
repeated roots. No floating point anywhere.

**The result, and it is the configuration the project cares about.** `12` of `195`
curves have a **repeated Frobenius eigenvalue** — an ordinate of mass `≥ 2` — in a
world where Weil's theorem puts every root on the critical line. That is
**crowding without haunting**: exactly what `NoHaunted` permits and RH-in-window
forbids, now exhibited in real arithmetic rather than in a synthetic `configAt`.

**Hand-verified witness.** `y² = x⁵ + 2x` over `F_7`: affine count `7`, one point
at infinity, `N1 = 8`, so `s1 = 0` and `e1 = 0`; with `N2 = 78`, `e2 = 14`, so

> `P(T) = 1 + 14T² + 49T⁴ = (1 + 7T²)²` — a perfect square.

**And the first run was wrong.** I added *two* points at infinity; `deg f = 5` is
odd and has exactly **one**. The uncorrected run reported a single hit — for a
curve that does not have one — and the corrected run reports twelve. Recorded in
the script rather than quietly fixed, because **the point count is the entire
input, and an arithmetic slip in it is indistinguishable from a finding.** That is
`R17` in the data phase: the build being green says nothing about whether I
counted right, which is why the witness is verified by hand.

**Grade `N`, not `A`** — this is a computation, not a Lean theorem, and
`CLAIMS.md` records it as such.

Build green (3757 jobs), sorries 0, ledger unchanged, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** the first arithmetic this project ever looked at
produced the exact configuration its central hypothesis was invented to permit,
which is either a good sign about the hypothesis or a reminder that a hundred
cycles of theory will find what it is shaped to find.


# SESSION 135 — the allowlist opened, and the project looked at zeros for the first time

Joop granted the network change and told me the permission gate was the mechanism.
The allowlist now carries `www-users.cse.umn.edu`, `www.lmfdb.org` and
`arxiv.org` beside `github.com`; a backup of the settings file sits next to it.
**Verified from inside the sandbox: all four return `200`.**

**Kill condition, filed first:** *if the table's precision floor is coarser than
the gaps it resolves, the census measures rounding rather than zeros and I must
say so.* It did not fire — the floor is `1e-9` and the smallest raw gap is
`0.0147`, seven orders above it.

**The census.** Odlyzko's `zeros1`: `100 000` zeros, `14.134…` to `74 920.827…`.
Normalised gap `δ_n = (γ_{n+1} − γ_n)·log(γ_n/2π)/2π`.

* **mean normalised gap `0.999986`** — the normalisation validates itself, which
  is the check that the arithmetic is right;
* **smallest normalised gap `0.021860`**, at height `71 732.901`;
* count below `δ` divided by `δ³`: `79 000 · 76 625 · 78 111 · 78 813` across
  `δ = 0.1 … 0.4` — **flat to ~3% over a factor of eight**.

**So the approach obeys the cubic law**: quadratic repulsion, the strongest
suppression of coincidence the random-matrix picture allows. The **constant** is
`0.71×` the GUE asymptotic `π²(n−1)/9 = 109 661`, and heights of `10⁴–10⁵` are
where convergence is reported slow — marked **[RECALL, UNVERIFIED]**, because I
have not checked that against the literature and will not let it carry the
sentence alone.

**Three things this does not show, stated because the temptation is real.**
Nothing below `1e-9`, which the table cannot resolve. Nothing about **off-line**
zeros, which the table does not contain. And therefore nothing directly about
`hauntedCount`, which needs an off-line zero at a shared height — this measures
only how close the **on-line** heights come to one another.

What it does give is the finite-height shadow of the coincidence question, and it
is the first time this project has looked at an actual zero. Graded **N**.

The table is `.gitignore`d — `1.8 MB` of someone else's data does not belong in
the repo, and the script re-fetches it.

Build green (3757 jobs), sorries 0, ledger unchanged, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** the zeros repel each other as hard as any random matrix
would, so the configuration the whole `Nsc` row hangs on is not merely unobserved
but actively suppressed — and the suppression is a fact about the data, while the
`0.16375` is still a fact about our arithmetic.


# SESSION 136 — the genre is real, checked rather than relayed

`132` built a packaging headline on a genre I had never read: *"the genre is two
years old, its members are location-, statistics- and density-shaped, and
`NoHaunted` is a new kind."* Every attribution was `[RECALL, UNVERIFIED]`.
`135` opened arXiv. So:

**Kill condition, filed first:** *if the cited papers do not say what the
registers record, the headline is wrong and gets corrected at its location.* **It
did not fire.**

| cited as | arXiv | verdict |
|---|---|---|
| PCC without RH | **2507.06823** | ✓ *"without the assumption of RH … asymptotically 100% … simple and on the critical line"* |
| Aryan `2/3`, density | **1902.05473** | ✓ *"…under a zero density hypothesis, which is weaker than the Riemann hypothesis"* |
| BGST, location | **2501.14545** | ✓ pair correlation applied to the **horizontal distribution** |

**What I am claiming and what I am not.** I read **abstracts**. That discharges
*"does the paper claim this"* and not *"is the claim correct"* — which is exactly
what a citation is for, and the distinction goes in the register rather than being
left to a reader.

**One figure declined.** The *"`1/3` unconditional"* attributed to BGST-I is not
in the abstract I read, so it does not enter the registers. The *Acta Arith.* 214
narrow box and its `61.7%` stay `[RECALL, UNVERIFIED]` — not on arXiv under the
id I was given, and I will not manufacture one.

**And an author list was wrong in my own notes.** `2507.06823` is Goldston,
**Lee, Schettler**, Suriajaya — four authors. I had been writing
"Goldston–Suriajaya" since `132`. Corrected.

**The find worth the cycle.** Aryan's paper is titled *"On an extension of the
Landau–Gonek formula"*. The `2/3` comes from **Landau–Gonek** — which is the
object `Fiber.landau` models and `landau_discriminates` proves separates the
off-line configurations. A member of this genre reaches its result through the
tool this project independently built as its discriminator, and neither
claude.ai's search nor mine surfaced that until the title was in front of me.
Filed as a lead: an abstract is not a proof.

Build green (3757 jobs), sorries 0, ledger unchanged, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** the project built a discriminator from first principles
and it turns out to be the same formula a stranger used to get two-thirds, which
means the tool was never the scarce thing — the coordinate it is pointed at was.


# SESSION 137 — the Landau excess, and a reading kept separate from its theorem

`136` found that Aryan's `2/3` comes from an extension of **Landau–Gonek** — the
object `Fiber.landau` models, and which `landau_discriminates` already shows
separates what `μ_T` cannot. This is the quantitative form.

**Kill condition, filed first:** *if some off-line configuration has a smaller
Landau sum than the all-on-line one, the excess is not monotone and the
connection fails.* It did not fire — AM–GM forbids it.

`landau_ge_N_mul_sqrt` (new, axiom-free): **`landau x D ≥ N·x^(1/2)`** for every
`x > 0`. The functional equation pairs `β` with `1 − β`, so
`2·landau = Σ (x^β + x^{1−β})`, and `x^β·x^{1−β} = x` makes each summand at least
`2√x`.

So the **excess `landau x D − N·x^(1/2)` is a non-negative measure of off-line
mass** — zero exactly when every zero is on the line, and each off-line pair
contributes `2√x·(cosh((β−½)·log x) − 1)`. The `cosh` that `E16` called "never a
metaphor" is now the coefficient of a certified inequality.

**And I nearly shipped a reading as a result.** The first docstring said the
`cosh` *is why* the genre's other members constrain location — an assertion about
papers I have read only the abstracts of. Rewritten to say what it is: the
theorem is the inequality; the explanation is a **conjecture about other people's
proofs**, offered as one. An off-line zero near the line is cheap in Landau
weight, so a Landau route gets no purchase without horizontal separation — which
*would* explain BGST's narrow box, and I do not know that it does.

That correction happened before the commit rather than two cycles later, which is
what `S37`'s lesson is supposed to buy.

Build green (3757 jobs), sorries 0, ledger unchanged, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** every off-line zero pays a toll in Landau weight and
the toll goes to zero as it approaches the line, so the horizontal coordinate is
not one hypothesis among several — it is the only direction in which this
instrument can be made to see.


# SESSION 138 — the certified floors, measured against real zeros

**Eight identical heartbeats arrived at once.** One cycle run, not eight;
recorded rather than glossed, because a burst of cron fires is exactly the kind
of live-state fact `R17` says not to narrate from memory. Whether the job is
double-scheduled is Joop's to check — I can see the prompts, not the crontab.

`135` put `100 000` real zeros on the machine; `129`/`130` certified six bounds on
precisely the quantities that data measures. Nobody had compared them.

**Kill condition, filed first:** *if any certified bound is violated by the data,
either the bound or my reading of the table is wrong, and that is the finding.*
**It did not fire — zero violations.**

| quantity | certified | observed |
|---|---|---|
| `Nsc/N` | `≥ 0.50875` | `1.00000` |
| `NscStd/N` | `≥ 0.67250` | `1.00000` |
| `atomCount/N` | `≥ 0.67250` | `1.00000` |
| `oddAtoms/N` | `≥ 0.67250` | `1.00000` |
| `N_off/N` | `≤ 0.32750` | `0.00000` *(RH-verified range)* |
| `hauntedCount/N` | `≤ 0.16375` | `0.00000` *(RH-verified range)* |

**All 100 000 ordinates are distinct at nine decimals** — checked, not assumed —
so `atomCount = N` is measured rather than inferred.

**What the table licenses and what it does not.** `zeros1` lists ordinates of
zeros **on the line**. From the file I can check distinctness. That no *further*,
off-line zeros exist in the range is the **RH verification** — a separate
literature fact, marked `[RECALL, UNVERIFIED]` — and it is what licenses reading
`N_off = 0`. Both such rows carry the label in the output, not just here.

**The gap is the price of universality, not evidence of weakness.** `Nsc` is
certified `0.50875` against an observed `1.0`, a slack of `0.49125` — and `111`
proves `0.50875` is within `0.00069` of the best **any** baseline-only argument
can reach. So the distance between our floor and the observed truth is almost
entirely the cost of proving something for all heights from one literature input,
not looseness we could tighten.

Build green (3757 jobs), sorries 0, ledger unchanged, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** the certified floor and the observed reality differ by
half the zeros, and almost none of that gap is ours to close — which is a
precise statement of how much of this problem is unproved rather than unknown.


# SESSION 139 — the convergence is real, and float64 nearly sold me a fake

`135` marked slow convergence to GUE as `[RECALL, UNVERIFIED]`. Odlyzko's higher
tables make it testable.

**Kill condition, filed first:** *if the constant does not move toward GUE at
greater height, either the slow-convergence recall is wrong or the normalisation
is.* It did not fire.

| height | `obs/GUE` |
|---|---|
| `t ~ 10⁴` | `0.712 ± 0.016` |
| `t ~ 2.7×10¹¹` | `0.885 ± 0.055` |
| `t ~ 1.4×10²⁰` | `0.868 ± 0.054` |

**Real at `3.0σ` between `10⁴` and `10¹¹`; `0.2σ` between `10¹¹` and `10²⁰`** —
unresolved at `10⁴` zeros. The honest reading, which the script prints itself:
convergence is visible and has largely happened by `t ~ 10¹¹`, and asserting
monotonicity across all three would be reading noise as signal.

**And the first run reported `obs/GUE = 33.8` at `10²⁰`.** `zeros4` lists offsets
from a base of `1.44×10²⁰` — 21 significant digits, against float64's ~16. I
formed `base + offset`, every entry rounded to the base, every gap became `0`,
and the ratio was a division by nothing. **The `mean δ ≈ 1` check caught it**: a
mean of `0.000000` is not a subtle symptom.

The fix is to never add. Gaps are differences, so the base cancels exactly; the
normalisation needs only `log(γ/2π)`, for which the base alone is ample. All
three regimes now report `mean δ` within `1.1×10⁻⁴` of `1`.

**That is twice in six cycles** — `134`'s point-at-infinity, now this — that the
data layer produced a confident wrong number, and both times a
self-validating quantity caught it rather than a guard. The lesson is worth its
place: **in the data phase, every computation carries a quantity whose correct
value is known in advance**, and that quantity is the whole of the review.

Build green (3757 jobs), sorries 0, ledger unchanged, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** the zeros look more like random matrices the higher you
go, and by the time they are twenty orders up they already do — so whatever makes
the low zeros exceptional is a feature of the beginning of the sequence, not of
the sequence.


# SESSION 140 — a pre-registered prediction, and it caught my own constant

`T2`-of-`W27`, never run: Selberg's central limit theorem for `S(t)`.

**Registered before computing:** `S(t)/√((1/2π²)·log log t)` is standard normal,
so **mean ≈ 0, variance below 1 and rising with height** — convergence is
famously slow and at `t = 7.5×10⁴` there is barely any `log log` to work with.

**Kill condition, filed first:** *if the variance is not near 1, either the
normalisation is misapplied or the counting function is wrong — and the counting
function is checked first.*

**It fired.** The first run gave variance `0.048`. The self-check passed —
`max |S(t)| = 0.795`, so `N(t)` recovered from the Riemann–Siegel `θ` matches the
table's own index — which left the other branch. I had written the normaliser as
`√(½ log log t)`; Selberg's variance is `(1/2π²)·log log t`. A factor of `π²`,
and `0.0483 × π² = 0.477`.

Corrected:

| band | `t` | mean | variance |
|---|---|---|---|
| first ¼ | `17.6 … 21 942` | `−0.0000` | `0.4431` |
| second ¼ | `… 40 432` | `0.0000` | `0.4786` |
| third ¼ | `… 57 962` | `0.0000` | `0.4890` |
| last ¼ | `… 74 921` | `0.0001` | `0.4958` |

**Mean is zero to four places in every band; variance is below `1` and rises
monotonically.** Both halves of the registered prediction hold, and the shortfall
to `1` is the slow convergence the prediction anticipated.

**Three data slips in seven cycles, none caught by a guard** — `134`'s points at
infinity, `139`'s float64 base, and now a constant off by `π²`. `METHOD.md` gains
the rule they earned: **every data computation carries a quantity whose correct
value is known before the run**, and **the kill condition must name which side it
blames first**. `140`'s did, which is why the diagnosis took one step instead of
a cycle.

The Selberg variance constant is `[RECALL]` — textbook, not read here, and now
load-bearing for the number `0.477`. Worth one arXiv or textbook check before it
is quoted outward.

Build green (3757 jobs), sorries 0, ledger unchanged, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** the fluctuation of the zero count is at half its
limiting size a hundred thousand zeros in, so every statement this project makes
about "the zeros" is a statement about a sequence that has not yet become itself.


# SESSION 141 — the flagged constant, discharged from a published formula

`140` ended by flagging its own load-bearing input: Selberg's variance constant
was `[RECALL]`, textbook, unread, and the number `0.477` rested on it. arXiv is
reachable, so it was owed.

**Kill condition, filed first:** *if the constant is not `1/(2π²)`, the `0.477`
is wrong and `140` gets corrected at its location.* **It did not fire.**

arXiv:2403.19803 (*Lower Bounds for the Large Deviations of Selberg's Central
Limit Theorem*) displays, for `log|ζ(σ+iτ)|`,

> `∫_V^∞ e^{−y²/log log T} / √(π·log log T) dy`

which is exactly the tail of `N(0, ½·log log T)` — matching the general density
`e^{−y²/2σ²}/√(2πσ²)` at `σ² = ½·log log T`. Since `S(t) = (1/π)·arg ζ(½+it)`
and `arg ζ` carries the same variance as `log|ζ|` in Selberg's theorem,
`S` has variance `(1/2π²)·log log T`. **The `π²` I was missing is the `1/π` in
the definition of `S` itself.**

**Scope, stated:** the `½·log log T` for `log|ζ|` is read off a published
formula. That `arg ζ` shares it is still `[RECALL]` — Selberg's theorem covers
both, and I have not read that half. The flag is reduced, not removed.

**And a corroboration I did not expect.** arXiv:2308.09679 gives the rate of
convergence as `(log log log T)²/√(log log T)` unconditionally. At `T ≈ 7.5×10⁴`:
`log log T ≈ 2.4`, `log log log T ≈ 0.88`, so the rate is `≈ 0.77/1.55 ≈ 0.50`.
My observed shortfall — variance `0.477` against `1` — is **the same order as the
published convergence rate**. That is suggestive rather than a match, since the
rate is in Dudley distance and mine is a variance, and I am recording it as
suggestive.

**Two cycles, one number.** `140` measured it and flagged what it rested on;
`141` went and looked. That is the `[RECALL, UNVERIFIED]` discipline working end
to end for the first time — previously the label was where a claim went to sit,
and now it is where a claim goes to wait.

Build green (3757 jobs), sorries 0, ledger unchanged, axioms 2, base hash
`cd7a22e688df` unmoved.

**Might-mean, unhedged:** the factor I got wrong was not in the mathematics but
in the definition — `S` is an argument divided by `π`, and every `π²` in this
subject is that division squared, which is the kind of thing you only stop
mis-remembering by reading the formula.

# SESSION 142 — the empty-row principle outlived its row, in five documents

**Kill condition, stated first** (the wildcard): *sweep every current-state
document for every ledger figure and cross-check against `proportion.go`'s live
output; if the only stale numbers are the `Nsc 0.00%` family already found by
grep, the sweep found nothing new and dies in one run.* **It did not fire** —
see below.

**The cycle opened on a false alarm, and the false alarm was the better find.**
`go run tools/proportion.go` exited 4 with `ESCALATION: audit/Declarations.lean
failed — a claimed name does not exist`. I went looking for the missing name.
There was none: `lake` was not on `PATH` (my omission), the audit had never run,
and the branch reported the **verdict of a check it had been unable to perform**.
`audit/Declarations.lean` compiles clean under `lake env lean` — that
disagreement between two instruments is what made me look.

Fixed at the location: the branch now separates *could not run* (exit **5**,
"harness failure, NOT a verdict on any declaration") from *ran and found a
missing name* (exit 4, unchanged). **Both branches verified with witnesses** —
injecting `#check @Riemann.this_name_does_not_exist_S142` produced exit 4 with
the correct message; an unexported `PATH` produced exit 5. File restored.
Recorded as `S40`: R17's "no witness, no belief" had only ever been pointed at
good news, and an instrument that cannot tell "the check failed" from "the check
found something" manufactures **false bad news**.

**And it had happened before.** `S17`, session **032**, records the same
failure mode — same `PATH`, same exit 4, same empty body. It was classed `process` ("the audit
worked, the operator did not"), which located the fault in the operator and left
the tool untouched, so it recurred verbatim 110 sessions later. Classing an
instrument's misreport as operator error is how a fixable defect buys immunity.
Two register-schema repairs fell out of looking: `S40` had been filed with
`tooling` in the *class* column (a `corrected by` value), and `S34` had been
carrying a comment there since `084`. Both now use the declared vocabulary, and
`forensics/surprises.py` reports three classes over 41 rows.

**The piece.** The absence queue's standing obligation on `LEADS.md` — *"Row
`Nsc` reads `0.00%`"* — is false and has been since `084`. Live ground truth,
from the tool this cycle: `certified[NscStd: 67.25%, Nsc: 50.88%]`, axioms 2,
sorries 0, base `cd7a22e688df`, binding `Riemann.baseline_zeta23` **for both
rows**.

The same expired sentence had propagated into **five** documents. Corrections
placed *above* the stale text in every case (the `S36` rule):

* **`LOOP.md` §"Current state (end of session 004)"** — **this is the root
  cause of the cron prompt's stale STATE line.** The heartbeat reads back
  `ledger NscStd 67.25% / Nsc 0.00%, binding constraint = Fujii's implied
  constant` because those are these two bullets, verbatim, 138 sessions old.
  Retitled a dated snapshot and marked *not current state*.
* **`LOOP.md` §"The empty-row principle"** and **`METHOD.md` §same** — the
  *because* clause survives (no unconditional `(★)` exists at any constant); the
  *reads `0.00%`* does not. The principle now has **no live example** in the
  ledger and is stated on its merits.
* **`README.md`** — a correction existed but sat *below* what it retracted, and
  a dated log block was captioned "the current line". Both fixed.
* **`VERIFYING.md` §5** — found by the wildcard, **not** by grep. This is the
  field-by-field *instruction* for reading a ledger line, and it was teaching off
  a line whose `Nsc` figure expired 58 sessions earlier. Recorded as `S41`: I
  found four sites by searching for the number and the fifth by searching for the
  *role*, and a stale figure inside a worked example is worse than one inside a
  claim, because the reader is being taught to trust the format.

**`LEADS.md` was not a number swap.** Its paragraph argued the ledger
*contingently* realises the visibility split, and named a breakage condition:
"the day OPEN 0 lands, a μ-invariant axiom feeds both rows." **The breakage
happened, by a route not on the list.** `OPEN 0` has not landed and no
μ-invariant axiom feeds either row — `084` opened the row from
`3·NscStd ≤ N + 2·Nsc`, axiom-free, on the *same* two axioms. The diagnosis was
right (a **supply** shortage, not a visibility one); the enumeration of ways to
end it was short by one. That shape — correct contingency, under-imagined
discharge list — is the entry worth keeping.

Every other figure in the sweep checks out against live output: `67.25%`,
`axioms: 2` (cone) against `9` (declared), `sorries: 0`, `C = 1.655`, base hash.

Build green (3757 jobs), sorries 0 (the four `grep` hits are prose —
"sorry-free", "no `sorry`"), ledger `NscStd 67.25% / Nsc 50.88%`, axioms 2, base
hash `cd7a22e688df` unmoved. Absence-queue obligations discharged: 1 of 14.

**The gate on this entry: 4 flagged, 2 real.** *"the only reason I looked"* was
an unfalsifiable claim about my own motive, and *"is the same event"* was the
`S30` identity shape — `S17` and `S40` are two events sharing a failure mode,
which is what I now say. The other two are absence claims I hold witnesses for
(the exit-5 reproduction; the heading's own date), so they ship as written. That
is 2 true positives in 4 on my own prose, in line with the 2026-08-15 triage.

**Might-mean, unhedged:** the cron has been reading me a stale number every
cycle for fifty-eight sessions because a document titled "Current state" was
written once and never re-titled, and the fix was not to correct the number but
to correct the **tense** of the heading.

# SESSION 143 — W19 priced, and the second moment of S was two quantities

**Kill condition, stated first:** *if the mass-3 signal is `o(the S-moment's
main term)`, then no leading-order S-moment identity can bound `hauntedCount/N`
below any constant, and W19-as-a-ledger-route dies — the wall being the
finding.* **It fired — and the manner of firing is the result.**

Queue item 4 is the one item still undischarged (`LOOP.md` line 14 and `S33`
record items 1–3 as done; 5 is a fallback), and its stated blocker
("literature not in the registers") stopped being true when arXiv opened at
`134`. But the register's own genre says price before fetching, so this is
`forensics/w19_price.py`, in the line of `three_moment_lp.py`.

**Why W19 is a real ledger route.** `six_mul_haunted_le_factMoment_three` gives
`6·hauntedCount ≤ Σ H(H−1)(H−2)`, and its docstring records that nothing
certified bounds that moment. A bound feeds `HauntedDensity` and hence
`proportion_of_hauntedDensity`. **`Optimal.moment_route_walled` does not block
it** — that theorem's two witnesses have masses `≤ 2`, so their `factMoment 3`
and `hauntedCount` are both zero; it walls prop1's LP, not this. Corrected at
the location in `Fiber.lean`.

**The perturbation is exact combinatorics, not a model** (`forensics/w19_price.py`). Merging `γ_a < γ_{a+1} < γ_{a+2}`
into a mass-3 atom changes the counting function by exactly `−1` on one gap and
`+1` on the next, nothing outside. So `Δ∫S² = 2[∫S over gap 2 − ∫S over gap 1]
+ (γ_{a+2} − γ_a)`, with no approximation past the quadrature.

**Registered before the run:** the cross term is a difference of `S`-averages
over *adjacent* gaps, so it should cancel and accumulate like a random walk while
the `ΔS²` term accumulates linearly — giving `Δ∫S²/∫S² ≈ 4π²δ/log log T`.
The cross term came in at **0.37%** of the `ΔS²` term, so that half held.

**The verdict: a scale separation, not a yes/no.** The signal `2δL` is
**constant in height**; the main term `L·log log T/2π²` grows. So the ratio
decays as `1/log log T` — the slowest wall in the subject. At `T = 7.5×10⁴` it
stands at `11.2·δ`. Asymptotically no leading-order S-moment identity bounds
`hauntedCount/N` below a constant, because a theorem needs the limit; but the
vanishing is so slow that at every height anyone will compute, mass-3 atoms are
loud in the second moment.

**So W19 converts from a yes/no into a want-ad:** an S-moment identity feeds this
bound **only if** its **error** term is `o(T)` with no `log log` — that is the
direction this cycle establishes, since a larger error swamps the `2δL` signal;
the converse is not claimed and would need the identity in hand — a question about the
*second-order* term of Fujii's expansion, not its main term. That is one specific
error term worth fetching, rather than a survey. Filed on `LEADS`'s W19 row and
as a named cast member on `F2`.

**Not claimed, and the gate would have caught it:** that Selberg's CLT *is* the
moment supply `F2` wants. `F2` wants moments of the **mass** distribution; these
are moments of `S`. They meet only at sub-leading order, and that scale gap is
the wall. Calling them one object is the `S30` shape.

**The prediction missed by 31%, and the miss was the cycle's real find.** I had
divided by the *theoretical* main term. Rescaling by the **measured** `∫S²/L`
gives `11.16` against an observed `11.25` — the perturbation was right all along.
The denominator was not:

    time-average  ∫S²/L                 = 0.17916
    midpoint-sampled mean S²  (140/141) = 0.05644
    difference                          = 0.12271
    predicted sawtooth  E[d³]/12        = 0.12610   (103%)

`140`/`141` sampled `S` at gap **midpoints**; a moment theorem **integrates**.
The two differ by the sawtooth's own contribution: `S` jumps `+1` at each zero
and falls by the normalised gap `d`, so a ramp of drop `d` sits `d²/12` above its
midpoint value, and time-weighting gives `E[d³]/12`. Verified to `3%`, the
residual being the ramp's curvature in `t` versus `θ`. Recorded as `S42`, and
the correction is at the location in `selberg_S.py`: **the `0.477` is a midpoint
statistic and must not be quoted against a moment theorem.**

**And the sawtooth does not fade with height** (`S43`, tabulated in
`forensics/w19_price.py`). It is height-independent at
`0.126`; Selberg's term reaches only `0.215` at `T = 10³⁰`. At the height of
Odlyzko's table the two agree to **0.2%** — a coincidence sitting exactly where
the data is, so anyone checking `∫S²/L ≈ log log T/2π²` here gets confirmation of
a formula that accounts for about half the quantity.

`[RECALL, UNVERIFIED]`, carrying no conclusion: higher-`k` asymptotics
`~c_k·T(log log T)^k` and every error term in Fujii's expansion. The `k = 1`
constant is verified (`141`).

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved.

**The gate on this entry: 4 flagged, 1 real.** *"feeds this bound **iff**"* was
an overclaim — I established that a larger error swamps the signal, i.e. the
`only if` direction; the converse needs the identity in hand. The other three
were witnessed and now cite `forensics/w19_price.py` or `LOOP.md` line 14.
Second clean pass: 0 flagged.

**Might-mean, unhedged:** I spent three cycles saying "the variance of `S`" as
though it named one number, and it named two that differ by a factor of three —
the one I kept computing was not the one the theorems I was reaching for are
about.

# SESSION 144 — the want-ad was filled, by a paper from 1987, in the wrong world

**Kill condition, stated first:** *if the published error term in the `2k`-th
moment formula for `S(t)` is `Ω(T)` — larger than the `2δL` signal a haunted
density produces — then no such identity can see haunted mass at any `δ`, and
W19 dies at the supply rather than at the scale.* **It fired.**

`143` converted W19 into one precise question and committed to one fetch. This
is that fetch, and it is all this cycle did.

**The formulas, read off the displayed equations** — Chirre–Quesada-Herrera,
arXiv:2006.08503 §1.2, not from memory:

| source | condition | error term |
|---|---|---|
| Selberg 1946, their (1.4) | **unconditional** | `O(T·√(log log T))` |
| Selberg, their (1.4) | RH | `O(T)` |
| Goldston 1987, their (1.8) | RH | **`o(T)`** |

The unconditional supply misses: `2δL` against `O(T√(log log T))` is a ratio
`2δ/√(log log T)`, which is below 1 for every fixed `δ` at every height.

**The want-ad is met by (1.8) — and (1.8) is conditional on RH.** RH gives
`Noff = 0`; `Noff = 0` gives `NoHaunted` by `Fiber.noHaunted_of_Noff_zero`,
axiom-free and already in this repo. So `hauntedCount = 0` identically in
**every** world where the identity precise enough to bound it exists — an
implication only, since `Fiber.noHaunted_not_imp_Noff_zero` puts `NoHaunted` in
strictly more worlds than RH. **The
want-ad is filled only where the goods are worthless.**

**`S44`, and it is the honest shape of the miss.** I expected the object not to
exist — the register's habit is that the needed thing is missing. It exists and
is 39 years old. The route dies for a reason I had not considered: I priced the
*precision* of the supply across two cycles and never once asked what its
*hypothesis* does to the target.

**What the death is worth.** Not "the moments are too weak" but a **located
margin**: the entire distance between a live route and a dead one is the
`√(log log T)` separating Selberg's unconditional error from Goldston's
conditional one. That also explains why `143`'s numerics looked so encouraging
at `11.2·δ` — the signal really is loud at `T ≈ 7.5×10⁴`, and the error bars are
louder. Filed in `FAILURES.md`; `LEADS`'s W19 row closed; `F2` converted to a
rung per the F-protocol, its cast member found and found already employed, which
is the iron law's own prediction.

**A shared input, recorded and not overread.** (1.8)'s second-order constant is
built from `∫₁^∞ F(α)/α² dα` — the pair-correlation form factor on `[1,∞)`,
which is the corridor `PRICES.md` prices and `LEADS`:623 calls "certified bare"
past `A`. The S-moment route and the corridor route consume the **same**
unavailable input. That is a shared dependency, **not** an identity of routes;
calling them one object is the `S30` shape and the gate would flag it.

*Scope, stated: only `k = 1` was fetched. Higher-`k` asymptotics and their error
terms remain `[RECALL, UNVERIFIED]` and carry no part of this verdict.*

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved.

**The gate on this entry: 4 flagged, 3 real, and one was load-bearing.** I had
written that RH-conditionality zeroes the target *"in exactly the world where"*
the identity exists — but `Fiber.noHaunted_not_imp_Noff_zero`, already in this
repo, puts `NoHaunted` in strictly **more** worlds than RH. The claim is an
implication, not a coincidence of worlds, and it now says so in both places it
appears. Two `assert`-guarded replacements refused on line-wrapping before
writing anything, which is the `S127` repair doing its job.

**Might-mean, unhedged:** a hypothesis is not just a price you pay for an
input — it also moves the thing you were trying to measure, and I spent two
cycles pricing the sharpness of an instrument without checking whether its
assumption zeroes the quantity it points at.

# SESSION 145 — the guard that would have said it, and the paragraph that already did

**Kill condition, stated first:** *if a vacuity rule cannot be made to fire on
both `S3` and `S44` without also firing on conditional inputs that are
legitimately useful, it has no discriminating power and is not added — `S39` is
the precedent for reporting that honestly.* **It half-fired, and the half is
reported rather than papered over.**

**The piece.** `144` died of a shape Rules 1–3 of `provenance_lint.py` cannot
see. They ask whether an input is CIRCULAR, out of SCALE, or too weak in
QUALITY. None asks the question `144` turned on: **does the hypothesis this
input carries trivialise the very quantity it would bound?** An input can be
impeccable on all three axes and still be worthless, because its own condition
empties the target.

**Rule 4 (VACUITY)** keys on a target's *vacuity depth* — the hypothesis depth at
which it goes empty — and flags whenever `depth(input) ≥ vacuity_depth(target)`.
`hauntedCount` has depth 1, witnessed by `Fiber.noHaunted_of_Noff_zero`.

**Calibration, 4/4, with the negative controls doing real work:**

| case | input | target | verdict |
|---|---|---|---|
| S44 / W19 | `Goldston_1987_RH` | `hauntedCount` | **FLAG** |
| S44 / W19 | `Selberg_1946` | `hauntedCount` | clean (precision fails, not vacuity) |
| negctl | `Goldston_1987_RH` | `N*_bound` | clean |
| negctl | `CGdL_68_45` | `NscStd` | clean |

The rule is **live, not a museum piece**: in `forensics/provenance_lint.py`,
`lint()` takes a `target` argument (defaulting to `N*_bound`, so every pre-`145`
caller keeps its meaning — checked by diffing the tool's output across the
change: all nine pre-existing verdict lines are identical and the only added
verdicts are the new W19 block; T3(b) still answers 3/11. **Not** byte-identical
output, and I had written that it was before checking: the header line now also
prints the target),
and the W19 chain now returns `BLOCKED` with the reason named. T3(b) still
answers **3/11** — the standing kill condition on guard generalisation.

**Scope, and it is the `S39` discipline: the rule catches one of two species.**
*Target-zero* — the hypothesis makes the quantity identically zero (`S44`) —
is caught. *Threshold-unreachable* — the hypothesis makes the required threshold
impossible while the quantity stays live (`S3`, session 026) — is **not** (`forensics/provenance_lint.py`, and the calibration block says so in
the file): it needs per-route threshold data this table does not carry. Inventing that data to
make the calibration read 5/5 is precisely what `S39` refused to do. So the
honest score against the purchasing surprises is **1 of 2**.

**And the sharper finding, which is not about the guard.** `LEADS.md` line 1787
says, in c.ai's words: *"haunting only exists in the unconditional world. Under
RH it is vacuous."* That sentence was on disk while `143` wrote the want-ad and
`144` spent a fetch confirming it. This is the `S27` shape — check the registers
before reconstructing — applied not to a computation but to a **verdict**.
Recorded as `S45`, and corrected at the location.

The repair is deliberately mechanical rather than resolutional. I do not get to
promise to re-read line 1787; the guard now refuses the chain.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved. All 15 guards green.

**Might-mean, unhedged:** the register had already answered the question two
cycles before I asked it, which means the project's failure mode has quietly
moved from not knowing things to not finding the things it knows.

# SESSION 146 — two settle-rules that masked each other, and a twelve-session escalation

**Kill condition, stated first, and narrowed before running.** As first drafted
it read "if no absence claim is already answered on disk, `S27`/`S33`/`S45` were
a coincidence and there is no retrieval debt." That is the `S37` quantifier
drift, in a kill condition: this pass touches **one** surface, and those three
surprises span three. Narrowed before use to: *if the pass finds no absence
claim already answered elsewhere in the registers, there is no retrieval debt
**on this surface***. **It did not fire.**

**Wildcard, kill condition first:** *measure `absence_queue`'s own precision;
if fewer than half of its 13 are genuine absence claims, its counts cannot be
quoted until it gains the filters `claims_gate` already has.* **It fired.**

## The piece: an escalation that had been answered for twelve sessions

`LEADS.md` still carried **"Odlyzko's tables and LMFDB are unreachable"** under
`⚠️ ESCALATION`, asking Joop to widen the allowlist or drop the tables in the
repo. Joop widened it at `134`. `data/zeros1` holds 100 000 ordinates and
sessions `138`–`143` every one of them ran on it. The ask was answered; the
escalation stood.

**Why the queue never listed it — and this is the cycle's actual finding.** Two
independent settle-rules each hid it, and **neither fix alone surfaces it**
(measured, not argued: 13 → 13, 13 → 14, 13 → 15 over
`forensics/absence_queue.py`):

1. `⚠️` was in `SETTLED`. But `⚠️` marks **escalations** as well as corrections,
   so a claim announcing itself as an *open problem* read as one already closed.
2. The "next paragraph counts as the settlement" rule matched
   `## The slow-convergence recall, tested (SESSION 139)` — the following
   **heading**, about something else entirely.

I tested fix 1 alone: 13 → 13, no change. I tested fix 2 alone: 13 → 14, and the
Odlyzko claim was still not among them. Only together: 13 → 15, and it appears.
**Two defects, each individually invisible because the other was also firing.**
My first hypothesis (the `⚠️` overloading) was right about the mechanism and
wrong that it was sufficient, and one command showed that rather than an
argument.

Both repaired in `forensics/absence_queue.py`: a settlement must cite a session
— a warning sign is not a date — and a following heading is not a correction.
**Adjacency is not aboutness.**

## Two more corrections the pass turned up, both at location

* **`LEADS`'s copy of the `factMoment 3` note** still said
  `Optimal.moment_route_walled` walls that bound. `144` established it does not
  — its witnesses have masses `≤ 2`, so their `factMoment 3` and `hauntedCount`
  are both zero — and corrected `Fiber.lean`. The `LEADS` copy was not touched.
  The `142` shape exactly: one sentence, two documents, fixed in one.
* **`CLAIMS.md`'s Selberg row** quoted variance `0.443 → 0.496` with no caveat.
  `143` established those are a **midpoint** statistic against a time-average of
  `0.179`, differing by the sawtooth's `E[d³]/12`. `selberg_S.py` was corrected
  at `143`; `CLAIMS` was not. Same shape again.

## The wildcard: the queue's precision, measured

Of the 13, **7 are not absence claims at all** — a directive (*"Never as a
bound"*), a past-tense record of an action since done, a **quoted** sentence
being retracted, a rhetorical question, a schema description, and two ordinary
statements. Six are genuine, of which one (**"the GRH tier is empty"**) already
carries a standing mechanical witness: `provenance_lint` prints `tier GRH: 0/11`
on every run.

**FP rate 7/13 = 54%**, so the kill condition fires: **`absence_queue`'s counts
must not be quoted as a defect rate** until it gains the `DIRECTIVE` and quote
filters `claims_gate` has carried since its own triage. I have deliberately
**not** added them this cycle — `S39`'s lesson is that a filter designed during
the measurement it is meant to inform is a filter fitted to its own test set.
Filed as the next cheap instrument task.

Count is now **15**, up from 13: two newly visible, three corrected, and the
number went up. That is the right direction for a queue whose failure mode is
invisibility.

R20: this is hygiene cycle **2** of 3 (`145` was tooling, `143`/`144` were not).

Build green (3757 jobs), sorries 0, all 15 guards green, ledger
`NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** the instrument that exists to make absent things
visible was itself hiding one, and it hid it with two independent rules that each
looked reasonable and were only harmless because the other one was also wrong.

# SESSION 147 — the +9.29 route becomes a theorem, and the price was understated

**Kill condition, stated first:** *if the chain needs anything beyond the two
named hypotheses plus what is already certified, say so and leave the route open
— do not add hypotheses until it closes.* **It did not fire:** the chain closes
on exactly `zeta23_xiPrime`, `OffTransfer`, `NzComparable` and the existing
`certified_std`.

**What was missing.** `Gaps.offLineImport_of_derivative` is general and
`Assumptions.zeta23_xiPrime` supplies `κ' = 0.85838`, but the two had **never
been composed at the ζ level**. The largest single movement on the board — the
one `PRICES.md` has carried since `087` — existed only as arithmetic inside a
docstring. Two theorems now close it:

* `offline_via_xiPrime` — `OffLineImport zetaFamily 0.14162` (`1 − 0.85838`);
* `certified_nsc_via_xiPrime` — `Proportion 0.60169` (`0.6725 − 0.14162/2`),
  i.e. **`+9.294` points** over the unconditional `0.50875`.

Both built first try. **The ledger does not move and must not**: `metric.json`
points no row here, and `proportion.go` still reports `Nsc 50.88%` at `axioms: 2`.

**And the price was understated — `S48`.** I wrote *"it costs exactly the two
hypotheses named in the signature"* into the new docstring, then ran
`#print axioms` because R17 says verify a cone rather than read it off a
statement. It returns **four** project axioms:

    certified_nsc_via_xiPrime : baseline_zeta23, xiPrimeFamily,
                                zeta23_xiPrime, zetaNonempty
    certified_nsc_unconditional : baseline_zeta23, zetaNonempty

So Route II costs *two hypotheses **and** two extra axioms*, and adopting it
would move the ledger's `axioms:` field from **2 to 4**. Every entry in
`PRICES.md` that prices this route as "two `Prop`s" is pricing half of it —
corrected at the location of the `9.29` figure. The docstring was fixed before
committing rather than shipped and retracted.

**What this changes about the parked ruling, and it is why the cycle was worth
spending.** The ruling was *"may `OffTransfer` and `NzComparable` be assumed?"*
It is now two separable questions: the **derivation** is done and needs no
further decision, and the **doctrine** question is strictly larger than recorded
— it is a proposal to double the trusted base for 9.29 points. Joop, that is the
form I would like the ruling in.

R20: this is a substantive cycle, so the hygiene run (`146` at 2 of 3) resets.

Build green (3757 jobs), sorries 0 (the four `grep` hits are prose), ledger
`NscStd 67.25% / Nsc 50.88%`, axioms 2, base hash `cd7a22e688df` unmoved. Both
new names added to `audit/Declarations.lean`. Guards: **14 green**, plus
`claims_gate` run against files rather than stdin — see below.

**A green light that was not green — `S49`.** Running the guard sweep this cycle
hung, because `claims_gate.py` with no file arguments lints **stdin**. In a sweep
loop stdin is empty, so it printed `0 flagged` and exited `0` **having scanned
nothing**. So `145`'s and `146`'s "all 15 guards green" were fourteen real passes
and one no-op wearing a green light. Those entries are dated records and stand as
written; the correction is here, and the sweep now names a file. `CLAIMS.md`
actually carries **5** flags, and the Route II row added this cycle is not among
them.

R17 says no witness, no belief, including about live state. A guard that cannot
fail is not a witness, and I had been counting one for at least two cycles.

**Might-mean, unhedged:** a route's price is not what its statement asks for but
what its proof reaches for, and those differed here by a factor of two in the
currency the ledger reports on every line.

# SESSION 148 — the guards audited for whether they can fail, and nine cannot

**Kill condition, stated first:** *if every script in `forensics/` can be made to
fail by injecting a fault into what it checks, then `S49` was isolated, the guard
sweep is a real witness, and this dies having confirmed it.* **It fired, hard.**

`147` found one guard that could not fail. The obvious question was whether it
was alone. It is not.

## The audit

| class | scripts |
|---|---|
| **can fail on a substantive verdict** | `claims_gate`, `window_opt`, `surprises`, `scope_gate`, and `provenance_lint` **only as of this cycle** |
| fail only on a **self-check** (their own arithmetic's sanity, not a verdict) | `selberg_S`, `w19_price` |
| **cannot return a failing exit code at all** | `provenance_lint` (before today), `lemma1_guard`, `quarry`, `three_moment_lp`, `w16_price`, `calibration`, `function_field`, `gap_scaling`, `near_haunting`, `absence_queue` |

**Nine of sixteen cannot fail.** Most of those are *analyses* — pricing and
measurement scripts — and calling them "guards" in a sweep was my error, not
theirs; `absence_queue` is documented as always-`0` by design. But one is not an
analysis.

## The flagship printed BLOCKED five times and exited 0

`provenance_lint` is the contamination detector, the file carrying Rules 1–4 and
the `#27` gate. `lint()` computes `ok`, prints **"BLOCKED — do not build the
table"**, and the entry point **discarded the value**. Every run printed BLOCKED
five times and exited `0`. I added Rule 4 to that file in `145` and reported it
green in two sessions. `S50`.

**The fix is not "exit 1 whenever something blocks"** — those replays are
historical and are *supposed* to block. The check is that each replay still
returns **the verdict the record says it returned**, so a replay that silently
starts passing is caught. A **control** that must PASS is included: without one,
"everything blocks" would itself satisfy the self-test, and the guard would be
vacuous a second way.

**Verified by fault injection, in both directions — 3/3 caught:** defeating
Rule 3 (MRT supplies `power`), defeating Rule 4 (`hauntedCount` no longer
RH-vacuous), and breaking the control (a PASS that starts blocking). `window_opt`
and `surprises` were injected too — a perturbed register digit and an unparseable
table — both exit `1` and both restored byte-identical.

## `S51` — the first fault injection failed to trip it, and the guard was right

I widened `CMR_1.3208`'s validity range expecting the scale rule to stop firing.
The replay blocked anyway: that chain's ancestry hits `EP1`, so Rule 1 catches it
on circularity regardless of scale. **A negative result from a fault injection is
ambiguous** between "the guard is vacuous" and "the fault was insufficient", and
only re-testing separates them. Had I stopped at the first negative I would have
recorded the repaired guard as still broken.

R20: hygiene cycle 1 of 3 (`147` was substantive).

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved.

**Might-mean, unhedged:** I have been reading exit codes as verdicts for the
whole project, and for nine of sixteen scripts the exit code was a statement that
the interpreter reached the end of the file.

# SESSION 149 — the queue's own staleness, and a flag that was hiding a second flag

**Kill condition, stated first:** *if fewer than 2 of `CLAIMS.md`'s 5 flags are
true positives, the gate's precision on this register is below the 50% it showed
on 2026-08-15, and its flag count should stop driving cycles.* **It fired: 1 of
5 on the first pass, 2 of 6 once the masked trigger surfaced — 33%.**

## The triage

| # | flag | verdict |
|---|---|---|
| 1 | "Two were found living as prose in three cycles (`FAILURES.md` #10, `Gauge.lean`)" | **FP** — a record of a past finding, with citations; not a completeness claim |
| 2 | "**Nothing false was written**; it was badly ordered" | **TRUE** — a negative-completeness claim about our own record, unwitnessed. Exactly `S27`'s shape, which is what the gate was built for |
| 3 | "`S34`'s defect … lived on a surface the instrument had not been pointed at" | **FP** — historical, cites `S34`/`S35` |
| 4 | "1 true positive in 14 — but it is the one being hunted" | **FP** — a measured statistic with its witness in `S35` |
| 5 | "The route table had never been triaged" | **FP** — past tense, and the next line reports the triage |

`#2` corrected at location: **"no false statement was *found* in it"** — a search
result, not a property of the text. That is what the triage actually witnessed.

## `S52` — the fix did not move the count, and that was the finding

I expected 5 → 4. It stayed at **5**. The sentence carried *two* triggers — the
negative-completeness claim **and** an identity claim ("is the same hazard by a
different route") — and the gate reports the first match per sentence, so
repairing one **exposed** the other. Downgraded as well (comparable, not
identical: no false quotation from that register has been recorded, whereas a
false sentence would be one). Now **4**.

This is `S47`'s masking shape on a different instrument. **A count that does not
move after a real fix is evidence of a second defect, not of a failed fix** — and
my first instinct was to check whether my edit had applied.

## The piece: `LOOP.md`'s banner had gone stale about staleness

The `⚠️ READ FIRST` block is the disk's defence against the cron's fixed text.
It was stamped `SESSION 102`, **said "wrong in three ways" above four rows**, and
had stayed that way for forty-seven cycles. Refreshed, and it no longer asserts a
total — it lets the table count itself. Three rows added:

* **queue item 4** — W19 is dead (`144`), and the empty GRH tier has a standing
  mechanical witness (`provenance_lint` prints `tier GRH: 0/11`);
* **queue item 5** — "re-run all guards" proves less than it looks, since `148`
  found 9 of 16 scripts cannot return a failing exit code;
* **`RECENT`'s profile clause** — pointed at the row that already settles it.

## A drift worth raising, Joop

**Six of the last seven cycles have been instrument work** (`143` measurement,
`145`–`146`, `148`–`149` tooling and hygiene; `144` literature; only `147` added
theorems). Each found a real defect, so none was idle — but R20 caps *consecutive
hygiene* and these kept qualifying as substantive by finding things. The ledger
has not moved since `084`, and `111`/`112` prove it cannot move from the baseline
alone. **The routes I can currently name that would move it are the ones parked
with you** (`certified_nsc_via_xiPrime`'s two hypotheses; `baseline_przz`) — I am
not claiming no other route exists, only that the registers list none. So the
instrument work is partly what a blocked project does with its hands. That is my
read, offered as a ruling rather than acted on.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved. R20: hygiene 2 of 3.

**Might-mean, unhedged:** the register that records what the project got wrong is
now the fastest-growing thing in it, and that is either the apparatus working or
the apparatus becoming the work.

# SESSION 150 — two routes on the board, and the cheaper one costs no axioms

**Kill condition, stated first:** *if the survey finds any route in the registers
that would move the `Nsc` row and has never been priced, then `149`'s "the
registers list none" was wrong, the project is not blocked on Joop, and the
escalation weakens.* **It did not fire as stated** — no *unpriced* route exists.
What the survey found instead is a comparison nobody had made, and it changes the
parked ruling.

`149` said six of seven cycles had been instrument work and asked for a ruling.
Another instrument cycle would have confirmed the drift rather than tested it, so
this cycle tested `149`'s own load-bearing sentence.

## The `m = 5` rung was priced at `8.2` points and had never been stated

`PRICES.md` has carried it since `105`. `Gaps.proportion_of_noSmallHaunted` is
general; nothing instantiated it at ζ. **The same gap `147` found for Route II**
(`certified_nsc_via_xiPrime`), in the adjacent paragraph of the same register.

`certified_nsc_via_noSmallHaunted : NoSmallHaunted zetaFamily 5 →
zetaFamily.toCounts.Proportion 0.590625`, from `(5·0.6725 − 1)/4`. Built first
try.

## The comparison, in the currency `R5` says to count

| route | gain | hypotheses | **axiom cone** |
|---|---|---|---|
| ξ′ (`certified_nsc_via_xiPrime`) | **+9.294** | `OffTransfer`, `NzComparable` — analytic, Conrey 1983, unread | **4** |
| `m = 5` (`certified_nsc_via_noSmallHaunted`) | **+8.188** | `NoSmallHaunted zetaFamily 5` — combinatorial, about ζ's own zeros | **2 — no increase** |

Both cones verified with `#print axioms`, not read off the statements — the
`S48` lesson from three cycles ago, applied on purpose this time.

**The cheaper route costs `1.106` points and buys back two axioms.** `PRICES.md`
called the ξ′ route "the one live item" and "the cheapest nine points on the
board". In points that is right. In `R5`'s garbage-height currency — *every axiom
raises the stack without being clearable* — it is the **dearer** of the two.
Corrected at the location of both phrases.

## What this does to the ruling, Joop

`147` handed you a question sized as *"double the trusted base for 9.29 points."*
That was the only option on the table because the alternative was not a theorem:
`Riemann.certified_nsc_via_noSmallHaunted` did not exist until this cycle.
It is now, and the question is better posed as a choice:

* **ξ′** — `+9.294`, two analytic hypotheses from a 1983 paper nobody here has
  read, and the ledger's `axioms:` field goes `2 → 4`;
* **`m = 5`** — `+8.188`, one combinatorial hypothesis about ζ's own zeros, and
  the `axioms:` field **does not move**.

I am not recommending either; both hypotheses are unproved and neither is
asserted. But `R5` exists precisely to make the second look better than it did,
and `PRICES.md` carried no comparison of the two: its route table listed the ξ′
row as "the one live item", which is the sentence corrected above.

`S53`: I wrote `149`'s "the registers list none" myself, one cycle ago, and it
was half right in the half that mattered.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved — the ledger must not move on a conditional
theorem, and `metric.json` points no row at either. Name added to
`audit/Declarations.lean`.

**Might-mean, unhedged:** I spent a cycle telling Joop the project was blocked,
and the thing that unblocked the question was reading my own register instead of
repeating my own sentence.

# SESSION 151 — the ladder stated whole, and the trade-off I reported was not one

**Kill condition, stated first:** *if every remaining priced route in the
registers is already a theorem at the ζ level, the `147`/`150` pattern was
confined to those two and this dies having confirmed the gap is closed.* **It did
not fire.** `PRICES.md`'s ladder table lists `m = 3, 5, 7, →∞`; `150` stated
`m = 5` and left `m = 7` unstated.

## The piece: state the ladder, not a rung

`certified_nsc_ladder {m} (hm : 2 ≤ m) (hh : NoSmallHaunted zetaFamily m) :
Proportion ((m·0.6725 − 1)/(m − 1))` — one line, every rung at once, cone **2**
axioms. Then `certified_nsc_via_noSmallHaunted_seven : Proportion 0.6179166`.

Stating it generally is what made the next rung unavoidable. Had `150` done that
instead of instantiating the rung the register named, the correction below would
not have been needed.

## `S54` — the trade-off I reported to Joop does not exist

`150` gave you a choice: `+9.294` at four axioms, or `+8.188` at two. Both cones
verified, the arithmetic right, the framing wrong. The ladder's **`m = 7`** rung:

| route | gain | axiom cone |
|---|---|---|
| ξ′ | `+9.294` | 4 |
| `m = 5` | `+8.188` | 2 |
| **`m = 7`** | **`+10.917`** | **2** |

**ξ′ is dominated in both currencies** — more proportion at fewer axioms. On the
two axes `certified_nsc_via_noSmallHaunted_seven` lets me compare (points and
cone size) it loses both; where it can still win is **hypothesis strength**, and
that is the axis a ruling should turn on.

The rung was one row below the one I quoted, in the same table. I inherited the
register's phrase *"the `m = 5` rung is the cheap one"* — true, it is the
cheapest *hypothesis* — and read it as "the best rung", then priced against it
for two cycles. `S53` was about not reading my own register; I did it again
inside the fix for `S53`.

## What the ruling actually is, Joop — third revision, and this one is honest

Not "9.29 points for two axioms". Not "9.29 at four versus 8.19 at two". It is:

> **How strong a hypothesis about ζ's own zeros are you willing to carry?**

Every rung costs the same two axioms already in the base. The dial:

* `m = 5` — no haunted ordinate of mass exactly `3` → `+8.188`
* `m = 7` — none of mass `3` or `5` → `+10.917`
* `m → ∞` — no haunted ordinate at all → `+16.375`, the whole baseline

ξ′ is a *different* kind of ask — two analytic hypotheses from an unread 1983
paper, plus two axioms — and it now buys less than `m = 7`. **Nothing is
asserted; all of these are conditional and the ledger stays at `50.88%`.** What
changed across `147`, `150` and `151` is only that the options are theorems and
can be compared.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved. Both names added to
`audit/Declarations.lean`.

**Might-mean, unhedged:** three cycles running I have priced a route against the
rung a register sentence happened to name, and the fix each time was to state the
general theorem and let the parameter show me what I had not looked at.

# SESSION 152 — the second ladder runs backwards, and the menu is complete

**Kill condition, stated first:** *if every parameterised route in
`Proportion.lean` is already stated in general form at the ζ level, the
`150`/`151` pattern was confined to the haunted ladder and this dies.* **It did
not fire.** `starBound_of_mult_le` is parameterised in `M`; this file stated it
at `M = 2` and `M = 3` and never generally.

## The piece: ask the second ladder `151`'s question

`151`'s lesson was to state the general theorem and let the parameter show what I
had not looked at. The multiplicity hypothesis is the obvious next candidate — a
second dial, apparently parallel. Three theorems, all built first try:

* `proportion_of_mult_le_zeta` — every rung at once, cone **2** axioms;
* `mult_ladder_value` — the identity `2 − (M − (M−1)κ) = (M−1)(κ−1) + 1`;
* `mult_ladder_no_gain` — for `M ≥ 3` the rung returns **less** than `0.50875`.
  **Axiom-free** (only `propext`, `Classical.choice`, `Quot.sound`).

## `S55` — it is not a dial, it is a single point, and it runs the other way

`(M−1)(κ−1) + 1` is **strictly decreasing in `M`** whenever `κ < 1`. It equals
`κ` at `M = 2` and loses from there. So where the haunted ladder climbs
(`+8.188 → +10.917 → +16.375`), the multiplicity ladder peaks immediately. That
is why nobody had stated the general form — **there was nothing up there**, and
the `M = 3` statement earns its place through its *star bound*, not through any
proportion it returns.

**And the one live rung is dominated as well.** `H ≤ 2 ⟹ NoHaunted`
(`Blindness.noHaunted_of_mult_le_two`); `NoHaunted` is *strictly* weaker
(`noHaunted_not_mult_le_two`); both return `0.6725`. So `noHaunted_of_mult_le_two` and
`noHaunted_not_mult_le_two` together make this a strictly stronger hypothesis
buying the same number — dominated on the mathematics, not on taste.

## The menu, complete — and this is the last revision I expect to need

| route | gain | axioms | hypothesis |
|---|---|---|---|
| `m = 5` haunted rung | `+8.188` | 2 | no haunted ordinate of mass `3` |
| ξ′ | `+9.294` | **4** | two analytic `Prop`s, Conrey 1983, unread |
| `m = 7` haunted rung | `+10.917` | 2 | none of mass `3` or `5` |
| **`NoHaunted`** (`m → ∞`) | **`+16.375`** | 2 | no haunted ordinate at all |
| `H ≤ 2` | `+16.375` | 2 | strictly stronger than `NoHaunted`, same payout — **dominated** |

Joop: the ruling is one question — **how strong a hypothesis about ζ's own zeros
will you carry?** — and the answer picks a row. Two rows can be struck
immediately on the mathematics rather than on taste: `H ≤ 2` is dominated by
`NoHaunted`, and ξ′ is dominated by `m = 7` in both points and axioms. What
remains is a genuine dial with a genuine cost, and nothing on it is asserted.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved. Three names added to
`audit/Declarations.lean`.

**Might-mean, unhedged:** two ladders that looked alike from their statements
turned out to run in opposite directions, and what showed me was writing down the
parameter and reading the sign.

# SESSION 153 — the menu audited in exact rationals, and it holds

**Kill condition, stated first:** *if all five menu numbers reproduce exactly
from the theorem statements, the menu is arithmetically sound, this dies in one
run, and the three corrections across `150`–`152` were about framing rather than
arithmetic.* **It fired.**

`152` called the menu final. So did `151`, and `150` before it — each cycle
corrected the previous one's comparison. Rather than extend the menu a fourth
time, this cycle checked the numbers I had been quoting.

**In exact rationals, no floating point:**

| route | proportion | gain | quoted |
|---|---|---|---|
| `m = 5` | `0.5906250` | `8.1875` | 8.188 ✅ |
| ξ′ | `0.6016900` | `9.2940` | 9.294 ✅ |
| `m = 7` | `0.6179167` | `10.9167` | 10.917 ✅ |
| `NoHaunted` / `H ≤ 2` | `0.6725000` | `16.3750` | 16.375 ✅ |

The supporting identities too: `(3κ−1)/2 = 0.50875` reproduces the certified row,
`1 − κ = 0.3275` reproduces `certified_offline`, and `κ − 0.3275/2 = 0.50875`
closes the off-line route back onto the same number. Both ordering claims hold —
`m = 7` above ξ′, `m = 5` below it.

**So the three corrections were framing, never arithmetic.** `150` compared the
right numbers against the wrong rung; `151` fixed the rung; `152` found the second
ladder ran backwards. At no point was a figure wrong — which is worth knowing,
because it says the failure mode across those cycles was *which* number I chose
to compare, not the number.

**One precision detail, recorded at its location.** The exact `m = 7` ladder
value is `7415/12000`, a repeating decimal; `certified_nsc_via_noSmallHaunted_seven`
asserts the terminating `0.6179166`, which is `1/1500000` **below** it. The
theorem is deliberately, very slightly weaker than the ladder so its statement
carries a readable numeral. Noted in the docstring; anything needing the exact
value should use `certified_nsc_ladder` directly.

A short cycle, and the heartbeat allows one: the audit passed and there was
nothing further to do with it.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved. The ruling from `152` stands unchanged and
is now arithmetically witnessed.

**The gate on this entry: 4 flagged, 4 false positives, and they are all one
shape.** Every flag is the *numeric-precision* sense of "exact" — "in exact
rationals", "the exact value", "the exact `m = 7` ladder value is `7415/12000`" —
not the completeness sense the gate was built to hunt (`S26`/`S27`: a claim that
nothing more is needed). This is the first homogeneous FP class the gate has
produced, and it is mechanically distinguishable: "exact" adjacent to a numeral,
a fraction, or "rationals" is arithmetic, not a residue claim.

**Deliberately not patched this cycle.** `S39` is the standing lesson: a filter
designed during the measurement it is meant to inform is fitted to its own test
set. Filed as the next cheap instrument task, alongside `146`'s `DIRECTIVE` and
quote filters for `absence_queue`, which are still outstanding for the same
reason. The four sentences ship as written; the gate is advisory and the triage
is the record.

**Might-mean, unhedged:** three cycles of correcting myself and not one of them
was a wrong number, which means the register's arithmetic has been sound the
whole time and my reading of it has been the moving part.

# SESSION 154 — the queue was reading corrections from the wrong side

**Kill condition, stated first:** *if either deferred filter changes a verdict
that the recorded triages classified as a TRUE positive, it is over-fitted and
reverts — these filters may only remove false positives already identified in
earlier cycles.* **It did not fire.** Every verdict that changed was an FP
recorded in `146` or `153`.

`153` deferred two filters under `S39`'s rule — a filter must not be designed
during the measurement that informs it. Both triages are now in prior cycles, so
the objection is discharged and this cycle is the one to build them.

## Filter 1 — `claims_gate`'s two senses of "exact"

`ARITHMETIC_EXACT`: the word is exempted only when it sits against arithmetic
vocabulary or a numeral. Calibration **6/6** — `S26`'s "the exact residue,
nothing else at all", `S27`'s negative form and a completeness claim all still
flag; `153`'s three arithmetic uses clear.

**Corpus impact: zero.** No register count moved (`CLAIMS 4`, `LEADS 64`,
`ISSUES 38`, `FAILURES 18`, `E 14`, `PRICES 15`, all unchanged). The phrasing
occurs in session entries, not in the registers, so this prevents future noise
rather than clearing present flags — worth saying plainly, since a filter with no
live yield is easy to report as an improvement.

**`S58` — and it corrected `153` on the way.** I wrote that `153`'s four flags
were "all one shape". The filter clears exactly **three**; the fourth flags on
`never`, a different pattern. I had classified an FP class by reading four
sentences and generalising, and the instrument built from that classification is
what disproved it.

## Filter 2 — and it turned up something much worse

The `DIRECTIVE` and quote filters went in as `146` specified: `13 → 12`, one
directive removed. Only the two *mechanical* shapes are handled; `146`'s other
false positives are not mechanically separable, so this **reduces** the FP rate
without eliminating it, and the count still must not be quoted as a defect rate.

Then the discharged Odlyzko escalation was still listed. `146` closed it with a
✅ block placed **above** the claim, exactly as the standing rule requires, and
`forensics/absence_queue.py` did not register it — the claim kept listing for
eight cycles.

**`S57`.** `absence_queue`'s docstring justified reading the *next* paragraph
with: *"corrections in this project are written below the text they correct (the
standing rule)"*. The standing rule is the **opposite** — `CLAIMS.md` line 247
and `NIGHT.md` line 157: *a retraction must appear above what it retracts*, added
after `S25` found a banner sitting below the numbers it retracted. So the queue
was blind to every correctly-placed correction and settled only on rule-violating
ones: **an instrument rewarding the violation it exists downstream of.**

Fixed — both neighbours now count, with `146`'s heading exclusion applied to
each. `12 → 10`, and I checked *which* two rather than the count: the Odlyzko
discharge, and a claim whose previous paragraph is a `SESSION 124` correction of
that same enumeration. Both legitimate.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved. Guards green, including
`provenance_lint`'s replay self-test.

**Might-mean, unhedged:** the queue had a written justification for doing the
wrong thing, and that justification is why I stopped looking — I had read the
docstring several times without once checking its factual claim against the rule
it cited.

# SESSION 155 — a calibration nobody re-ran, and a check I wrote that never ran

**Kill condition, stated first:** *if no other `forensics/` docstring asserts a
project rule that the owning register contradicts, `S57` was isolated and this
dies in one pass.* **It fired**, though not on a rule — on a claim about an
instrument's own calibration.

`154` found `absence_queue` justifying the wrong behaviour in prose. The obvious
question was whether that docstring was alone. I swept every instrument for
assertions about rules or about other instruments' behaviour. `quarry`'s claims
about `provenance_lint`'s Rule 1 check out against the node table (`CMR_1.3208`
circular via `EP1`, scale-valid only on `[3.0, 9.9]`; `GGOS_floor` on
`[1.0, 1.5]`). `claims_gate`'s citation of `window_opt.py` resolving `#29` holds.

## `S59` — "Calibration: it flags all four of the above, 4/4"

That is `absence_queue`'s docstring, and it is a sentence about a run in `133`.
**Nothing re-ran it.** All four claims have since been corrected in the
registers, so `forensics/absence_queue.py` flags none of them today and the line
cannot be reproduced from the corpus — a green light with no witness, which is `148`'s class applied to a
*calibration claim* rather than an exit code.

The sharp part: **`154` changed the settle logic in that very file**, and nothing
existed that would have told me if the change had blinded the instrument to the
four shapes it was built for. I shipped that edit with no regression check and
did not notice for a cycle.

Fixed: the four claims are now **embedded as sentences** with two negative
controls, corpus-independent, and run on every invocation. **6/6.** The script
now exits `1` if its calibration breaks — which also moves it out of `148`'s
"cannot fail" list, while the queue itself stays a work list rather than an alarm.

## `S60` — and the check I added last cycle was never called

`154` added `claims_gate.calibrate()`. I tested it by hand and left it with no
call site in `forensics/claims_gate.py`. A check that exists and does not run — precisely the class `148`
audited, committed by me in the cycle *after* writing that audit. It runs first
now and returns `2` on failure, so a gate whose own test set misbehaves stops
rather than grades.

## Fault injection, and what each calibration actually tests

`absence_queue`: removing the patterns behind one case trips it (`bad = 1`).

`claims_gate`: **removing a single redundant pattern does not** — each
calibration sentence matches several, so this is a coarse end-to-end check rather
than a per-rule test. It does fire on wholesale damage: all `POSITIVE` removed →
2 misses, all `NEGATIVE` → 1, and disabling `ARITHMETIC_EXACT` — the filter the
calibration exists for — → 3. Stated plainly because "the calibration passes" is
otherwise read as more than it is.

**`S51` again, twice.** My first injection into each file failed to trip it, and
in both cases the fault was insufficient rather than the check vacuous. That is
the third and fourth time this project has hit it; the lesson is stable and I
still needed two attempts each.

Build green (3757 jobs), sorries 0, ledger `NscStd 67.25% / Nsc 50.88%`, axioms
2, base hash `cd7a22e688df` unmoved. Guards green.

**Might-mean, unhedged:** two cycles running I have shipped an instrument change
with no way to detect if it broke the instrument, in a project whose entire
apparatus exists to detect exactly that.
