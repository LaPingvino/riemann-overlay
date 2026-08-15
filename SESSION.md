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
