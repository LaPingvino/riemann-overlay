# COMPARISON — a claimed proof of RH, set against this project

**Written `SESSION 445`, 2026-11-20, the day of the release.** Every factual
statement below is tagged **[read]** (checked against a primary source or the
released files, by this session) or **[secondhand]** (reported by someone else,
not checked here), and every inference is marked **[inferred]**. Nothing here is
a verdict on the proof. This project has not built it and cannot yet judge it.

## 1. What was released

* **The note.** Levent Alpöge, four pages, `https://alpo.ge/remark.pdf`
  (245,114 bytes, SHA-256 `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`).
  It says: *"I believe I have, working with Claude, discovered a proof of the
  Riemann Hypothesis. In fact, the method easily extends much further, resolving
  the so-called Generalized Riemann Hypothesis"*, and *"Claude and I have also
  formalized the arguments without assumptions."* It presents only Lean: *"I
  decided to only present Lean."* **[read]**
* **The tarball.** `https://alpo.ge/lean.tar.gz.part01` … `part14` (thirteen of
  18,000,000 bytes and one of 5,275,554; `part15` returns the site's HTML home
  page, so there are fourteen). Concatenated, `lean.tar.gz` has SHA-256
  `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; per-part
  hashes are in §7. It unpacks to `lean/` (1.4 GB): 175,187 `.lean` files,
  toolchain `leanprover/lean4:v4.33.1`, a single dependency, Mathlib at
  `0df444a360eaa60ab8c11dca51a86af692955474`. **[read]**
* **The author.** Alpöge is the co-author, with Ralph Furman, of
  arXiv:2608.13637 — the zeta-23 paper whose Lean tree this repository vendors
  as `vendor/zeta23` and whose `0.6725` is this project's `NscStd` row
  (`MAP.md` §2). **[read]**
* **Reception.** Terence Tao's post of 2026-11-20, *"Unforced Euler singularity,
  unforced Navier-Stokes singularity, and the Generalized Riemann Hypothesis"*
  (<https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/>), describes *"an (enormous) Lean-only
  proof of the Generalized Riemann Hypothesis"*, says it *"appears to use the
  full power of modern developments on the Langlands program and arithmetic
  geometry"*, and points to a Lean Zulip thread for verification. The post
  reports no build, axiom check or error. **[read, through a fetch summary]**
  A *Scientific American* report quoting Andrew Sutherland on a kernel recheck
  *"with only the three standard axioms"* was relayed to this session and **not
  reached** by its searches. **[secondhand]** A comparator run is reported pending.
  **[secondhand]**

## 2. The statement

`src/Main.lean`, in full, after its two imports **[read]**:

```lean
theorem riemannHypothesis : RiemannHypothesis := rhOfAll
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
```

`RiemannHypothesis` is not defined in the tree; it is Mathlib's
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`):

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

`src/Statements.lean` imports only `Mathlib` and restates the zeta form and three
Dirichlet forms over Mathlib's `riemannZeta` and `DirichletCharacter.LFunction`.
`rhOfAll` is `Formalism.VW.rh_of_every allChi` in
`src/Supplements/Kernels/MainTheorems.lean`. **[read]**

**Pin diff of the definitions.** This repository builds against Mathlib
`51e6992e…` (2026-08-03); the release pins `0df444a…` (2026-08-21). Between the
two, `git diff --stat` over `Mathlib/NumberTheory/LSeries/`,
`Mathlib/NumberTheory/DirichletCharacter/`, `Mathlib/NumberTheory/EulerProduct/`,
`Mathlib/NumberTheory/Harmonic/` and `Mathlib/Analysis/SpecialFunctions/Gamma/`
shows **no change in the first four** and three edits in `Gamma/` — two
`@[grind =]` attributes, one new theorem, one proof shortened. No definition in
those directories moved. **[read]** That is a statement about those five
directories, not about the whole dependency closure of `riemannZeta` (`Complex`,
`cpow`, the Mellin machinery), which this session did not diff.

## 3. The trust audit

`tools/trust_audit.py` is the scout's grep audit made reproducible. It strips
comments and string literals, then reports pins, shipped artefacts, a
forbidden-token list, every metaprogram site, any shadowing of statement-level
names, and the top-level statement. Its result on this tarball:

Run 2026-11-20 on the unpacked tree (`175,187` files, `17,374,215` lines; 20
minutes on this machine). **[read]** — every line below is the script's output or
this session's reading of the site it names.

| check | result |
|---|---|
| toolchain | `leanprover/lean4:v4.33.1` (this repo: `v4.33.0-rc2`) |
| dependencies | Mathlib `0df444a…` and its transitive packages, nothing else; `lakefile.toml` options are `--tstack=400000`, `maxHeartbeats = 4000000`, `synthInstance.maxHeartbeats = 400000` — no kernel-related option |
| shipped artefacts | **none** — no `.lake/`, no `.olean`, no local `Mathlib/`, no native code |
| `axiom`, `sorry`, `sorryAx`, `admit`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, `ofReduceBool`, `reduceNat`, `trustCompiler`, `skipKernelTC`, `addDeclWithoutChecking`, `@[csimp]`, `opaque` | **0 each**, comments and strings stripped, every token matched at word boundaries anywhere on a line (so `set_option … in axiom`, two commands on one line and `attribute [csimp]` count) — re-run with these patterns on a re-fetched copy, same SHA-256 |
| `run_cmd` + `modifyEnv` | 5 sites, `src/BuildAid/D1`–`D5.lean`, four lines each: `Lean.LibrarySuggestions.nameDenyListExt.addEntry env "<namespace>"` — a library-suggestion deny list; it adds no declaration |
| `addDecl` | 2 sites, `Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean` (`cpt_copy_thms`): copies definitions and theorems under new names with a substitution. `Lean.addDecl` sends the declaration to the kernel |
| `elab` | 4 sites: `cpt_copy_thms` above; `kexactB` (`…/HeckeNonvanishing/Imports.lean`) and `kcopy`/`#kcopy_probe` (`…/NumberFieldFamilies/OwnStruct.lean`), tactics that assign the goal without the elaborator's type check — a mismatch would surface at the kernel, not before |
| `macro` / `notation` | 87 sites in 64 files / 1,722 in 952 files; none reuses a statement-level name (next row) |
| shadowing | no declaration or notation named `RiemannHypothesis`, `riemannZeta`, `DirichletCharacter`, `hurwitzZeta` or `completedRiemannZeta`; two `def LFunction`s, namespaced `GroundTheory.Automorphic.GodementJacquet` and `HeckeCharacter`, and four `IsPrimitive`s in their own namespaces — none is `DirichletCharacter.LFunction`, and `Main.lean` opens no namespace |
| top level | `src/Statements.lean` imports only `Mathlib`; `Main.lean` as in §2 |

So the scout's grep audit reproduces: no forbidden token, and the four
metaprograms it named are the only sites matching the listed metaprogram patterns
that touch the environment or a goal. Each skips an elaborator check; none, as
read here, skips the kernel's. Scope: the `87` macros and `1,722` notations were
counted, not read, and the pattern list does not cover `setEnv` or elaborators
registered through an attribute — a reader extending the audit should start
there.

**What this audit cannot do.** Grep is necessary, not sufficient. The decisive
checks are a full build and `#print axioms riemannHypothesis`, preferably through
an independent kernel replay (`lean4checker`) or the Lean FRO's comparator
against a trusted statement file. This machine has 23 GB of RAM and no swap, and
building 17.4M lines was not attempted.

## 4. The strategy

* **The endgame is Landau's theorem.** **[read]**
  `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean`
  proves `landau_entire` — if a Mellin integral of a function `H ≥ 0` matches
  `P′/P` past `Re s = 1`, then `P` has no zero with `Re s > θ` — and, at line
  `538`, `zero_free_of_Chebyshev_growth : Lv.ChebyshevGrowthImpliesZeroFree`,
  whose statement (`ExplicitFormulaErrorOfHostConditions.lean`) is: a one-sided
  bound `Gm y ≤ y^θ` for all large `y` gives a zero-free half-plane `Re s > θ`.
  `Gm` is `Gz` plus a weighted sum of character terms. **[read]** That `Gz` and
  `Gm` are weighted prime sums — so that this is Landau's theorem on Dirichlet
  series with non-negative coefficients, a one-sided sign bound giving
  zero-freeness — is **[inferred]**: `Gz`'s definition was not opened.
* **The inputs to that bound are arithmetic-geometric.** The note's timeline
  names a Stepanov-type argument (*"In Stepanov's argument resolving Riemann over
  function fields one uses a divisor involving multiplicity. This argument is a
  descendant of Stepanov's"*), iterated theta lifts between totally definite
  unitary groups (item 8), and *"a significant weakening of Vandiver"* (item 17).
  **[read, in the note]** That these are what the Lean constructs is
  **[inferred]**, and the tree's vocabulary only half supports it. Substring
  counts over the `.lean` files: `GaloisRep` in `3,976`, `Theta` in `47,621` and
  `theta` in `10,424` (ambiguous — theta functions and series as well as lifts),
  but `Vandiver` and `Stepanov` in **`0`**. This session read no proof in the
  middle of the development. A blog commenter on Tao's post
  describes an integrality bound with an error term whose arithmetic part
  involves Tate–Shafarevich groups of Tate twists, and Galois representations
  attached to automorphic forms on unitary groups. **[secondhand]**
* **"Multiplicity" in the note is not the multiplicity of a zero.** It is the
  order of vanishing of Stepanov's auxiliary divisor, which the chain of lifts
  *"mimics"*. **[read]** No statement about the multiplicity of zeros of `ζ`
  appears among the five top-level theorems. **[read]** That nothing in the tree
  bounds it is **[inferred]** from the endgame's shape (§4, first bullet).

## 5. Item by item against this project

All of this is conditional on `h : RiemannHypothesis`, which `Riemann/RH.lean`
carries as a **hypothesis**, never an axiom (`Riemann/Assumptions.lean`'s rule);
each cone below is `[propext, Classical.choice, Quot.sound]`.

| this project's object | what `h` does to it | declaration |
|---|---|---|
| `zetaZeroData T` (zeta-23's `zerosIn 0 T`: `ζ ρ = 0`, `0 < Re ρ < 1`, `0 < Im ρ ≤ T`) | covered by Mathlib's `RiemannHypothesis` directly: `0 < Re ρ < 1` excludes the trivial zeros and the pole | `Riemann.re_eq_half_of_mem_zerosIn` |
| `N_off` | `0` in every window | `Riemann.zetaZeroData_Noff_eq_zero` |
| `NoHaunted zetaFamily` | holds | `Riemann.noHaunted_zeta_of_RH`, via `Blindness.noHaunted_of_Noff_zero` |
| the two rows, window by window | `Nsc = NscStd` | `Riemann.Nsc_eq_NscStd_of_RH` |
| **the `Nsc` row** | **`50.88%` → `67.25%`** | `Riemann.proportion_of_RH_zeta`, via `Riemann.proportion_of_noHaunted_zeta` and `Riemann.certified_std` |
| **the `NscStd` row** | **unchanged at `67.25%`** — `h` locates zeros and does not count them | `Riemann.certified_std` is the input |
| the `≈0.682` wall, `StarBound`, `MomentBound`, `Riemann.starBound_of_mult_le_two`, `ProportionAny` | nothing: every one is a multiplicity statement. At the level of a single window, `N_off = 0` — what `h` gives — admits configurations with `N⊛ > C·N` for every `C` | `Riemann.Blindness.noHaunted_no_starBound`; `MAP.md` §5, `PRICES.md` |
| §3's blindness (`Blindness.no_muInvariant_theory_computes_NscStd`), `Gauge`, `Fiber` | still true — they are theorems about every `ZeroData` — and **confirmed by the route**: the proof reaches RH through prime-sum positivity, information that is not a function of the ordinate measure `μ_T` **[inferred]** | `MAP.md` §3 |
| `ξ′` | `h` puts the zeros of `ξ′` on the line too (classically), but deriving it in Lean needs a Hadamard factorisation this repo does not have; `Riemann.xiPrimeFamily` stays an axiom, with no construction | follow-up |
| `FAILURES.md` `#9`–`#11` (the RH tier) | their `¬RH` branch empties, so the deaths stand unconditionally; none is revived | `FAILURES.md` T3(b), `445` note |
| RH-conditional literature constants (CMR `1.3208`, `~0.679`) | stay `[RECALL, UNVERIFIED]` — `h` makes them applicable, not checked | `PRICES.md` |

**Headline.** The off-line side is settled conditionally: under `h` the `Nsc`
row rises from `50.88%` to `67.25%`, by exactly the certified haunted density
`0.16375`. The multiplicity side — everything between `67.25%` and `100%` — is
untouched. The blindness results are confirmed rather than contradicted by the
route: the proof goes around the `μ_T`-invariant class, as §3 of `MAP.md` says
any route to these questions must.

### Where the proof sits in the project's own terms [inferred]

* **The right wall, from the right side.** `FAILURES.md` W7's epitaph is
  *"only the Euler product bites"*, and W28's cold draft (`LEADS.md`) bundled the
  multiplicative nature as **M** — free monoid, `Λ ≥ 0`, Euler product, explicit
  formula. Landau's theorem on a non-negative-coefficient Dirichlet series lives
  in bundle M.
* **The same family, not the same tool.** W16 (`LEADS.md`) found the prime side
  `β`-sensitive — `x^ρ = x^β e^{iγ log x}` — and outside the blindness class.
  W16 used Landau's *formula*, `Σ x^ρ`; the proof uses Landau's *theorem*, a
  sign argument. Same family, not the same tool.
* **The right proof that M cannot suffice alone.** W28's Beurling negative
  control — generalised prime systems with all of bundle M and PNT, for which RH
  is false — predicted that M alone is not enough. The proof agrees: its extra
  input is arithmetic-geometric (theta lifts, Galois representations, a weakened
  Vandiver), structure Beurling systems lack. It is **not** the additive bundle
  **S** (Type I/II, level of distribution) that the draft named as the mandatory
  second field (`SURPRISES.md` `S240`; `LEADS.md` `445`).

## 6. What cannot be judged yet

* Whether the development builds, and with which axioms — not attempted here
  (§3).
* Whether the middle of the development constructs what its names say.
* Whether the dependency closure of `riemannZeta` between the two Mathlib pins
  is unchanged beyond the five directories diffed (§2).
* Any claim about GRH's consequences for this project: this repository has no
  Dirichlet-`L` objects.

## 7. Cheap checks for readers

1. **Hashes.** Download `part01`…`part14`, `sha256sum` each and the
   concatenation, and compare with the list below.
2. **The audit.** `python3 -I tools/trust_audit.py <unpacked>/lean
   --ref-manifest lake-manifest.json` — read §4 of its output (the metaprogram
   sites) yourself; they are listed, not scored.
3. **The statement.** `src/Main.lean` is twelve lines; `src/Statements.lean`
   imports only Mathlib. Check that nothing in the tree redeclares
   `RiemannHypothesis` (the audit's §5).
4. **The pin.** `git diff 51e6992e 0df444a3 -- Mathlib/NumberTheory/LSeries` in a
   Mathlib clone is empty.
5. **This repository's half.** `lake env lean audit/PrintAxioms.lean | grep RH`
   — the five `Riemann/RH.lean` theorems print the three standard axioms and
   nothing else; `h` is a binder.

```
86974b1c242ca7b6748f3299df4fc64ee0f6e06c776ac964fb64888101a3de77  lean.tar.gz.part01
1c2a2477354a9dfa97ff1ce54861e96ed885bd456fffbaaabc2028314a229c42  lean.tar.gz.part02
1465a23b1b579a881e24e5ffaf7c4c3727af28ea24741f1ec80e1d67947530a3  lean.tar.gz.part03
3929e327eecb4e2c5c7cae30e104e6a4a52fa6b82d28325bcda8e9da1c86893b  lean.tar.gz.part04
f25d7e80f7c4ad6d674aa18b323ca760f848857c8755501c149317c38a66c75d  lean.tar.gz.part05
a8c651a68327811b37dce3cca8eda5e0b2102fa227c0d395cbb7553e4dd69939  lean.tar.gz.part06
65c7e502a9b236a0f68d9e0aa6e089d4c09b9fc7a0960a149384063ccbe5e869  lean.tar.gz.part07
71b027ad6e4179c3a50ce72921e3fec0a2dd751ec7472ac2c644ad145a50ec7e  lean.tar.gz.part08
47718977ebaa8613f1647e93134479780db9320c5fa911463fd312a6257b796f  lean.tar.gz.part09
1d85ece78e0779cec26b0cce29c6462d9f90180e56d78120b152df101715240b  lean.tar.gz.part10
cf83a159d1a9540012229c376562587dd966da10cd657cbcef53acfd03232448  lean.tar.gz.part11
1aa5415bd2db83b2689afeeb946419303b3c4f599ae790ad74d38465f768b502  lean.tar.gz.part12
2de4edbce8ebdbfd0b94bc89bab518c7294209f408ec5b14a7be9e4832d9da81  lean.tar.gz.part13
53f8ea43a9b5dcab97b84a52f3ac2848711c844a5420a4c56418093bacb3c6f6  lean.tar.gz.part14
9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc  lean.tar.gz  (concatenation)
3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d  remark.pdf
```

Fetched 2026-11-20 ~22:19 UTC. The site can change; these hashes are what this
session read.
