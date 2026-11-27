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

## 8. The shortened editions (`SESSION 447`, 2026-11-27)

Tags as above: **[read]** checked here against the primary source, **[secondhand]**
reported by someone else, **[inferred]** this session's reading.

### 8.1 What was released

* **The repository.** <https://github.com/lsernau/grh-lean>, one commit,
  **`72fead102f663d5c7a407964a13dc0cf9d977207`** (author line *Luke Sernau
  &lt;l.sernau@gmail.com&gt;*, 2026-11-25 12:38 −0800), Apache-2.0. The GitHub
  profile `lsernau` carries no name or affiliation. That the work comes from
  Anthropic rests on the README's own words, *"produced in collaboration with my
  colleagues at Anthropic, and Claude"*, and on `LICENSE` and `NOTICE`
  (*Copyright 2026 Anthropic, PBC*). **[read]** The press reports
  (heise.de; Wikipedia's article on the proof) were not fetched by this session.
  **[secondhand]**
* **Two editions, one Lake project each.** Both are pinned to
  `leanprover/lean4:v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. That
  commit is on upstream Mathlib `master` (the GitHub compare API reports the
  pin `behind_by 0` against master). Every package URL in `lake-manifest.json` is
  `leanprover-community` or `leanprover`, and the two manifests are byte-identical. **[read]**

| edition | `.lean` files under `src/` | lines (`wc -l`) | non-blank | code (no comments) | bytes | ~tokens (bytes/4) |
|---|---:|---:|---:|---:|---:|---:|
| `grh/` (readable) | 803 | 477,124 | 432,527 | 299,902 | 30,050,271 | ~7.5M |
| `grh-compact/` | 794 | 112,827 | 95,030 | 76,149 | 7,420,187 | ~1.9M |
| Alpöge's release (§1) | 175,187 | 17,374,215 | — | — | ~1.4 GB unpacked | ~350M |

The README's *"about 300,000 lines of code"* and *"about 76,000"*, and the press
figure of 477k, are the code and `wc -l` columns: all three readings check out. **[read]**
(Counts are this session's: comments are `--` and nested `/- -/`; the token figure is a
rough rule, not a tokenizer.)

### 8.2 The audit, redone on both editions

`tools/trust_audit.py`, run unchanged on each folder (`src/`, `scripts/` and
`Challenge.lean`). Its exit code is `1` on both, and the hits explain it: the
**five `sorry`s of `Challenge.lean`**, the Comparator challenge file, with one
`sorry` per theorem by design. Nothing imports that file, and it is not among the lakefile's
`defaultTargets` (`Lib`, `New`, `Main`). Its only importer, `comparator.json`'s
`challenge_module`, is a reference by name. The hits also show that the scanner
does see a token when one is there. **[read]**

| check | `grh/` | `grh-compact/` |
|---|---|---|
| `axiom`, `sorryAx`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `reduceBool`, `reduceNat`, `trustCompiler`, `debug.skipKernelTC`, `addDeclWithoutChecking`, `csimp`, `opaque` | **0 each** | **0 each** |
| `sorry` | 5, all in `Challenge.lean` | 5, all in `Challenge.lean` |
| `run_cmd`, `run_elab`, `run_meta`, `#eval`, `modifyEnv`, `addDecl`, `addAndCompile`, `elab`, `macro`, `syntax`, `notation`, `initialize`, `import Lean` | **0 each** | **0 each** |
| extra greps (`445`'s gaps): `setEnv`, `command_elab`, `term_elab`, `tactic_elab`, `@[tactic`, `builtin_initialize`, `declare_syntax_cat`, `macro_rules`, `Lean.Environment`, `CoreM`, `MetaM`, `TacticM` | **0** | **0** |
| shadowing of `RiemannHypothesis`, `riemannZeta`, `DirichletCharacter`, `LFunction`, … | none | none |
| shipped artefacts (`.lake/`, `.olean`, native code) | none | none |

So **none of Alpöge's metaprogram sites** (§3: the `D1`–`D5` deny-list
`run_cmd`s, `cpt_copy_thms`'s `addDecl`, the `kexactB`/`kcopy` elaborators) has a
counterpart in either edition. A further grep, for `infix`, `infixl`, `infixr`, `prefix`,
`postfix`, `notation`, `notation3`, `macro`, `syntax` and `elab` at the start of a line (with or
without `local`/`scoped` and attributes), finds one hit, and that hit is prose inside a docstring
(`New/Spanning/Unfolding/PoincareSeries.lean:13`). So neither edition declares a macro, notation,
elaborator or environment edit. **[read]** What is left at the elaborator level, read
here: `Lib/Speed.lean` lowers the priorities of 84 Mathlib instances and takes 64
Mathlib lemmas out of the default `simp` set (`attribute [simp ←, simp]`). The
authors say *"with this file emptied, everything still compiled on Lean 4.33.1"*,
which was not checked here. The `set_option`s in the files are 33 `backward.isDefEq.respectTransparency`,
5 `synthInstance.maxSize`, 5 `synthInstance.maxHeartbeats` and one
`warning.simp.varHead`. These are among further local settings (`seal … in`, `irreducible`
marks, local instances; `GUIDE.md` §5 lists them), which were not counted here. All of them steer elaboration. None reaches the kernel or
changes a statement whose type is a Mathlib or `Statements.lean` constant.

### 8.3 The statements

* `src/Statements.lean` is **byte-identical in all three releases**: both editions
  and Alpöge's tarball (extracted again from the parts cached on this machine, whose
  concatenation still hashes to `9631b4f0…`), SHA-256
  `79ef7ca776e42abe1f46caee13ea09bd19f1e2d0b1620d8d5d200258f33b47bf`. So
  *"the same five theorems"* is [read] for the statement bodies, not only for the names.
  `Main.lean` has the five names and types of §2, with different proof terms:
  `New.zeta_zeros_on_line New.grh`, `New.grh`,
  `New.zeros_on_line New.grh`. **[read]**
* **Mathlib's `RiemannHypothesis` at the new pin.** Its text at `56a00585`
  (`RiemannZeta.lean:185`) is identical to the one at this repository's pin
  `51e6992e`. Between the two pins (1,776 commits), the five directories of §2 show 42
  changed files. The only definition-header line added or removed is a new
  `def hardyZ`. Read by hand, the changes to `RiemannZeta.lean`,
  `DirichletContinuation.lean`, `HurwitzZeta.lean` and `DirichletCharacter/Basic.lean`
  are proof edits and import moves. **[read]** The caveat of §2 stands: this is
  not the whole dependency closure of `riemannZeta`.

### 8.4 Build and axioms

**The full build was started and stopped.** It ran in a cgroup capped at `9 GB` with no
swap (`systemd-run --user --scope -p MemoryMax=9G`, drilled first: a `400 MB` allocation under
a `200 MB` cap was killed), with `LEAN_NUM_THREADS=4`, the Mathlib cache from
`lake exe cache get` and a 4-hour time-box. No script of the repository was run. In the
16 minutes after the cache was in place it built 52 tree modules (log jobs 9047 to 9098 of
9852), which projects the 803 modules to about 4–4.5 hours, at or past the time-box. It was
**stopped by choice** at that point, to run the plucked build below instead. It ran within the cap
and was not killed. The built `.olean`s are kept in `~/Projects/.riemann-ext/grh-lean/grh/.lake`,
and the scripts are in `~/Projects/.riemann-ext/axcheck/` (`build.sh`, `pluck.sh`), so a later run
resumes where it stopped. **So there is no
`#print axioms` here for the five theorems.** The README reports the build, `#print axioms`,
three independent kernels (nanoda, con-leche, con-ron) on a `leanexport` of the five theorems,
and Comparator v4.35.0. All of that is **[secondhand]**.

**A plucked build of one compartment was done instead.** That compartment is the endgame of §9,
built alone with `lake build New.Reduction.Zeros.Criterion New.Reduction.Zeros.PrimeNumberTheorem`
under the same cap. It completed in 4 minutes on top of the modules the stopped run had already
built. Then this session's own file (`.riemann-ext/axcheck/Endgame.lean`; the repository's
`scripts/PrintAxioms.lean` was not used) printed **`[propext, Classical.choice, Quot.sound]`** for
each of `New.LFunction_ne_zero_of_primeRemainder_le`, `New.isPolar_primeRemainder`,
`New.IsPolar.landau`, `New.exists_entireL_quadTwist_ne_zero`,
`New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt` and
`New.eventually_abs_primeRemainder_le`. **[read]** This checks the endgame's lemmas with the kernel
of `v4.35.0` and nothing beyond them. It says nothing about `star_inequality` or the five theorems.

### 8.5 The route, read in the readable edition

This settles several of §4's **[inferred]** tags *for this edition*. It does not settle them
for Alpöge's tree, whose names and files differ.

* **The endgame is Landau's lemma, and the prime sum is now read, not inferred.**
  `New.LFunction_ne_zero_of_primeRemainder_le` (`New/Reduction/Zeros/Criterion.lean`)
  takes the remainder `R_q(x) = Σ_{n≤x} λ(n)(1/n − 1/x) − log x/φ(q) − c_q` with
  `λ(n) = Λ(n)(1 − (n/d))` on `n ≡ 1 mod q` and `0` otherwise. That weight is **non-negative**
  (`lambdaKResidueClass_nonneg`, `New/Reduction/Zeros/PrimeError.lean:45,76`: the definition is
  Mathlib's `vonMangoldt.residueClass 1 n · (1 − chiK d n)`, and the lemma is
  `mul_nonneg (residueClass_nonneg …) (one_sub_chiK_mem_Icc …).1`; both are in the plucked build
  of §8.4). The criterion turns a
  one-sided bound `R_q(x) ≤ x^(β−1)` into no zero of any `L(s, ψ)` mod `q` in
  `re s > β`. The transform of `R_q(e^v)` has simple poles with residue
  `(n(s) − n′(s)) / (φ(q) s (1 − s))` (`isPolar_primeRemainder`), where `n` and `n′`
  sum the **orders of the zeros** (`analyticOrderNatAt`) of the `L(s, ψ)` and of their
  twists by `(·/d)`. A prime `d` is chosen with no twisted zero in the box
  (`exists_entireL_quadTwist_ne_zero`, a zero-density count from Pólya–Vinogradov). So
  `n′ = 0` there, the residue is `n(s)/(φ(q)s(1−s)) ≥ 0` at real `s`, and
  `IsPolar.landau` forces `n(ρ) = 0`. **[read]**
* **The one-sided bound comes from one inequality.** `New.Data.primeRemainder_le`
  (`OneSidedBound.lean`) bounds `R_{q₀}(x)` by `φ(q₀) log⁶ b / m + |R_{q₀}(x₁)| + log b·|R₁(x₁)|`
  through `star_inequality` (`MainInequality.lean`). The two error terms at the far
  cut-off `x₁` are handled by the prime number theorem with a crude zero-free region
  (`Lib/Analytic/PrimeNumberTheorem`). The main inequality compares a covolume bounded
  above by Theorems A (short forms) and B (enough forms) with one bounded below by
  Theorem C (long forms). Its head lists, as earlier bounds for sums over primes by size against divisibility,
  Pritsker (the Gelfond–Schnirelman method), Granville–Stark, Bombieri (*Counting points on
  curves over finite fields*) and van Frankenhuijsen. **[read]**
* **Stepanov is present; Vandiver is not used.** `New.stepanov_count`
  (`New/UpperBound/ElementaryDivisors/RootLemma.lean`, *"Stepanov's count of zeros at
  the residue classes of a local ring"*) [read]. The only occurrence of *Vandiver* is a
  comment in `New/Congruences/FirstOrder/DenominatorBound.lean`: *"the orders of the even
  classes, where Vandiver's conjecture lives, do not enter"*. So §4's *"a significant
  weakening of Vandiver"* (the note's item 17) has **no counterpart in this edition's
  inputs**, by the authors' account. **[read, as their comment; not traced]**
* **Multiplicity enters only as a sign.** In the whole edition, zero orders
  (`analyticOrderNatAt`, `analyticOrderAt`, `meromorphicOrderAt`) occur in exactly five
  files: `Lib/Analytic/Landau`, `Lib/Analytic/EntireLFunction`, `New/Reduction/Zeros/Criterion`,
  `New/Reduction/Zeros/PrimeError`, and `Lib/CM/Sigma/Basic` (there the order is that of the Weierstrass `℘`).
  The positive witness (`R17`) is that list together with the one place the orders are consumed: the
  residue above, used through `n(s) ≥ 0` and `n(ρ) = 0`. The order statements in the
  four analytic files are `analyticOrderAt_entireL_ne_top`, `analyticOrderNatAt_entireL_eq_zero_iff`
  (order zero exactly where `entireL` does not vanish), the residue lemma
  `tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt`, and the uses in `isPolar_primeRemainder`
  and the criterion. None bounds an order from above, and none of the five top-level statements
  mentions one. **[read]**

## 9. The compartment map (`447`): the readable edition, level by level

**Why.** To check and borrow one compartment at a time, with memory and context bounded,
rather than the whole tree. The map is generated, not hand-drawn: `tools/explorer` (the
`446` generator) now reads a checked-out edition (`-src`, `-commit`) and writes
`c.json` from a spec, `tools/explorer/compartments/grh.json`. The spec holds the top
two levels and their plain-language summaries. Below them every directory and every file
becomes a node, and each file lists its declarations, which link into the explorer's
declaration view. The Pages Action regenerates it from the pinned commit, and the explorer
shows it at `?d=grh`. Not on `origin` yet: the push is Joop's. *(`448`: pushed since; `origin/main` was at `1032e78` on 2026-11-27.)*

**Summaries at every level.** Levels 0–2 carry the spec's hand-written summaries. Every file
node (801 of 803) carries the title its authors gave it, the first `# ` line of its module
docstring. Every directory lists the titles of its files. Declarations are named and sized, and
their statements are left out of the data to keep it small; the edition's Apache-2.0 licence
allows `-statements`. **The compact edition is not mapped.** It is not flat (794 files under
`Lib/` and `New/`), but its folders differ from the readable edition's (`New/Endgame`,
`New/Filling`, …). Its own `GUIDE.md` §2 does assign them: A to `Curve`, `Columns`, `TwistedHecke`,
`Core`, `Seesaw`; B to `Filling`, `RealPlace`, `DiscreteSeries`; C to `Heights`, `Rows`, `Exchange`,
`Trace`, `GaloisRep`, `Forms`, `SiegelWeil`, `Weil`, `Selmer`, `Patching`, `Lift`. A spec of its own,
following that list, is the next step. It was not written in this session.

### 9.1 Others' maps, and the boundaries reused

Read through the GitHub API at the commits named. What these projects claim about the
proof is **[secondhand]**.

* **The authors' own:** `grh/GUIDE.md` §1 has a topic table (Reduction; Derivatives; Upper
  bound; Spanning; Lower bound: determinant, one lift, congruences; Appendix) and
  sorts `Lib` from `New`. **This map's top level is that table.**
* **The GRH Lean Handbook,** <https://github.com/tamnd/grh-lean-handbook> at `152bdf2a`, on
  this edition: 13 planned volumes, each a union of folders (vol. 1 Reduction; 2
  `Lib/Analytic`; 3–8 the `Lib` theories; 9 Theorem A = `UpperBound` + `Derivatives`
  without `Sharpness`; 10 Theorem B = `Spanning`; 11 Theorem C = `Determinant` +
  `OneLift` + `Derivatives/Sharpness`; 12 `Congruences`). **The background sub-compartments
  and the A/B/C split follow its volumes**, and each node names its volume. There are two
  departures. The appendix stands alone here, where the Handbook puts it with representations
  (vol. 5). And `Reduction/Data/Existence` sits under the reduction, where vol. 2 takes it in part.
* **A blueprint of this edition,** <https://github.com/Euler2023/grh-blueprint> at
  `23025bd0` (in Chinese, with an English monograph): an interactive dependency graph
  from the data and the weighted prime remainder, through Theorems A, B, C and the main
  inequality, to the zeros. It uses the same top-level cut.
* **On Alpöge's original:** <https://github.com/rh-lean-roadmap/rh-lean-roadmap> at
  `0be265cc` has a six-step reading guide, a `Roadmap.lean` that derives `RiemannHypothesis`
  inside the archive from three inputs (`Green`, `VWin`, `HypsAlt …`), and a slicer that
  keeps 18,096 of 175,188 files (3.2M of 17.4M lines). It cites J. Shore's kernel-traced
  dependency data (<https://github.com/james-shore/rh-proof-dependencies>): 804,912 of
  1,061,400 declarations are used by the five theorems.
  <https://github.com/thekeunpie-hash/rh-lean-dissection> at `5f66a21e` has a static audit
  and a "minimal backbone" spec. <https://github.com/Sidler4Hare/alpoge-claude-rh-reconstruction>
  at `7d17bb99` is a 329-page paper reconstruction.
* **Where Sernau's editions differ from those maps:** the original's folders
  (`Formalism/…`, `Supplements/…`) do not survive. The endgame's prime sum is a
  differently named object (`primeRemainder` with weight `Λ(n)(1 − (n/d))`, against §4's
  `Gz`/`Gm` Chebyshev-growth form). The edition's size is 2.7% of the original's lines. So the
  original's slices and step numbers do not carry over by name. The *shape*
  (endgame by Landau, one main inequality, three theorems behind it) does. **[inferred]**

### 9.2 The top levels

Tokens ≈ bytes/4. *Cone* = every file the node imports inside the tree, itself included,
Mathlib not counted: what a reader or a build needs besides Mathlib to check that node
alone. Module imports are exact (read from the `import` lines).

| level · node | files | lines | ~tokens | decls | cone files | cone ~tokens |
|---|---:|---:|---:|---:|---:|---:|
| **0 · the five theorems** (all through `New.grh`) | 803 | 477,124 | 7.5M | 23,839 | 803 | 7.5M |
| 1 · the statements and the last step (`Statements`, `Main`, `New/Main`) | 3 | 103 | 1.3k | 11 | 803 | 7.5M |
| **1 · endgame: one-sided prime bound → zeros** | 13 | 4,320 | 69k | 186 | **22** | **126k** |
| 2 · · the criterion and the remainder (`New/Reduction/Zeros`) | 3 | 775 | 12k | 37 | 21 | 119k |
| 2 · · analytic background (`Lib/Analytic`) | 10 | 3,545 | 56k | 149 | 19 | 113k |
| 1 · the reduction: data, lattices, main inequality | 14 | 5,378 | 79k | 412 | 801 | 7.5M |
| 1 · Theorem A: short forms | 72 | 44,510 | 704k | 2,387 | 428 | 3.9M |
| 2 · · upper bound: a composite lift | 55 | 35,318 | 559k | 1,865 | 428 | 3.9M |
| 2 · · derivatives of theta functions | 17 | 9,192 | 145k | 522 | 221 | 1.9M |
| 1 · Theorem B: enough forms (`Spanning`) | 91 | 59,251 | 952k | 2,800 | 451 | 4.1M |
| 1 · Theorem C: long forms | 116 | 77,040 | 1.3M | 3,279 | 754 | 7.1M |
| 2 · · the determinant | 33 | 21,707 | 360k | 941 | 754 | 7.1M |
| 2 · · one lift | 24 | 17,323 | 286k | 725 | 665 | 6.2M |
| 2 · · the bound is attained (`Derivatives/Sharpness`) | 6 | 3,199 | 52k | 178 | 274 | 2.4M |
| 2 · · congruences and Selmer groups | 53 | 34,811 | 578k | 1,435 | 723 | 6.8M |
| 1 · supplement: discrete series with a large gap | 9 | 4,979 | 81k | 264 | 122 | 1.0M |
| 1 · background theories (`Lib`, without `Analytic`) | 485 | 281,543 | 4.4M | 14,500 | 487 | 4.4M |
| 2 · · number fields, class field theory, CM | 63 | 36,235 | 565k | 1,817 | 348 | 3.2M |
| 2 · · unitary groups, automorphic forms | 59 | 29,418 | 437k | 1,966 | 214 | 1.8M |
| 2 · · representations | 61 | 39,440 | 618k | 1,965 | 222 | 2.0M |
| 2 · · theta correspondence, Siegel–Weil | 91 | 52,216 | 813k | 2,753 | 283 | 2.4M |
| 2 · · cohomology, p-adic Hodge theory | 96 | 61,680 | 942k | 3,228 | 270 | 2.4M |
| 2 · · Shimura varieties, Galois representations | 74 | 48,555 | 771k | 1,911 | 356 | 3.3M |
| 2 · · general mathematics, global settings | 41 | 13,999 | 206k | 860 | 155 | 1.3M |
| 3 · 115 directories | — | — | 109 of them ≤ 150k | — | 10 of them ≤ 200k | — |
| 4 · 803 files | — | — | median 8.9k, max 24k | — | 191 of them ≤ 200k | — |

**Which compartments are shared.** Counts of import lines between compartments at level 1:
`background` is imported by Theorem C (68), A (67), B (51), the appendix (9), the reduction (6)
and the endgame (2). The endgame is imported by the reduction (4), by `background` (3: CM,
cyclotomic and Siegel–Weil files use `Lib/Analytic`) and by Theorem B (1). It imports only
`Lib.Base` and `Lib.General.NumberTheory.ImaginaryQuadraticField`. The authors' warning
(*"folders are not layers: files of different folders import each other in both directions"*)
shows at this level: A and C import each other (A→C 3, C→A 22), and so do A and B and B and C. At
the file level the graph is acyclic, as Lean requires.

**The five theorems have one cone between them.** At the module level each is the whole
tree, since `Main` imports everything. At the declaration level the explorer's edges are
**[parsed]**, and in this edition they undercount badly: the cones reach about 440
declarations (~91k tokens), because most proofs call lemmas by dot notation on a local
(`D.integral_forms_long` with `D : Data P`), whose type a parse cannot know. A new `-dot`
option resolves `x.foo` to the unique tree declaration ending in `.foo`. That helps a little,
and accepting up to four candidates helps more at the price of spurious edges.
The true declaration cone needs the elaborated environment, which the build gives.

### 9.3 What fits in one session's context

* **No whole edition does.** The compact edition is ~1.9M tokens and the readable one ~7.5M.
* **No single theorem's cone does,** at any granularity that is exact: all five share one,
  and it is the whole tree.
* **One compartment plus the map above it does, where the compartment is closed under
  imports.** The endgame is: ~126k tokens with its cone, plus ~0.4k of summaries above it.
  That is the analytic half of the proof, with Landau, the criterion and the prime number theorem
  it uses. The theorems behind it are not: each of A, B and C is 0.7–1.3M tokens itself
  and 3.9–7.1M with its cone. There the unit is the **file**: every file is ≤ 24k tokens and
  every directory but six is ≤ 150k tokens, but only 191 of 803 files have a cone ≤ 200k.
  So a check of one file in context needs the *statements* of its imports, not their
  proofs, and that is the next instrument (statement-only cone sizes, `-statements`).
* **The clean cut is the criterion's own hypothesis.** `OneSidedBound.lean` draws on the
  automorphic side through two inputs. One is `star_inequality`, used once, in
  `Data.primeRemainder_le` (`OneSidedBound.lean:51`, its only use outside its own file). The other is
  `eventually_exists_data`, from `Reduction/Data/Existence` (a 186-file cone): admissible data
  exist at every large `x`. Both are stated over `Data P`. The cut that needs neither is the
  hypothesis `h_bound` of `LFunction_ne_zero_of_primeRemainder_le`, a one-sided bound on
  `primeRemainder`, stated with Mathlib objects and this compartment's own definitions only.
  The endgame was built and axiom-checked alone with that hypothesis open (§8.4), the way
  `Riemann/RH.lean` keeps `RiemannHypothesis` open. **[read]**

### 9.4 This project's reductions, read against the map

* **The `NscStd` row, the `≈0.682` wall, pair correlation past support 1.** None of them
  has a compartment. Multiplicity appears in the endgame only as `n(s) ≥ 0` (§8.5), and no
  compartment speaks of `N(T)`, pair correlation, form factors or Fourier support. The witness
  is a case-insensitive grep over both editions' `src/` for `hadamard`, `weierstrass product`,
  `riemannXi`, `completedRiemannZeta`, `zeroCount`, `explicit formula`, `riemann-von mangoldt` and
  `pair correlation`. Its 18 hits (readable) and 7 (compact) are all Hadamard's *determinant*
  inequality (used for the covolume bound), one docstring saying the CM sigma function is *not*
  defined by a Weierstrass product, `completedRiemannZeta` in `New/Main` (the functional
  equation), and one compact docstring's *"by an explicit formula"* about the choice of data.
  `xi` alone hits only Fontaine's `ξ` in p-adic Hodge theory. **The multiplicity side is untouched**, as `445` read from the
  original. **[read]**
* **Blindness.** The facts are **[read]** for this edition: the definitions of
  `primeRemainder` and `lambdaKResidueClass` were opened, and the route's only zero-side input
  is the *sign* of a residue whose numerator is a count of zeros at one point. The reading is
  **[inferred]**: that this means the route goes around the `μ_T`-invariant class, as `MAP.md`
  §3 says any route must, because its information comes from the prime side (`λ ≥ 0`, the main
  inequality) and no quantity of the endgame is a function of the ordinate measure `μ_T`. §5's
  row keeps its **[inferred]** tag, now resting on read definitions.
* **What could be borrowed.** These live in the endgame compartment, which is closed and fits
  in context and is kernel-checked here (§8.4): Landau's lemma (`IsPolar.landau`); residues of the log-derivative as zero
  orders (`tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt`); the entire
  `L`-function; a crude zero-free region; a Tauberian PNT with error; Pólya–Vinogradov;
  the symmetry of Dirichlet zeros. Of these, the order-as-residue tie is not new on this disk:
  `vendor/zeta23` has the argument principle with zero orders (`Zeta23/Analytic/RectangleLogDeriv.lean`)
  for `ζ`, and the edition adds it for Dirichlet `L`, which this project has no row for. **Not there:** Hadamard factorisation, `ξ′`, `N(T)`. So
  `Riemann.xiPrimeFamily` gets no construction from this edition. Graded in `LEADS.md`
  `447`.

## 10. Orientation: the proof strategy in plain words (`SESSION 448`, 2026-11-27)

**Source, and its grade.** Wikipedia, *"Alpöge's proof of the Riemann hypothesis"*, section
*"Proof strategy"* and its subsection *"Obtaining estimates from theta functions"*, at revision
`1388368826`. It was fetched on 2026-11-27 through the MediaWiki API (`action=parse`, the wikitext)
with a plain client name. Every formula below was copied from that wikitext and checked against it
symbol by symbol. The section says of itself *"The following is based on those sources"*: a note by
Robin Zhang (IHES, Hexagon preprint `2611.00809v2`, 22 November 2026) and a working draft
written by three AI agents *"at the behest of Michael O. Rubinstein"* (Waterloo, version 2, 22
November 2026). These are its refs 42–43, counted from the wikitext's `<ref>` tags. Both were
made by using AI agents to scan the Lean source. Neither was fetched here. So everything in §10.1–10.3 is
**[secondhand]**, two steps from the Lean. Checks made in this session are tagged **[checked here]**, and
§10.4 sets the account against the editions on disk.

### 10.1 What is estimated

* **The classical equivalence.** RH is equivalent to `ψ(x) = x + O(√x log² x)`, where
  `ψ(x) = Σ_{p^k ≤ x} log p = Σ_{n ≤ x} Λ(n)` is Chebyshev's function. The article cites Broughan,
  *Equivalents of the Riemann Hypothesis* vol. 1, Thm 4.9 (the Schoenfeld criterion). Note the
  square root: it is the `√x` here that the choice `m ≈ √x` below has to reproduce.
* **The smoothed error (de la Vallée-Poussin).** The proof does not bound `|ψ(x) − x|` directly. It bounds
  `G(x) = Σ_{n ≤ x} Λ(n)(x/n − 1) − x log x + (1 + γ)x`, with `γ` Euler's constant.
  **[checked here]** Since `Σ_{n≤x} Λ(n)/n = log x − γ + o(1)` (Mertens), `G(x) = x − ψ(x) + o(x)`.
  The constant `1 + γ` is the one that makes `G` small, and an upper bound on `G` is a bound on
  `ψ` from below.
* **The target: intermittent and one-sided.** For every `ε > 0` and every `A` there is a `Y > A`
  with `G(x) ≤ x^{1/2+ε}` for all `x` with `Y < x < Y^{3/2}`. It is an upper bound only, and it holds
  only on some windows `(Y, Y^{3/2})`, not for all large `x`. So the proof needs two steps.

### 10.2 Step one: the intermittent bound gives RH (Landau–Turán)

The article: this step is *"essentially"* classical, the theory of oscillations of prime-counting errors
due to Landau and Turán. It cites Kaczorowski–Pintz, *Oscillatory properties of arithmetical
functions I*, Acta Math. Hungar. 48 (1986), Thm 1 and Cor 1. The Mellin transform of `G` has poles at
the zeros of `ζ`. Differentiating the transform many times puts a weight on it that concentrates the
integral on a window where the bound holds. The bounds on the derivatives that result rule out a pole
to the right of the critical line. **[secondhand]**

### 10.3 Step two: the bound itself, from theta lifts

* **Stepanov's descendant.** By Alpöge's own note (*Remark*, 20 November 2026, the article's ref 7),
  an early milestone is a *"descendant"* of Stepanov's argument for RH for curves over finite fields.
  Carrying it over to the integers needs control of *"the length of a chain of theta lifts"*. In Stepanov's
  method an auxiliary function vanishes to high order. Here repeated theta lifts between unitary
  groups take that role, and each lift raises the **divisibility** of periods of automorphic forms.
  Arakelov theory compares this divisibility with the **size** of those periods. **[secondhand]**
* **Chebyshev's squeeze, the model: divisible but bounded.** `C(2n, n)` is divisible by every prime
  `n < p ≤ 2n` and is less than `4^n`, so `Σ_{n<p≤2n} log p ≤ n log 4`. The divisibility gives the left side,
  a prime-log sum like those in `G`. The size of the integer gives the right side. **[checked here: classical]**
* **The prototype in the proof: ℤ[i] theta.** Let `Θ(z) = Σ_{λ ∈ ℤ[i]} e^{−π|λ|² + λz}` and
  `T_n = Θ^{(n)}(0) = Σ_{λ ∈ ℤ[i]} λ^n e^{−π|λ|²}`. Then:
  * `T_n = 0` unless `4 | n`. **[checked here]** `λ ↦ iλ` gives `T_n = i^n T_n`.
  * The article states that `A_n = 2^n T_n / T_0^{n+1}` is an integer, and more generally for theta
    functions of CM fields. **[not checked here]**
  * Analytically `|T_n| ≤ T_0 (n/(πe))^{n/2}`. **[consistent, checked here]** The largest value of a single
    term, `max_r r^n e^{−πr²} = (n/(2πe))^{n/2}`, lies below this bound.
  * So `log|T_n|² ≤ n log n + O(n)`, and the same holds for `log A_n²`.
  * If a nonzero `A_n` is divisible by `p^{e_p}` for each `p` in a finite set `S`, then
    `Σ_{p∈S} e_p log p ≤ ½ n log n + O(n)`. Note the `½` and the exponent `n/2`. **[secondhand]**
* **How this meets `G`.** In the proof's theta functions the lower bounds for `e_p` contain terms
  `max(a/p^j − w, 0)`, where `a` is an order of differentiation and `w > 0` a weight. Put
  `x = a/w` and multiply by `log p`. The result is `w · max(x/p^j − 1, 0) log p`, which is `w` times the
  `p^j` term of the sum in `G(x)`. **[checked here: `Λ(p^j) = log p`; the lower bound itself is secondhand]**
* **Composing lifts: integral matrices.** For unitary groups a theta lift is a finite sum over
  lattice classes. So each lift is a matrix whose entries are derivatives of theta functions of pairs
  of lattices, and composing lifts multiplies the matrices. Entries divisible by `p^a` and by `p^b` give a product
  divisible by `p^{a+b}`, provided the denominators met along the way are controlled. Over a chain of
  `m` lifts the main divisibility grows like `m`. The covolume errors telescope to the first and last
  lattices, and the other errors (denominators among them) accumulate. With the chains chosen well,
  the endpoint error is of order `x/m` and the accumulated error of order `m`, up to small powers of
  `x`. **[secondhand]**
* **Why `m ≈ √x`.** `m = x/m` at `m = √x`, and only there. Both errors are then `√x · x^{o(1)}`, which is
  `G(x) ≤ x^{1/2+ε}`, the square root of §10.1. **[checked here: arithmetic]**

### 10.4 Against the editions on disk, and onto the compartments of §9

The article describes Alpöge's proof, read by agents. The editions on disk are Sernau's rewrites
(§8). Where they disagree, the files win for what *they* do, and neither reading settles what the
original does.

* **`G` is the edition's `primeRemainder`, twisted.** `R_q(x) = Σ_{n≤x} λ(n)(1/n − 1/x) − log x/φ(q) − c_q`
  has the shape of `G(x)/x`, with `Λ(n)` replaced by `λ(n) = Λ(n)(1 − (n/d))` on `n ≡ 1 mod q` (§8.5).
  So the bound `G ≤ x^{1/2+ε}` corresponds to `R ≤ x^{β−1}` with `β = 1/2 + ε`.
  **[read: the definition; the correspondence is this session's arithmetic]**
* **`m` is read.** `Data.primeRemainder_le` takes an `m` in `[√x, 2√x]`, the least power of `2`
  that is at least `√x` (`Reduction/Data/Existence.lean`: `isLeast_m`, line 555). Its bound is
  `φ(q₀) log⁶ b / m` plus two errors at the far scale `x₁`. In the `R` normalisation the `1/m` term is the
  `x/m` error. The `m`-sized error was not traced: it is not visible in that lemma. **[read]**
* **The intermittent step does not match. Recorded, not harmonised.** On disk, every criterion that
  turns a prime bound into zeros takes it **for all large `x`**:
  * the readable edition's `LFunction_ne_zero_of_primeRemainder_le` (`h_bound : … ∀ᶠ x in atTop`)
    and `IsPolar.landau` (`∀ᶠ v in atTop`), which are Landau's lemma, not Landau–Turán;
  * the compact edition's `entireL_ne_zero_of_primeError_le` (*"eventually ≤ x^(β−1)"*);
  * Alpöge's tree's `zero_free_of_Chebyshev_growth`, *"for all large y"* (§4, **[read]** at `445`).

  The windowed idea shows on disk in one place: the compact edition's
  `IsPolar.exists_window_sub_mul_le` (`New/Endgame/OneSidedCriterion.lean`). It differentiates the
  transform `k` times under the integral (`iteratedDeriv k`) and bounds the moments to find some
  `u ∈ [t, t²]` with `E(u) − X E′(u) ≤ e^{−t}`, citing Pintz and Kaczorowski. Its docstring gives it
  another job: it *"replaces a pointwise prime number theorem in progressions when the second scale of
  (⋆) is chosen"*, that is, it picks the far scale `x₁`. It does not weaken the criterion's hypothesis. **[read]**

  There are two readings, and neither is settled. Either the agents' specialisation to `ζ` (refs 42–43)
  rearranges the argument, or Alpöge's tree has an intermittent step that `445`'s reading did not reach.
  The witness for "no Turán in the readable edition" is a grep for `Turán`, `Turan` and `Kaczorowski`
  over both editions' `.lean` files outside `.lake`. Its only hit is the compact file above. The grep
  did not cover Alpöge's tarball, which is cached in parts on this machine (§8.3) but not extracted.
* **Arakelov and Chebyshev, by name.** A grep for `Arakelov` over both editions' `.lean` files returns **zero files**. The sizes go by
  *heights*: `New/Reduction/Lattices/Heights`, and the compact `Heights` folder, which its guide puts
  in Theorem C (§9). That these are the article's *"Arakelov sizes"* is **[inferred]**. `Chebyshev`
  hits five readable files: `Lib/Analytic/Primes`, the two `Zeros` files, `Lib/Shimura/ThetaModuli/ThetaFamilyRigidity`
  and `New/Spanning/Bessel/CutTailBound`. None of them was read as a binomial squeeze, so no compartment
  is claimed for the squeeze. Stepanov is `New.stepanov_count`, in one file (§8.5).

| the article's part | compartment (§9.2) | grade |
|---|---|---|
| `ψ`/`G` equivalence; the zeros from a one-sided bound (the article's Landau–Turán step) | **endgame** (13 files; 126k tokens with its cone): the criterion, Landau's lemma, the twist that removes `n′`, PNT at the far scale | **[inferred]** that it plays that role; the mechanism differs (above) |
| the main estimate `G ≤ x^{1/2+ε}` and the choice of `m` | **reduction**: `star_inequality`, `Data.primeRemainder_le`, `eventually_exists_data` | **[read]** names and `m` |
| divisibility from composed lifts (Stepanov's vanishing order) | **Theorem A** (upper bound: *a composite lift*; derivatives of theta functions); **Theorem C** (one lift, the determinant, congruences and Selmer groups) | **[inferred]**, from §9.2's node names only |
| enough forms for the lifts to act on | **Theorem B** (`Spanning`) | **[inferred]**, node names |
| sizes against divisibility (Arakelov, covolumes) | the main inequality compares a covolume bounded above by A and B with one bounded below by C (§8.5); heights | covolume comparison **[read]**; "Arakelov" **[inferred]** |
| the ℤ[i]/CM theta prototype | background: *number fields, class field theory, CM* and *theta correspondence, Siegel–Weil*; *derivatives of theta functions* | **[inferred]** |

So, at the level of §9's names: the endgame compartment is the analytic half, the part the article
gives to Landau–Turán, and Theorems A, B and C hold the theta lifts.

### 10.5 A note on the word "multiplicity"

In the proof, *multiplicity* means **Stepanov's vanishing order**, which the chain of lifts turns into
**`p`-adic divisibility**: the article's `e_p` and the `p^{a+b}` of composed matrices. It is **not** the
multiplicity of the zeros of `ζ`, which this project's `NscStd` row and the `≈0.682` wall are about.
The proof uses that only as the sign `n(s) ≥ 0` of a residue (§8.5). §4's last bullet made the same
distinction for Alpöge's note. In these registers, plain *multiplicity* keeps the meaning `m(ρ)`. The
proof's sense is written *Stepanov multiplicity* or *`p`-adic divisibility*.
