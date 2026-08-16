# F — the fictions

A fourth register, commissioned by Joop and written by claude.ai. **F-items are
derivations that do not exist, narrated as if they did**, each extrapolated from
a route the project has already walked.

A fiction's function is to **name its missing cast precisely** — the objects
that would have to exist for the story to compile. The cast list is a want-ad
the baskets can hire against.

**Protocol.** Fictions cannot be true or false, only **castable**. Annotate when
a cast member is found (cite the finding); promote to `W` when the cast is
complete; **never kill** — a fiction whose cast is proven *impossible* converts
to a **rung**, because the impossibility is a ceiling theorem (`E11` brick,
`R21`-certified if closure is proved).

The register's standing observation: every fiction is a known route driven one
theorem past its terminus, so List F is the project's want-ad section. Per the
iron law, expect two of ten casts to be already employed elsewhere under names
we have not met.

---

## Status board

| # | fiction | status |
|---|---|---|
| F1 | the strip kernel | open, cast named |
| F2 | the Hausdorff route | open, cast named |
| F3 | the flow entropy | open, cast named |
| **F4** | **the smoothed gate** | **CONVERTED TO A RUNG — kill condition fired, see below** |
| F5 | the resonance comb | open; **absorbed F4's live remnant** |
| F6 | the q→1 tightrope | open, no direct spawn |
| F7 | the machine-found invariant | open, = W15 narrated |
| F8 | the self-verifying tail | open, W34b gains a second question |
| F9 | the fingerprint theorem | open, = T4 upgraded in motivation |
| F10 | the Möbius pairing | open, fastest-killable |
| — | *second shelf: the wild ones* | — |
| F11 | the laboratory Hamiltonian | open; sober shadow = a cast-list audit of the regularization literature |
| F12 | Shor reads the ledger | open; sober shadow **already partly employed** (iron-law exempt) |
| F13 | infinite descent on crowds | open; sober shadow asks a question the registers never posed |
| F14 | the proof was in the weights | open; sober shadow = W15 aimed at concepts |
| **F15** | **almost-RH first** | open, **but its cast analysis is wrong — see correction** |
| F16 | the renormalization conjugacy | open; sober shadow = a finite read |
| F17 | the negative literature | open; sober shadow **already partly employed** (iron-law exempt) |
| F18 | the thermodynamic terminus | open; wish written as physics, one real spawn |

---

## F4 — the smoothed gate. **Kill condition fired on the register's own record.**

**The fiction:** the gate's power-requirement is an artifact of sharp cutoffs;
rerun the GM chain with Cesàro-weighted shift averages instead of the sharp
`Σ(h−|k|)` window, per-shift amplification drops from `h` to `h^ε`, log-power
suffices, MRT walks across at `θ = 8/33`.

**Its own kill condition, as filed:** *if the amplification is intrinsic, the
gate is confirmed load-bearing and the fiction dies having verified the wall.*

**It fired, twice over, and neither check needed a paper.**

**(1) The premise is already false in the record.** `ISSUES` #27 states the
bridge's weight as `Σ_{|k|<h}(h−|k|)·[Λ-correlation at shift k]`. **`(h−|k|)`
*is* the Fejér/Cesàro weight.** The smoothing the fiction proposes adding was
present in the derivation from the start; there is no sharp window to replace.

**(2) And no weight of any shape can help.** With only per-shift *absolute*
bounds `|E_k| ≤ E`, the total error is

> `Σ_k w_k |E_k| ≤ E · Σ_k w_k = E · (total mass)`

and the **main term fixes the total mass at `≈ h²` for every admissible
weight**. Fejér, flat and Gaussian weights were checked numerically: same total
mass, therefore the same `h²E`, whatever their sup or shape. The amplification
is a property of *bounding each shift separately*, not of the window's profile.

**CERTIFIED (next cycle):** the prose argument is now backed by
`Capacity.reweighting_worst_case` / `weighted_sum_le_mass_mul` /
`equal_mass_equal_worst_case`, axiom-free — the worst case `(Σw)·E` is
*attained* by the adversary who sets every error to `E`, so equal-mass weights
admit equal worst cases and shape is irrelevant. F4's rung has its `R21`
certificate and is grade **A**.

**So the gate is confirmed load-bearing, and per the F-protocol F4 converts to a
rung**: the class of *shape-modified* GM bridges cannot cross with log-power
input. Sharpening the census's `#27` from "MRT is too weak" to **"no
reweighting of the GM identity can be strong enough"**.

**The live remnant, and it is not smoothing.** The one escape the argument
leaves open is **cancellation between shifts** — replacing per-shift absolute
bounds with correlated control, so the errors do not simply add. That is not a
window question. **It is exactly the cast `F5` already names** (a large-sieve
inequality for correlated errors), and F4's remnant is absorbed there rather
than kept as a separate item.

*Scope, stated: this is an argument about the recorded derivation, not a Lean
theorem, and the recorded derivation is itself `[RECALL]` from Goldston's survey
§9. If that derivation is misrecorded, this conversion inherits the error.*

---

## The other nine, as filed

**F1 — the strip kernel.** Cast: a positive-definite kernel on `ℝ × [0,1]` with
functional-equation symmetry, whose diagonal restriction is M–T/Cohn–Elkies and
whose off-line evaluation norms are certifiable unconditionally. Spawn: ask the
dLRTW SDP machinery whether "kernel on `ℝ`" generalises to the strip. *Note: our
`landau_discriminates` is the one-point version of the off-line evaluation the
cast needs — the fiction's hardest member has a proved special case.*

**F2 — the Hausdorff route.** Cast: uniform-in-`k` constants in Fujii/Tsang,
plus a determinacy argument tolerant of the `o(1)`s. Reframes W19: not "does the
4th moment help" but **"what is the moment-determinacy threshold"** (Carleman
conditions), a known genre never asked of `S(t)`. *Note: `SESSION 061` proved
the third moment cannot help via `Σm(m−1)(m−2) ≥ 0`; F2 should be read as asking
whether the full sequence does what no finite prefix can.*

> ⚠️ **ANSWERED at inequality grade (2026-08-15).** It does not.
> `Optimal.moment_route_walled` (axiom-free): both witnesses forcing `prop1`'s
> optimum have **every** factorial moment of order `≥ 3` equal to zero, so no
> moment inequality of any order can exclude them — a constraint tight on the
> binding witness cannot move the bound. **What survives F2 is equality-grade
> only:** recovering the mass distribution needs asymptotic *identities* for the
> moments (Fujii-with-main-terms), a different supply chain. Re-filed at that
> grade and no higher.

> ⚠️ **SESSION 143 — the supply chain is now priced, and it is narrower than
> "main terms".** `forensics/w19_price.py` measures what the ledger's own
> quantity does to an S-moment: a haunted (mass-3) atom moves `∫S²` by exactly
> `2δL`, a term with **no `log log T`**. Fujii's main term carries `log log T`.
> So a moment identity is useful to `hauntedCount` iff its ERROR term is `o(T)`
> — the main term is the wrong part of the expansion to want. F2's cast gains a
> named member: *an S-moment asymptotic with error `o(T)`, uniformly*.
>
> **Not claimed:** that Selberg's CLT is this supply. F2 wants moments of the
> MASS distribution; these are moments of `S`. They meet only at sub-leading
> order, and that scale gap is the wall — calling them one object would be the
> `S30` shape.

**F3 — the flow entropy.** Cast: the Lyapunov functional (E5m's named gap), its
monotonicity, and — the hard member — arithmetic evaluability at `t = 0`. Spawn:
read Csordas–Smith–Varga's Lehmer-pair machinery as inequalities *on a
functional*, and ask what quantity they are the derivative of.

**F5 — the resonance comb.** Cast: uniform Landau–Gonek with **correlated**
error control across a comb `x = x₀^{(1+ε)ⁿ}` — a large-sieve inequality for
Landau sums, which does not exist — plus off-target decoherence. **Now also
carries F4's remnant.** Spawn: probe whether any large-sieve-for-zeros
literature bounds correlated Landau errors. *Note: `w16_price.py` already
established the binding constraint is the phase; this fiction is that constraint
with a proposed instrument.*

**F6 — the q→1 tightrope.** Cast: the interpolating family (`F₁`-adjacent,
Deninger-adjacent) plus a rigidity principle carrying `offAt ≡ 0` along it. No
direct spawn; filed so W36's function-field audit knows what the fiction needs
the proven case to supply.

**F7 — the machine-found invariant.** Cast: W15's run, a feature-extraction
pass, the iron-law lookup. Records the *prediction* that any found feature will
be pre-existing — which makes even its failure mode informative.

**F8 — the self-verifying tail.** Cast: weak-system independence for
witness-location statements (W34c's target) spliced with finite verification.
Gives W34b a second question: **has anyone proved witness-location independence
for any `Π₁` number-theoretic statement in any fragment?**

**F9 — the fingerprint theorem.** Cast: T4 run, the pattern-statistic
formalised, and the transfer lemma. Must be found **blind** per R19 or it is the
classifier again.

**F10 — the Möbius pairing.** Cast: the dictionary `α = 1/(1−θ)` as a
transformation on test-function space rather than on parameters, plus the
symmetrised certificate class. One whiteboard hour; the fastest-killable item on
the list.


---

# Second shelf — the wild ones (F11–F18)

Fictions past the castable horizon, each carrying its **sober shadow**: the real
spawn even an impossible fiction casts. Filed as received. The shelf's function,
per E13: the castable fictions recruit for the baskets; **the wild ones
calibrate the register itself**, marking where the want-ad vocabulary runs out.

Shelf protocol: wild fictions are exempt from the two-in-ten iron-law
prediction, **except F12 and F17**, where the sober shadows are near-certainly
already partly employed.

## F15 — correction to its cast analysis, from our own theorem

F15 argues that finiteness of off-line zeros is *"immune to the blindness
theorem because finiteness is not a `μ_T` statement."*

**That is wrong, and the counter-witness is `Fiber.ledger_visibility_split`.**
Finiteness of off-line zeros is a statement about `N_off`, and `N_off` is
**one of the two ledger components proved *not* to be a `μ_T` functional** — the
other being `NscStd`. Far from being immune, a finiteness target sits squarely
on the invisible side of the split.

**This makes F15 harder than advertised, not easier.** Its wedge was supposed to
be that a weaker goal dodges the obstruction; the obstruction applies to the
weaker goal at full strength. What survives is the second half — Bombieri's
exactness clause converting finiteness to zero — which the census has indeed
never treated as a target's second half, and which is unaffected by this
correction.

*Recorded here rather than in a reply, because F-items are annotated when a cast
member is found — and this is a cast member found to be missing.*

## The other seven, as filed

**F11 — the laboratory Hamiltonian.** Cast: arithmetic boundary conditions (the
Hilbert–Pólya gap), an identity theorem, and the wild member — that a physical
system's self-adjointness could be argued from its constructibility. **Sober
shadow:** read Berry–Keating, Connes, Bender–Brody–Müller as a *cast-list
audit* — which member is each attempt missing. That is a real W30-style table.

**F12 — Shor reads the ledger.** Cast: F5's large-sieve inequality reincarnated
as a decoherence bound, plus qubit counts three decades out. **Sober shadow, and
it is the mathematical content:** period-finding and the explicit formula share
the same exponential sum, and **no census entry has priced that dictionary**.
One read of the (small) quantum-computing-meets-L-functions literature to check
whether any certified statement crosses.

**F13 — infinite descent on crowds.** Cast: a mass-transport map with no known
analogue; heights are not usefully well-ordered and the "same invariants" clause
does impossible work. **Sober shadow — a question the registers never posed:**
is there *any* partial order on configurations under which the certified
inequalities are monotone? Even a failed search defines the order-theoretic
structure of configuration space, which W28's interface wants anyway.

**F14 — the proof was in the weights.** Cast: interpretability at a fidelity
that does not exist, plus the leap from representation to theorem. **Sober
shadow:** W15 pointed at *concepts* rather than data — if E20's plane is visible
in a strong model's embedding geometry, that is a measurable fact about the
literature whatever it says about `ζ`.

**F16 — the renormalization conjugacy.** Cast: the conjugacy (the E-register's
most-wanted object), the rigidity, and a cohomological accounting that is pure
invention. **Sober shadow:** T5's inventory plus W27's T3.4 — the mesoscopic-limit
theorems read for *what invariances they transport*. A finite read.

**F17 — the negative literature.** Cast: archive access, extraction at scale,
and the transfer lemma the demon still guards. **Sober shadow, real at pilot
scale:** the Nachlass literature — Siegel mining Riemann's own notes into the
Riemann–Siegel formula is the field's proof that negative literature contains
positive theorems. A W26 annex, fundable as history of mathematics.

**F18 — the thermodynamic terminus.** Cast: everything. **Sober shadow, and the
honest note is the register's own:** this is W∞'s wish written as physics. Its
one real spawn is *"is census information-content measurable at all"* — which
T2's null already began answering: yes, and the first measurement was of
ourselves.
