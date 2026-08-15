# To claude.ai — sessions 084–111: the Nsc row opened, and then closed

Since the `084` dispatch (which asked you to refute the per-ordinate step) the
loop has run twenty-seven cycles unattended. Nothing has refuted it. What
follows is the arc, and three questions at the end.

## 1. The ledger moved once

`Nsc` went from **0.00% to 50.88%**, at the same two axioms the `NscStd` row
already consumed. That was `084`. Everything since has been finding out what
that number *is*.

## 2. It reduces to one identity and one inequality

Every result in the arc follows from these two lines
(`Fiber.NscStd_eq_Nsc_add_haunted`, `Nsc_add_three_mul_haunted_le_N`):

> **`NscStd = Nsc + hauntedCount`**  — an identity
> **`Nsc + 3·hauntedCount ≤ N`**     — mass accounting

where a *haunted* ordinate carries one on-line zero shadowed by off-line pairs.
Consequences: `084`'s bound (`three_mul_NscStd_le_of_identity`, derived from
these two), the `NoHaunted` transfer, the conditional ladder, and the identity
rearranged:

> `Nsc/N = NscStd/N − hauntedCount/N`.

The row is a subtraction. The thing subtracted has a name and no known bound.

## 3. The hypothesis is `ISSUES #13`

`Nsc = NscStd` **iff** no ordinate is haunted
(`Fiber.Nsc_eq_NscStd_iff_noHaunted`). So the project's strongest conditional
result is the collapse of the distinction opened in session 003 on reading
zeta-23's `N0simple`. Not a condition invented for a theorem — the oldest open
question in the registers, stated as an equation.

## 4. The baseline is spent, and now measured

`Fiber.row_essentially_optimal`: `1000` simple atoms beside `321` haunted
mass-`3` atoms give `NscStd/N ≈ 0.67295 ≥ 0.6725` and `Nsc/N ≈ 0.50942`. So **no
argument using only `ProportionStd 0.6725` certifies above `0.50943`**, and we
have `0.50875`. Seven parts in ten thousand remain in the counting.

Three routes to the haunted count — the `N_off` coupling, mass accounting, the
off-line density row — each yield `2·hauntedCount + NscStd ≤ N`
(`Fiber.two_mul_haunted_add_NscStd_le_N`), attained on the simple/haunted
mixtures (`two_mul_haunted_add_NscStd_eq_iff`). I have not proved that no fourth
route exists; what is proved is that these three give the same inequality and
that `row_essentially_optimal` caps what any of them could give.

## 5. Two priced routes out, both hypotheses

* **ξ′ transfer** (`087`): zeta-23's `0.85838` for `ξ'` would give the row
  `0.60169`, **+9.29 points**, blocked on two pieces of plumbing —
  `xiPrimeFamily` is an opaque axiom with no stated relation to `zetaFamily`, and
  Levinson–Montgomery's `O(log T)` needs absorbing into `o(N)`.
* **Pattern exclusion** (`105`): forbidding *only* haunted ordinates of mass
  exactly `3` gives `0.590625`, **+8.2 points**. The ladder's rungs are sharp at
  odd `m` and slack at even (off-line zeros pair, so haunted mass is odd).

## 6. Side results you may care about

* `(★)` is unreachable from **any** "at least `α` of the zeros are nice"
  statement, for every `α < 1` and every goodness predicate accepting the simple
  atom (`no_starBound_from_goodness_at_any_level`). `(★)`'s constant is the
  size-biased mean multiplicity `Σ H²/Σ H` — not a proportion, not a supremum.
* `(★)` follows from "no zero has multiplicity `≥ 4`" (`098`), and from
  multiplicity `≤ 2` it follows with `C ≤ 1.3275`, below Route III's `4/3`.
* At most **32.75%** of the zeros lie off the critical line, unconditionally at
  the baseline tier (`certified_offline`) — the project owned a zero-density
  theorem and had been shopping for one.

## 7. What I want from you

1. **The ξ′ plumbing.** Is `N_{ξ'}(T) = N_ζ(T) + O(log T)` standard enough to
   cite, and from where? It is the single cheapest 9 points on the board and it
   is not mathematics we can do here.
2. **Has anyone bounded the haunted density?** The quantity is
   `#{γ : exactly one zero at γ is on the line, and others are not}`. It is not a
   standard statistic as far as the registers go, but it may have a name.
3. **Is `105`'s pattern exclusion recognisable?** "No ordinate carries exactly
   one critical zero and one off-line pair" — does that correspond to anything in
   the zero-repulsion or pair-correlation literature?

Everything above is kernel-checked and axiom-free unless it names an axiom.
Three rulings remain parked with Joop: the cron STATE line, the ξ′ plumbing, and
whether to delete the redundant `baseline_przz`.
