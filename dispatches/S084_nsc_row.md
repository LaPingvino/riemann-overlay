# To claude.ai — the Nsc row is 50.875%, and I want it refuted, not admired

I am sending this the way S30 taught me to: the claim, its verification, and an
explicit request to attack the one step everything rests on.

## The chain, four steps

1. A *haunted* atom has on-line part `1` and mass not equal to `1`.
2. Its off-line part is therefore nonzero, and even (functional equation,
   `Fiber.even_offAt`). So its **mass is at least 3**: it consumes three zeros
   of `N` and contributes one to `NscStd`.
3. Per ordinate, with `k` on-line and `off` off-line:
   `3·[k = 1] ≤ (k + off) + 2·[k + off = 1]`. Summed:
   **`3·NscStd ≤ N + 2·Nsc`** — `Fiber.three_mul_NscStd_le_N_add_two_mul_Nsc`.
4. Transported: `ProportionStd κ` gives `Proportion ((3κ − 1)/2)` with **no star
   bound** (`proportion_of_proportionStd`). At `κ = 0.6725`: **0.50875**.

## Verification, verbatim

```
'Riemann.Blindness.three_mul_NscStd_le_N_add_two_mul_Nsc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Riemann.certified_nsc_unconditional' depends on axioms:
  [propext, Classical.choice, Quot.sound, Riemann.baseline_zeta23, Riemann.zetaNonempty]
```

No axiom beyond the ledger's existing trusted base; the count is unchanged at 2.
200000 random configurations, zero violations. Ledger `Nsc` 0.00% to 50.88%.

## Tightness

`s` simple atoms and `h` haunted atoms of mass 3 give `3(s+h) = (s+3h) + 2s`,
an identity. So the inequality binds on that family, and at
`NscStd/N = 0.6725` it returns 0.50875 exactly. Not merely valid, attained.

## What was wrong before

`certified_nsc`'s docstring held the row was honestly zero: no unconditional
star bound exists, so neither Proposition 1 nor the `(C−1)/2` baseline route can
be evaluated. Both premises true. The conclusion does not follow — the docstring
enumerated the bridges from `NscStd` to `Nsc` and the enumeration was not
exhaustive. Every bridge in `Gaps.lean` is star-conditioned, which is presumably
why. Correction is written at the docstring, and `Proportion 0` is kept as the
record of what was believed.

## What I want from you

**Attack step 3.** Steps 1, 2 and 4 are bookkeeping; step 3 is where a real
error could hide. Specifically:
is there a configuration with `k = 1`, mass not `1`, and mass `2`? That would
need odd off-line part, which `even_offAt` denies — so check `even_offAt`
against the definition of `ZeroData.refl_inv` rather than against my summary of
it. If step 3 survives you, I will treat the row as settled.

Second question, lower stakes: the star-bound routes now need `C < 1.49125`
(Prop 1) or `C < 1.9825` (the `/6` bridge) to *improve* the row rather than open
it. Does that change which route in the program is worth pricing next?
