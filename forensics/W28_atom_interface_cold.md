# W28 — the `Atom` interface, drafted cold

**Protocol.** Written by the context-v2 operator from `Riemann/Basic.lean` and
`Riemann/Program.lean` only, before re-reading `E.md` (so before E22's
discussion) and before `A.md`. The two model checks were the whole spec:
**must instantiate over function fields**, **must fail on Davenport–Heilbronn**.
Sealed before the E-register is opened.

---

## 1. What the repo currently assumes about zeros, and why it is not enough

`ZeroData` has exactly two fields: a finite multiset `Z ⊆ ℝ × ℝ` and
`refl_inv : Z.map refl = Z`. That is *the functional equation and nothing
else*. Every theorem in `Basic.lean` — `prop1`, `two_NscStd_le`,
`six_mul_NscStd_le`, `H_eq_online_add_two_mul`, `card_odd_atoms_le_critical` —
is therefore a theorem about **any** reflection-symmetric point multiset.

This is the interface's starting point and its indictment: **Davenport–Heilbronn
is a `ZeroData`.** It has the functional equation, it has a Dirichlet series, it
has infinitely many zeros off the critical line. Everything we have proved
axiom-free is true of it. The combinatorial core cannot be the place where RH
enters, and the `Atom` structure is the name for what must be added.

Symmetrically, `Assumptions.lean` currently adds the missing content as nine
opaque constants about `ζ` specifically. That is the other failure mode: not too
weak to distinguish, but too specific to be an interface at all.

## 2. The design decision: two disjoint bundles, not one

The census already tells us the fields do not form one family. The deaths split
by which nature of the prime they consumed:

* deaths that consume **multiplication** — the Euler product, unique
  factorisation, the nonnegativity of `Λ`. `#3` ("only the Euler product
  bites") is explicit about it.
* deaths that consume **the sieve** — bilinear decompositions, levels of
  distribution, short-interval equidistribution. `#11`, the gate, is exactly
  here: MRT is a sieve-nature theorem and the bridge asked it for a
  power saving it cannot give.

So `Atom` carries **two bundles that are never mixed**, and the payoff of the
type is that every theorem declares which bundle it consumes in its signature.

```
structure AtomSystem where
  A        : Type*                       -- the atoms
  norm     : A → ℝ                       -- ‖a‖ ≥ 2
  one_lt   : ∀ a, 2 ≤ norm a

-- Bundle M (multiplicative nature)
structure Multiplicative (S : AtomSystem) where
  freeMonoid   : ...      -- the objects are the free commutative monoid on A;
                          --   equivalently: unique factorisation holds
  weight       : S.A → ℝ  -- Λ, supported on atom powers
  weight_nonneg: ∀ a, 0 ≤ weight a
  euler        : ...      -- the Dirichlet series factors over A on Re s > 1
  explicitForm : ...      -- pairing: Σ_zeros φ̂(γ) = main − Σ_a Λ(a) φ(log ‖a‖) + …

-- Bundle S (sieve nature)
structure Sieve (S : AtomSystem) where
  typeI        : ...      -- level of distribution θ: Σ_{q ≤ x^θ} max_error ≪ x/(log x)^A
  typeII       : ...      -- bilinear forms in the Vaughan/Heath-Brown ranges
  shortInterval: ...      -- equidistribution in [x, x + x^δ], the MRT regime
  savingShape  : Shape    -- ‹power› | ‹logPower› — the quality, as data
```

`savingShape` is a field and not a hypothesis on purpose: `#27` died because a
consumer needed `power` and the supplier had `logPower`, and the mismatch was
invisible until the arithmetic was done by hand. As a field it is a type error
at the interface, which is W33's whole thesis applied to the one place it has
already cost us a headline.

## 3. The model checks

| model | atoms | bundle M | bundle S | RH | verdict |
|---|---|---|---|---|---|
| `ζ` | rational primes | ✓ | ✓ (θ = 1/2 unconditional) | open | the target |
| `F_q[t]` | monic irreducibles, `‖a‖ = q^{deg a}` | ✓ | ✓ | **true** (Weil) | **must instantiate** |
| Davenport–Heilbronn | — | **✗** | ✗ | **false** | **must fail** |
| Beurling systems (DMV) | abstract multiplicative semigroup | ✓ | **✗** | **false** | *the separator* |

**Davenport–Heilbronn fails M, as required.** Its Dirichlet coefficients are
not multiplicative, so the free-monoid field has no witness and `Λ` is not
nonnegative. This is the check that says the interface has content beyond
`ZeroData`.

**Function fields instantiate both**, and cheaply: the monoid is free by
construction, `Λ ≥ 0`, and the sieve bundle is available with the best possible
quality. If the interface cannot be instantiated here it is wrong.

**And the third row is the one the cold draft actually adds.** Beurling
generalised prime systems have the full multiplicative nature — free monoid,
`Λ ≥ 0`, Euler product, explicit formula, even PNT — and RH fails for them
(Diamond–Montgomery–Vorhauer). They satisfy bundle M and have **no bundle S at
all**, because there is no additive structure in which to state a level of
distribution.

So the model table proves the bundles are independent, and it does it with two
counterexamples pointing in opposite directions:

> **DH says the functional equation alone is not enough. Beurling says the Euler
> product alone is not enough either.** Any route to RH must consume bundle S
> somewhere, and therefore *must* pass through a level-of-distribution or
> bilinear input.

That is not a slogan — it is a constraint on the program's route table. Route I
(Fujii's constant) and Route III (narrow box) are both stated in bundle-M
language in `Program.lean`. If the Beurling reading is right, neither can close
alone, and the arithmetic input `#27` failed to buy is not one option among
several but the mandatory field.

## 4. What this predicts, falsifiably

1. Every `Assumptions.lean` constant is classifiable into M or S. If any is
   genuinely M-only *and* would suffice for a positive proportion past the
   ceiling, the Beurling argument above is wrong and I want to know which.
2. `Basic.lean` stays entirely outside both bundles — it is `ZeroData`-only, and
   should remain so. The atom structure must not leak into the combinatorial
   core; the core's value is precisely that it holds for DH too.
3. The `{4,7,8}` cluster from the tri-read — what the functional cannot see —
   should be provable as a theorem *about* `ZeroData`, i.e. an inability that
   survives adding either bundle. That is a Lean-checkable prediction and the
   cheapest next W28 item.

**Might-mean:** if the two bundles are independent in the sense the model table
shows, then the project's route table has been shopping in one aisle, and every
death that looked like bad luck at the gate was the interface telling us the
mandatory field was empty.
