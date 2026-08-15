#!/usr/bin/env python3
"""The λ-sweep window optimisation — the computation behind LEADS.md's table.

ISSUES #29 recorded this table as having no code in the repo, and guessed the
repair would need the source paper.  **That diagnosis was wrong.**  The
specification was in `LEADS.md` all along, three lines above the table itself:

    for fixed λ, maximising  c(λ,v) = λ(∫v)² / (∫v² + λ²∬|s−s'|v v')  over v
    is a linear solve —  M v = a,  a = h·1,  M = h·I + λ²h²K,  K_ij = |s_i−s_j|,
    optimum value  c*(λ) = λ · aᵀ M⁻¹ a.   N = 160.

and the reported proportion is `2 − 1/c*(λ)`.  That is a complete
specification: functional, discretisation, and linear algebra.  Writing this
file is transcription, not reconstruction from memory — the distinction the
#29 note leaned on, applied correctly this time.

Verified against every value the register quotes; see `check()`.

**SESSION 120:** the check list originally held two of the sweep's five rows,
which let `CLAIMS.md` keep grading the sweep "code not in repo" long after `#29`
was resolved.  All five rows are now checked, and all five reproduce to seven
digits.
"""

import numpy as np


def cstar(lam: float, N: int = 160) -> float:
    """Optimum of `c(λ,v)` over all windows, by the register's linear solve.

    `N = 160` midpoint quadrature on `[0,1]`, ζ-case kernel `D(s) = s`.
    """
    h = 1.0 / N
    s = (np.arange(N) + 0.5) * h
    K = np.abs(s[:, None] - s[None, :])
    M = h * np.eye(N) + lam**2 * h**2 * K
    a = h * np.ones(N)
    return lam * a @ np.linalg.solve(M, a)


def proportion(lam: float, N: int = 160) -> float:
    """The certified proportion the container yields at `λ`: `2 − 1/c*`."""
    return 2.0 - 1.0 / cstar(lam, N)


# (λ, c*(λ), 2 − 1/c*) exactly as printed in LEADS.md's λ-sweep.
REGISTER = [
    (0.75, 0.6325448, 0.4190843),
    (1.00, 0.7533028, 0.6725126),
    (1.25, 0.8299265, 0.7950740),
    (1.50, 0.8728770, 0.8543632),
    (2.00, 0.8995905, 0.8883831),
]

# Montgomery–Taylor's closed form, for the λ = 1 identification.
MT = 1.5 - (1 / np.sqrt(2)) * (np.cos(1 / np.sqrt(2)) / np.sin(1 / np.sqrt(2)))


def check() -> bool:
    ok = True
    print("λ-sweep, reproduced from the register's own specification")
    print("  λ      c*(λ)        register     2−1/c*       register     match")
    for lam, c_reg, p_reg in REGISTER:
        c, p = cstar(lam), proportion(lam)
        good = abs(c - c_reg) < 5e-7 and abs(p - p_reg) < 5e-7
        ok &= good
        print(f"  {lam:<6.2f} {c:<12.7f} {c_reg:<12.7f} {p:<12.7f} {p_reg:<12.7f} "
              f"{'OK' if good else 'MISMATCH'}")
    print(f"\n  Montgomery–Taylor closed form 3/2 − (1/√2)cot(1/√2) = {MT:.7f}")
    print(f"  optimum at λ = 1                                      "
          f"= {proportion(1.0):.7f}")
    print(f"  gap = {proportion(1.0) - MT:.3e}  (quadrature error at N = 160)")
    print(f"\n  => {'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    raise SystemExit(0 if check() else 1)
