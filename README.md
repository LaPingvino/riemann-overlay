# riemann — the overlay program, in Lean, run as a loop

**What this is.** A Lean 4 + Mathlib formalization of the *reduction structure*
of a program for raising the proportion of zeros of the Riemann zeta function
known to be simple and on the critical line. It is **not a proof of anything
about `ζ`**. The deliverable is a machine-checked map of which piece of
information composes with which, at what cost — and, as its largest part, the
theorems saying what a whole class of certificates *cannot* see (`MAP.md` §3).
The baseline it builds on is the vendored `zeta-23` development
(arXiv:2608.13637, Alpöge–Furman; `vendor/PROVENANCE.md`).

**How it was made.** The project was run as a standing loop by Claude
instances, with Joop as operator: one numbered session per cycle, every claim
routed to the fastest available *no* (the Lean kernel, a guard script, the
literature, a second instance), and every wrong expectation logged. The record
is the point as much as the theorems, and it is all here:

| read | for |
|---|---|
| [`METHOD.md`](METHOD.md) | how the loop is run — the rules, the two-row ledger, the anti-Goodhart defences, the guards |
| [`FRAMING.md`](FRAMING.md) | where it came from — the operator, the two instances, the seam between them, with a verification appendix |
| [`SURPRISES.md`](SURPRISES.md) | the calibration meter — every time the record went against a stated expectation, and who or what corrected it |
| [`CLAIMS.md`](CLAIMS.md) | every "no member of class `C` can do `X`" claim, graded A (certified) / N (numerical) / C (class undefined) |
| [`SESSION.md`](SESSION.md) | the numbered, append-only log of every cycle — the primary record |
| [`MAP.md`](MAP.md) | what the project has established, in one page, with a declaration name behind every claim |
| [`VERIFYING.md`](VERIFYING.md) | how to reproduce the build and check each headline claim yourself |

Further registers: `LOOP.md` (the rules R1–R33, authoritative over `METHOD.md`),
`ISSUES.md` (the friction), `FAILURES.md` (the census of dead routes and why
they died), `PRICES.md` (what each escape channel costs), `LEADS.md` (the hold
queue), `STATEMENTS.md`, `RULING.md`, `E.md`, `A.md`, `S.md`, `F.md`,
`NIGHT.md`. The history is deliberately left as it was written: older entries
carry stale numbers with dated corrections beside them rather than edits.

> **20 Nov 2026 — a claimed proof of RH.** Levent Alpöge has released a Lean
> development claiming the Riemann Hypothesis and GRH for Dirichlet
> `L`-functions. **[`COMPARISON.md`](COMPARISON.md)** says what it is, what a
> reproducible trust audit of it shows (`tools/trust_audit.py`), and what it
> would and would not change here. In one line: carried as a *hypothesis*
> (`Riemann/RH.lean`, never an axiom), RH moves the `Nsc` row from `50.88%` to
> `67.25%` and leaves the multiplicity side untouched.

## The ledger

Two rows, always reported together (`go run tools/proportion.go`):

| row | notion | certified | witness |
|---|---|---|---|
| `NscStd` | the literature's: multiplicity one, on the line (zeta-23's `N0simple`) | **67.25%** | `Riemann.certified_std` |
| `Nsc` | this project's stronger one: the ordinate carries nothing else (`H = 1`) | **50.88%** | `Riemann.certified_nsc_unconditional` |
| `Nsc`, conditional on RH | the same, under the hypothesis `h : RiemannHypothesis` | 67.25% | `Riemann.proportion_of_RH_zeta` |

Both certified rows are unconditional: their axiom cones contain only Lean's
three standard axioms (`axioms: 0` in `PROPORTION.log`). The trusted base,
`Riemann/Assumptions.lean`, declares **six** axioms, each with its source in a
docstring, and none of them is in either row's cone; they feed only conditional
routes (`MAP.md` §1, `forensics/board.py --cones`). Open problems are never
axioms — they are `Prop`s in `Riemann/Gaps.lean`, carried as hypotheses.

`audit/regression/Boom_2026-08-13.lean` is a **negative** test: it derived
`False` from an early version of the axioms and must never compile again
(`ISSUES.md` #8; `tools/proportion.go` exits `5` if it does).

## The Lean

```
Riemann/Basic.lean        H(γ), N⊛, Prop 1, N + N_off ≤ N⊛     axiom-free
Riemann/Transfer.lean     (★) ⟹ proportion 2 − C               axiom-free
Riemann/Fujii.lean        the numeric window for [OPEN 0]      axiom-free
Riemann/Gauge.lean        NscStd is not gauge-invariant        axiom-free
Riemann/Blindness.lean    no μ_T-invariant hypothesis computes axiom-free
                          NscStd or N_off
Riemann/Fiber.lean        the blindness is supported exactly   axiom-free
                          on the crowded atoms
Riemann/Zeta.lean         zetaZeroData, built from zeta-23     axiom-free
Riemann/Gaps.lean         one Prop per open problem            definitions
Riemann/Assumptions.lean  every axiom, with its source         trusted base
Riemann/Program.lean      the §6 arrows                        from the axioms
Riemann/Proportion.lean   the fitness function                 certified vs conjectural
Riemann/Capacity.lean     rung 0: no gain past the known range axiom-free
Riemann/Optimal.lean      Proposition 1 is LP-optimal          axiom-free
Riemann/RH.lean           what RiemannHypothesis buys,         axiom-free besides
                          carried as a hypothesis              the hypothesis h
```

## Build

```bash
lake exe cache get                       # Mathlib oleans for the pinned rev
lake build                               # ~8900 jobs cold
lake env lean audit/PrintAxioms.lean     # axiom cones of the claimed theorems
lake env lean audit/Declarations.lean    # every name the registers cite must exist
go run tools/proportion.go               # the ledger (also runs the guards)
python3 forensics/session_gate.py        # the full guard roster
```

Toolchain `leanprover/lean4:v4.33.0-rc2` (`lean-toolchain`); every dependency
is pinned by exact revision in `lake-manifest.json`. `VERIFYING.md` has the
details, including the exit codes of `tools/proportion.go`.

## The explorer of Alpöge's release

**<https://lapingvino.github.io/riemann-overlay/>** is a browsable map of the
released Lean (`COMPARISON.md` §1), built **only from that Lean**, so it can be
set beside the author's write-ups as they appear. It opens on the five theorems
of `src/Main.lean`; each node shows its kind, name, file and line and the size of
what lies under it, and lists the declarations its statement and its proof use,
down to the edge of Mathlib, where it stops and names (and links) the Mathlib
declaration. A name search finds any node.

* **The edges are `[parsed]`, not `[elaborated]`.** `tools/explorer` reads the
  source: the identifiers each declaration mentions, resolved through
  namespaces, `open`s and imports against the tree's own names and then the
  pinned dependencies' names. It misses what the elaborator adds unnamed
  (instances, `simp` sets, coercions, notation, tactic-built terms) and can add
  a spurious edge for a local binder that shares a declaration's name. No build
  of the tree was done; the page says the same.
* **Statements and docstrings are withheld**, because the tarball carries no
  `LICENSE` or `README`; the generator's `-statements` flag switches them on.
  The page credits the release and links <https://alpo.ge/> and the note.
* **The data is regenerated by `.github/workflows/explorer.yml`**, which
  streams the fourteen parts through `gzip | tar`, checks the SHA-256 against
  `COMPARISON.md` §7 and refuses to publish on a mismatch, and writes only JSON
  shards under `explorer/data/` (not tracked). Locally:

  ```bash
  go -C tools/explorer run . -out ../../explorer/data     # fetches and streams
  python3 -m http.server -d explorer                      # then open :8000
  ```

## Licence

Code (Lean, scripts, build files) is Apache-2.0 — [`LICENSE`](LICENSE). The
prose registers (the Markdown files outside `vendor/`, and `PROPORTION.log`) are
CC BY 4.0 — [`LICENSE-docs`](LICENSE-docs) lists the files. `vendor/zeta23`
keeps its own Apache-2.0 `LICENSE` and `NOTICE`.
