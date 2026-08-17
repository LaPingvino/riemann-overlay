# zeta-23, vendored

**Ruled by Joop, `SESSION 231`.** `ISSUES` `#28(a)`'s second half — *"no vendored
copy of zeta-23"* — closed here.

| | |
|---|---|
| upstream | `https://github.com/anthropics/zeta-23-lean` |
| commit | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |
| tree hash | `c9baf0ab3555bc7e1a66fb5ab4735ab425c64f3fcef5c29e13c8d84a0c1e2fd5` |
| files | 341 |
| copied from | `.lake/packages/zeta23` at that commit, working tree clean |
| **published tag** | **`v1.0` — identified at `SESSION 357`** |

## The pin is the published version (`SESSION 357`)

`arXiv:2608.13637` (Alpöge–Furman, 13 Aug 2026) is this artifact's paper, and it
speaks of *"the cited repository tag (`v1.0`)"*.  `357` checked whether our pin is
that tag: `https://github.com/anthropics/zeta-23-lean/commits/v1.0` lists the ref's
history newest-first, and **its top entry is `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`**
— the commit above.

So the chain is complete in both directions:

* `forensics/vendor_check.py` verifies `vendor/zeta23` is byte-identical to the pin,
  every cycle;
* the pin is the tip of `v1.0`;
* `v1.0` is the tag the published paper cites.

**Method, stated so it is not over-read.** This is GitHub's rendered ref history, not
the git object database — no clone was made and no tag object was inspected.  What it
establishes is that the `v1.0` ref's newest commit is our pin at the time of checking.

**One consequence worth carrying.** The paper's statement that *"at the cited repository
tag (`v1.0`), the enclosures `EnclOK` are certified by interval arithmetic and are not
checked by the Lean kernel"* therefore describes **this** tree, not a neighbouring
version of it.  `PRICES.md`'s rung-0 note is about our own `vendor/zeta23`.

The tree hash is `sha256` over the sorted relative paths and the `sha256` of each
file's bytes; `forensics/vendor_check.py` recomputes it. Build outputs
(`.lake/`, `*.olean`) are excluded from both the copy and the hash.

This file sits **outside** `vendor/zeta23` on purpose: the mirror stays
byte-identical to the upstream commit, so the hash checks that property and not
a property of our own annotations.

## What this removes

The build no longer reaches the network for zeta-23. `lake build` compiles
`vendor/zeta23` in place — verified by deleting `.lake/packages/zeta23` and
rebuilding green, with no clone recreated.

Both pin-bearing files were changed together:

* `lakefile.toml` — `[[require]] name = "zeta23"` now carries `path`, not `git`
  and `rev`.
* `lake-manifest.json` — the `zeta23` entry is `type: "path"`, `dir:
  "vendor/zeta23"`, edited **by hand**, which is the same technique `#28(a)`'s
  first half used to align `inputRev`. `lake update` was not run; the standing
  instruction against it is intact.

**Changing only the lakefile does nothing.** `SESSION 231` tried that first: the
manifest's `git` entry won, lake re-cloned zeta-23 from GitHub at the pinned
commit, and the build went over the network while looking green. The manifest is
the authority for an already-resolved dependency.

## What this does not remove

Mathlib is still a `git` dependency, inherited from `vendor/zeta23`'s own
`lakefile.toml` at rev `51e6992efd06126df61a496bebf8f49482a4e129`. A fresh clone
still fetches Mathlib and its transitive dependencies. What is now on our own
disk is the package that carries this project's trusted inputs — the
`baseline_zeta23` cone and `PairCeiling` — not the whole toolchain.

Vendoring Mathlib was not ruled on and is not attempted here.

## Trust, before and after

Unchanged, and that is the point:

    base v2/cd7a22e688df (zetaNonempty) | axioms 2 | sorries 0
    certified NscStd 67.25% / Nsc 50.88%

Vendoring moves where the bytes live. It does not move what is believed.
