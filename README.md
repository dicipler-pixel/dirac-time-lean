<div align="center">

# The Ledger Outlives the Metric — Lean proofs

**Machine-checked finite projector algebra behind the gravity paper: projector tangents, the signed metric, the reciprocal determinant, the local overlap cap and the projector-overlap Taylor bridge.**

[![Lean proof check](https://github.com/dicipler-pixel/gravity-ledger-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/gravity-ledger-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-30-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![License](https://img.shields.io/badge/License-MIT-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22088625-blue)](https://doi.org/10.5281/zenodo.22088625)

Jeromie Beasley

</div>

---

## Start here

| If you want to… | Open |
| :--- | :--- |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the statements that must be rejected | [`FalseControls/`](FalseControls/) |

## What the library contains

| Subject | File | Theorems |
| :--- | :--- | :-: |
| **Projector algebra and the signed metric**: every tangent to an idempotent is purely off-diagonal; signed-square coordinates lose no directions; the Hermitian slice is a sum of squares; the reciprocal single-partner determinant is a negative square; a quantitative local-cap step; trace constraints from differentiating `P² = P` twice; exact counterexamples (phase alignment giving rank zero, `diag(0, −1)` against the weakened criterion, a negative non-self-adjoint tangent at a self-adjoint projector); the rank-one chart of the moving-wall example | [`Gravity`](Gravity.lean) | 23 |
| **Projector-overlap Taylor bridge**: the exact finite-difference identity for idempotents of equal trace; the full quadratic overlap limit from differentiability alone; a quantified small-o remainder; a negative tangent trace form forces cap excess on both sides; a local upper cap requires a nonnegative tangent trace form | [`GravityOverlap`](GravityOverlap.lean) | 7 |
| | **Total** | **30** |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: four deliberately false statements must fail to compile, for a
   mathematical reason: a positive reciprocal determinant, positivity at a point, a violated
   cap, and a positive moving signature.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

*The Ledger Outlives the Metric*, Jeromie Beasley. DOI
[10.5281/zenodo.22088625](https://doi.org/10.5281/zenodo.22088625).

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released
under the [MIT License](LICENSE). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
