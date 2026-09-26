<div align="center">

# Elemental Peeling and What the Boundary Retains — Lean proofs

**Machine-checked finite algebra behind the Elemental Peeling paper: what a specified removal takes away, what later records can recover, force recovery from readings, and the exclusion certificates of the combined peel.**

[![Lean proof check](https://github.com/dicipler-pixel/elemental-peeling-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/elemental-peeling-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-66-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![License](https://img.shields.io/badge/License-MIT-lightgrey)

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
| **Elemental foundations**: the original PR #17 layer (later-transmission gaps, the inverse chord identity and penalty, why averaging before inverting underestimates) plus joint records, robustness margins, the impossibility of a common-record predictor, and the scalar boundary ledger | [`ElementalFoundations`](ElementalFoundations.lean) | 30 |
| **Force recovery**: exact three-force recovery, unknown-offset four-reading recovery, deterministic error-combination bounds | [`ElementalForceRecovery`](ElementalForceRecovery.lean) | 13 |
| **Boundary ledger**: resolved versus common-floor comparisons for any finite family, and their quadratic-form version | [`ElementalBoundaryLedger`](ElementalBoundaryLedger.lean) | 5 |
| **Exclusion and a common retained coordinate**: the two-orbital Gram determinant is the squared antisymmetric amplitude; same-spin coincidence is forbidden while distinct samples are not; one retained coordinate drives two readouts; equal first-observer records do not fix the next filter record; the zero-time force-memory coefficient | [`PauliMemory`](PauliMemory.lean) | 17 |
| | **Total** | **66** |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: three deliberately false statements must fail to compile, for a
   mathematical reason: a false later-transmission equality with an unsafe mean-before-
   inversion inequality, a false memory law, and a false exclusion claim.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

*Elemental Peeling and What the Boundary Retains*, Jeromie Beasley. The Zenodo DOI will be added
here once the paper is deposited.

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released
under the [MIT License](LICENSE). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
