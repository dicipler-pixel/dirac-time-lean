<div align="center">

# The Dirac Time of the Gigantefermion — Lean proofs

**Machine-checked mathematics behind the paper, built up one programme item at a time.**

[![Lean proof check](https://github.com/dicipler-pixel/dirac-time-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/dirac-time-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-17_%2B_3_headline-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![License](https://img.shields.io/badge/License-MIT-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22978631-blue)](https://doi.org/10.5281/zenodo.22978631)

Jeromie Beasley

</div>

---

## The idea in one line

Memory comes before the clock. A present state is worth remembering only as far as some
future observation can tell it apart. Take a linear continuation map `L` and a declared
observation `R`. Two states are equivalent when every future reading `R Lⁿ` agrees on them,
and the quotient by that equivalence is the smallest state that still predicts everything:

$$
N_\infty=\{v : R L^n v = 0 \ \text{for all } n\},\qquad
V_{\text{pred}} = V/N_\infty,\qquad
\dim V_{\text{pred}} = \operatorname{rank}\,(R,\ RL,\ \dots,\ RL^{d-1}).
$$

## Start here

| If you want to… | Open |
| :--- | :--- |
| See the main results in plain Mathlib terms | [`DiracTime/Headline.lean`](DiracTime/Headline.lean) |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the proofs themselves | [`DiracTime/PredictiveQuotient.lean`](DiracTime/PredictiveQuotient.lean) |
| See the statements that must be rejected | [`FalseControls/`](FalseControls/) |

## Headline results

| # | Statement | In words |
| :-: | :--- | :--- |
| 1 | `future_decided_by_first_dim_steps` | Two states agree on every future observation exactly when they agree on the first `dim V` of them |
| 2 | `minimal_predictor_dimension` | Any linear summary that determines all future observations has rank at least `dim (V / N∞)` |
| 3 | `present_observation_closes_iff` | The present reading needs no memory exactly when `R L = A R` for some linear `A` |

## Programme

The paper lists its own theorem programme (§21). This repository follows it.

| Item | Content | Status |
| :-: | :--- | :-: |
| T1 | Predictive quotient: equivalence, descent, Cayley–Hamilton closure, rank, minimality, present-observation closure (§2.1–2.4) | **proved** |
| T2 | Star-projection tangent geometry and the metric–curvature inequality (Theorem P1) | next |
| T3 | Path-ledger descent: a potential exists exactly when every admitted loop has zero ledger (Theorem P3) | planned |
| — | Weak-value success bound (Theorem P2) | planned |
| — | Finite observable-return criterion (Theorem P5) | planned |
| — | Finite entropy/correlation identity (Theorem P6), on Physlib's quantum relative entropy | planned |
| T4 | Common-clock criterion (Theorem P4) | open |
| T5–T10 | Weak-history readout, thermodynamic repair, trefoil / 8₁₉ APS family, light-path inheritance, Maxwell–Dirac gate, arrow model | open |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.34.1 and Mathlib `v4.34.1`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: deliberately false statements must fail to compile, and fail for a
   mathematical reason, not a typo. This shows the checker can say no.

To check it yourself with Lean installed:

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

*The Dirac Time of the Gigantefermion*, Jeromie Beasley. DOI
[10.5281/zenodo.22978631](https://doi.org/10.5281/zenodo.22978631).

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released
under the [MIT License](LICENSE). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
