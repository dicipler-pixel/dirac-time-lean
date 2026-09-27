<div align="center">

# The Dirac Time of the Gigantefermion — Lean proofs

**Machine-checked mathematics behind the paper: every exact finite result it states, checked by the Lean kernel on every push.**

[![Lean proof check](https://github.com/dicipler-pixel/dirac-time-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/dirac-time-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-80_%2B_3_headline-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![License](https://img.shields.io/badge/License-MIT-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22978630-blue)](https://doi.org/10.5281/zenodo.22978630)

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

## What is proved

| Paper | Result | File | Status |
| :--- | :--- | :--- | :-: |
| §2.1–2.4, item T1 | Predictive quotient: equivalence, descent of the dynamics, Cayley–Hamilton closure, rank formula, minimality, closure of the present observation | [`PredictiveQuotient`](DiracTime/PredictiveQuotient.lean) | **proved** |
| §3.1 | Structural memory filtration: a coarser record cannot create distinctions | [`MemoryFiltration`](DiracTime/MemoryFiltration.lean) | **proved** |
| Theorem P1, item T2 | Projector tangents: tangent equation ⇔ both diagonal blocks vanish, tangents are off-diagonal, metric positivity, unitary invariance of `g` and `Ω`, metric–curvature inequality | [`ProjectorTangent`](DiracTime/ProjectorTangent.lean) | **proved** |
| Theorem P1, item 2 | Block formulas: `g = Re Tr(XY†)`, `Ω = −2 Im Tr(XY†)`, `Q = Tr(XY†) = g − (i/2) Ω` | [`ProjectorBlocks`](DiracTime/ProjectorBlocks.lean) | **proved** |
| Theorem P2 | Weak-value success-probability bound `p₀ |A_w|² ≤ ⟨i|A²|i⟩` | [`WeakValue`](DiracTime/WeakValue.lean) | **proved** |
| Theorem P3, item T3 | Path-ledger descent: an endpoint potential exists ⇔ every loop is silent; positive reachability is not antisymmetric | [`PathLedger`](DiracTime/PathLedger.lean) | **proved** |
| Corollaries P4.1–P4.3 | Common gap scaling `µⱼ − µₖ = τ̇ (Eⱼ − Eₖ)`; rate and shift unique for non-scalar `H₀`; rescaling `H ↦ sH` keeps every eigenvector but scales every gap | [`CommonClock`](DiracTime/CommonClock.lean) | **proved** |
| Theorem P5 | Finite return: a difference returns to the observed sector at some step ⇔ within the first `dim V` steps | [`FiniteReturn`](DiracTime/FiniteReturn.lean) | **proved** (discrete-step form) |
| Theorem P6, P6.1 | Entropy/correlation ledger `ΔS_S − Σ β_r Q_r = ΔI + Σ ΔD_r` and the integrated second law | [`EntropyLedger`](DiracTime/EntropyLedger.lean) | **proved** from the two stated operator facts |
| §9.2 | Affine phase readout: the angular numerator `AD − BC` is constant | [`PhaseSilence`](DiracTime/PhaseSilence.lean) | **proved** |
| §9.3, item T4 | Moving-frame identity `iħχ̇ = (R†HR − iħR†Ṙ)χ` and the common-clock form | [`MovingFrame`](DiracTime/MovingFrame.lean) | **proved** (instantaneous identity) |
| §11.4 | Equal-endpoint witness: `|a − ib e^{iΦ}|² = a² + b² + 2ab sin Φ`, `⟨Z⟩ = sin 2θ sin Φ`, equal present populations, probe blind to `π − Φ` | [`EqualEndpointWitness`](DiracTime/EqualEndpointWitness.lean) | **proved** |
| §12.6 | Friction on projector rotations: pair friction = reweighted intrinsic metric, Gibbs sign, two-level `tanh(β∆/2)`, zero-temperature band | [`FrictionMetric`](DiracTime/FrictionMetric.lean) | **proved** (pairwise formulas) |
| Theorem 13.1(3–4) | Torus-knot end indices `k ≡ a (mod p)`, `k ≡ ±b (mod q)`; silent sector ⇔ `pq ε_μ + ε_λ + a/2 ∈ ℤ` | [`PhaseSilence`](DiracTime/PhaseSilence.lean) | **proved** |
| §15.5 | Sector reduction: `(1−P)HP = 0` ⇔ `HP = PHP`; redistribution vanishes ⇔ `[H, P] = 0` | [`SectorReduction`](DiracTime/SectorReduction.lean) | **proved** |
| T5–T10 | Weak-history readout protocol, thermodynamic repair for a Davies bath, trefoil / 8₁₉ APS family, light-path material realization, Maxwell–Dirac gate, arrow model | — | open |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.34.1 and Mathlib `v4.34.1`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: thirteen deliberately false statements must fail to compile, and fail
   for a mathematical reason, not a typo. This shows the checker can say no.

To check it yourself with Lean installed:

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## The paper

*The Dirac Time of the Gigantefermion*, Jeromie Beasley. DOI
[10.5281/zenodo.22978630](https://doi.org/10.5281/zenodo.22978630).

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and scripts are released
under the [MIT License](LICENSE). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
