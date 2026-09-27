# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.
Formalization is evidence for the mathematics, not for the physical interpretation.

## Proved, with their exact scope

* **§2 predictive quotient (T1).** Finite-dimensional vector space over any field, linear
  dynamics, linear observation.
* **Theorem P1 (T2).** Tangent characterization in any ring; positivity and unitary invariance
  for complex matrices; the metric–curvature inequality in block variables; the block formulas of item 2 for the
  splitting `Ran P ⊕ Ran Q` written as a sum of index types.
* **Theorem P2.** Any complex inner-product space, symmetric observable, normalized postselection.
* **Theorem P3 (T3).** Any admitted path system with additive, reversal-odd ledger on a
  connected configuration space; spectral flow is the case `A = ℤ` but spectral flow itself is
  not constructed.
* **Theorem P5.** The discrete-step criterion `R Lⁿ Δ`; the continuous-time exponential form and
  the operator-space dimension bound are not formalized.
* **Theorem P6 and P6.1.** The unitarity fact is proved: von Neumann entropy is invariant
  under `ρ ↦ UρU†` (`UnitaryEntropy`, built on Physlib), and P6 is restated with that
  hypothesis discharged. The Gibbs-reference form of the relative entropy,
  `D(ρ‖τ) = −S + βE + log Z`, is still a hypothesis; deriving it needs the logarithm of a
  Gibbs state. Klein's inequality (nonnegativity of relative entropy) is used as a hypothesis in
  P6.1.
* **Corollaries P4.1–P4.3.** Complex matrices; the eigenvector and gap statements, uniqueness
  of rate and shift for a non-scalar reference generator, and the rescaling statement.
* **§9.3 / T4.** The moving-frame identity at each instant, from the product rule; existence and
  uniqueness of solutions and the propagator form of Theorem P4 are not formalized.
* **§11.4.** The exact amplitudes, populations and readout of the finite witness.
* **§12.6.** The pairwise algebra, the Gibbs sign, the two-level gap and the zero-temperature
  band. The first-order slow-driving derivation of the pairwise formulas from the relaxation
  model is not formalized.
* **Theorem 13.1, parts 3–4.** The end-index congruences and the silence criterion. Parts 1–2
  (the SU(2) representation arcs) and the root statement for the Alexander polynomial are not
  formalized.

## Not proved here

* Programme items T5–T10: the weak-history readout protocol, the thermodynamic repair for a
  microscopically derived bath, the trefoil / 8₁₉ APS family and the exterior Cauchy-data
  computation, the material realization of light-path inheritance, the Maxwell–Dirac gate
  (Proposition 15.3 is a PDE statement), and the arrow model.
* Every physical hypothesis: the electron-memory hypothesis, the Gigantefermion hypothesis, path
  inheritance for light, the arrow architecture, and any gravitational or cosmological reading.

## A note on Theorem 13.1(4)

With `A = m + ε_μ`, `B = 1`, `C = n + ε_λ + a/2`, `D = −pq`, the numerator is
`AD − BC = −(pq (m + ε_μ) + n + ε_λ + a/2)`. The silence criterion
`pq ε_μ + ε_λ + a/2 ∈ ℤ` follows from this form and is what `PhaseSilence.lean` proves.
