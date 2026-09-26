# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

The declarations do not formalize spectral differentiation, density-matrix dynamics, Maxwell
boundary conditions, homogenization, analytic contour integrals, entropy functional calculus,
continuum optical capacity, Kakeya or local smoothing, or a physical transport-to-permittivity
identification.

* The census is formalized as scalar and count algebra plus a projector-block identity; the full
  singular-value spectral mapping remains a written argument.
* Rigidity starts from a specified scalar singular value; it does not construct the
  singular-value operator or identify rigidity with `n²`.
* The calibration obstruction in `LightCompletion` assumes that the squared transport singular
  value equals the field metric, a fixed positive regularizer, and optical coefficient `1 + k g`
  with `k > 0`. It excludes that particular identification only.
* The Edition 7.2 results of Sections 4.9e–f, 4.10a and 5.2 (the gapped spectral-measure
  extension, conserved-strength upward redistribution, the quantum-oscillator realization and
  the weakest-singular-value criterion) are proved in the written paper and checked by its exact
  rational scripts; they are not yet formalized here.

Formalization is evidence for the mathematics, not for the physical interpretation.
