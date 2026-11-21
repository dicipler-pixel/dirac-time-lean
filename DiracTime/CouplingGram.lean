/-
Instantaneous coupling Gram (§10.1 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

For an idempotent `P`,
`P H² P − (P H P)² = P H (1 − P) H P`.
-/
import Mathlib

namespace DiracTime.CouplingGram

variable {R : Type*} [Ring R]

/-- **§10.1.** The instantaneous coupling Gram of an idempotent. -/
theorem coupling_gram {P H : R} (hP : P * P = P) :
    P * H * H * P - (P * H * P) * (P * H * P) = P * H * (1 - P) * H * P := by
  have hPP : P * H * P * P * H * P = P * H * P * H * P := by
    calc
      P * H * P * P * H * P = P * H * (P * P) * H * P := by noncomm_ring
      _ = P * H * P * H * P := by rw [hP]
  have hassoc : (P * H * P) * (P * H * P) = P * H * P * P * H * P := by noncomm_ring
  rw [hassoc, hPP]
  noncomm_ring

end DiracTime.CouplingGram
