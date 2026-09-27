/-
Sector reduction must be proved (§15.5 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

For a projector `P` and generator `H`, the retained sector evolves autonomously only if
`(1 − P) H P = 0`; otherwise the omitted sector feeds back. The off-diagonal redistribution
operator `F(H, P) = (1 − P) H P + P H (1 − P)` vanishes exactly when `H` commutes with `P`.
(Any ring; `P` idempotent where stated.)
-/
import Mathlib

namespace DiracTime.SectorReduction

variable {R : Type*} [Ring R]

/-- The retained sector is invariant exactly when `(1 − P) H P = 0`, i.e. `H P = P H P`. -/
theorem leak_zero_iff (P H : R) : (1 - P) * H * P = 0 ↔ H * P = P * H * P := by
  constructor
  · intro h
    calc H * P = (1 - P) * H * P + P * H * P := by noncomm_ring
      _ = P * H * P := by rw [h, zero_add]
  · intro h
    calc (1 - P) * H * P = H * P - P * H * P := by noncomm_ring
      _ = 0 := by rw [h, sub_self]

/-- **Redistribution vanishes exactly on commuting generators.** -/
theorem redistribution_zero_iff_commute {P H : R} (hP : P * P = P) :
    (1 - P) * H * P + P * H * (1 - P) = 0 ↔ H * P = P * H := by
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  constructor
  · intro h
    have hl : P * H * (1 - P) = 0 := by
      calc P * H * (1 - P) = P * ((1 - P) * H * P + P * H * (1 - P)) - P * (1 - P) * H * P -
            (P * P - P) * H * (1 - P) := by noncomm_ring
        _ = 0 := by rw [h, hPQ, hP]; simp
    have hr : (1 - P) * H * P = 0 := by
      calc (1 - P) * H * P = ((1 - P) * H * P + P * H * (1 - P)) * P -
            (1 - P) * H * (P * P - P) - P * H * ((1 - P) * P) := by noncomm_ring
        _ = 0 := by rw [h, hQP, hP]; simp
    calc H * P = (1 - P) * H * P + P * H * P := by noncomm_ring
      _ = P * H * (1 - P) + P * H * P := by rw [hr, hl]
      _ = P * H := by noncomm_ring
  · intro h
    have e1 : (1 - P) * H * P = 0 := by rw [mul_assoc, h, ← mul_assoc, hQP, zero_mul]
    have e2 : P * H * (1 - P) = 0 := by rw [← h, mul_assoc, hPQ, mul_zero]
    rw [e1, e2, add_zero]

end DiracTime.SectorReduction
