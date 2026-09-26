import Mathlib

/-!
Algebraic bridges for Jeromie Beasley's Light Keeps the Ledger.
STATUS: complete proof scripts, NOT COMPILED in the delivery environment.
No assertion of kernel acceptance is made. See STATUS.json.
These universal identities are standard algebra applied to the source manuscript;
they are not novelty or physical-identification claims.
-/

set_option autoImplicit false

namespace LightBridges
section RingIdentities
variable {R : Type*} [Ring R]

/-- Off-diagonal redistribution relative to an idempotent. -/
def redistribute (P A : R) : R := (1 - P) * A * P + P * A * (1 - P)

/-- This expansion does not require self-adjointness. -/
theorem redistribute_expansion (P A : R) :
    redistribute P A = P * A + A * P - (P * A * P + P * A * P) := by
  unfold redistribute
  noncomm_ring

/-- The redistribution operator is a double commutator for every idempotent. -/
theorem redistribute_double_commutator (P A : R) (hP : P * P = P) :
    redistribute P A = P * (P * A - A * P) - (P * A - A * P) * P := by
  rw [redistribute_expansion]
  calc
    P * A + A * P - (P * A * P + P * A * P) =
        (P * P) * A + A * (P * P) - (P * A * P + P * A * P) := by rw [hP]
    _ = P * (P * A - A * P) - (P * A - A * P) * P := by noncomm_ring

/-- Commuting generators produce no redistribution. -/
theorem redistribute_zero_of_commuting (P A : R) (hP : P * P = P)
    (hcomm : P * A = A * P) : redistribute P A = 0 := by
  rw [redistribute_double_commutator P A hP, hcomm]
  simp

/-- Normality reduction, before division by two. -/
theorem symmetric_skew_commutator (S K : R) :
    (S + K) * (S - K) - (S - K) * (S + K) =
      -((S * K - K * S) + (S * K - K * S)) := by
  noncomm_ring

/-- Upper-left block of P^2=P gives cross-boundary coupling = C-C^2.
The premise is a block equation, not positivity or a census bound. -/
theorem boundary_defect_of_block_idempotence (C B2 : R)
    (hblock : C * C + B2 = C) : C - C * C = B2 := by
  calc
    C - C * C = (C * C + B2) - C * C :=
      congrArg (fun X : R => X - C * C) hblock.symm
    _ = B2 := by abel

/-- An involution is characterized by its factored quadratic polynomial. -/
theorem involution_factorization (U : R) :
    (U - 1) * (U + 1) = 0 ↔ U * U = 1 := by
  have h : (U - 1) * (U + 1) = U * U - 1 := by noncomm_ring
  rw [h, sub_eq_zero]


end RingIdentities
end LightBridges
