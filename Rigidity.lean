import Mathlib

/-!
Candidate algebraic formalization for Light Keeps the Ledger, integrated v2.
NOT COMPILED in the preparation environment. No kernel-verification claim.
`s` represents an already specified least transport singular value. This module
neither constructs a singular-value operator nor identifies rigidity with n^2.
-/
namespace LightRigidity

noncomputable def regularized (s eta : ℝ) : ℝ := 1 / (s ^ 2 + eta)

theorem denominator_pos (s eta : ℝ) (h : 0 < eta) : 0 < s ^ 2 + eta := by
  nlinarith [sq_nonneg s]

theorem regularized_pos (s eta : ℝ) (h : 0 < eta) : 0 < regularized s eta := by
  exact one_div_pos.mpr (denominator_pos s eta h)

theorem regulator_cap (s eta : ℝ) (h : 0 < eta) : regularized s eta ≤ 1 / eta := by
  unfold regularized
  exact one_div_le_one_div_of_le h (by nlinarith [sq_nonneg s])

theorem null_direction (eta : ℝ) : regularized 0 eta = 1 / eta := by
  simp [regularized]

theorem inverse_identity (s eta : ℝ) (h : 0 < eta) :
    regularized s eta * (s ^ 2 + eta) = 1 := by
  unfold regularized
  exact one_div_mul_cancel (ne_of_gt (denominator_pos s eta h))

theorem antitone_in_singular_value (s t eta : ℝ)
    (heta : 0 < eta) (hs : 0 ≤ s) (hst : s ≤ t) :
    regularized t eta ≤ regularized s eta := by
  unfold regularized
  apply one_div_le_one_div_of_le (denominator_pos s eta heta)
  nlinarith

/-- Algebra AFTER the variational derivation has supplied conserved squared
momentum and one common positive kinetic factor. The variational derivation is
not encoded here; angle variables are their already specified sine values. -/
theorem interface_from_common_kinetic_factor (p K r₁ r₂ a₁ a₂ : ℝ)
    (hK : K ≠ 0)
    (h₁ : p ^ 2 = K * (r₁ * a₁ ^ 2))
    (h₂ : p ^ 2 = K * (r₂ * a₂ ^ 2)) :
    r₁ * a₁ ^ 2 = r₂ * a₂ ^ 2 := by
  apply mul_left_cancel₀ hK
  exact h₁.symm.trans h₂

/-- Substitution of the agreed scalar rigidity into the squared interface law. -/
theorem regulated_interface_iff (s₁ s₂ eta a₁ a₂ : ℝ) (heta : 0 < eta) :
    regularized s₁ eta * a₁ ^ 2 = regularized s₂ eta * a₂ ^ 2 ↔
      a₁ ^ 2 * (s₂ ^ 2 + eta) = a₂ ^ 2 * (s₁ ^ 2 + eta) := by
  have h₁ : s₁ ^ 2 + eta ≠ 0 := ne_of_gt (denominator_pos s₁ eta heta)
  have h₂ : s₂ ^ 2 + eta ≠ 0 := ne_of_gt (denominator_pos s₂ eta heta)
  unfold regularized
  rw [one_div_mul_eq_div, one_div_mul_eq_div]
  exact div_eq_div_iff h₁ h₂

end LightRigidity

#print axioms LightRigidity.denominator_pos
#print axioms LightRigidity.regularized_pos
#print axioms LightRigidity.regulator_cap
#print axioms LightRigidity.null_direction
#print axioms LightRigidity.inverse_identity
#print axioms LightRigidity.antitone_in_singular_value
#print axioms LightRigidity.interface_from_common_kinetic_factor
#print axioms LightRigidity.regulated_interface_iff
