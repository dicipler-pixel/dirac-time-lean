import UPGProjectorDynamics

/-!
# Finite factorized resolvent feedback criterion

This module isolates a finite algebraic resolvent statement.  If a hidden
response matrix factors as `R = C Cᵀ` and `C` has an explicit right inverse,
then vanishing retained feedback `B R Bᵀ` is equivalent to vanishing coupling
`B`.  No spectral square-root theorem or physical resolvent identification is
assumed here.
-/

open Matrix

namespace UPGFeedback

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- Finite retained-sector feedback associated with a hidden response matrix. -/
def feedbackWith (B : Matrix r h ℝ) (R : Matrix h h ℝ) : Matrix r r ℝ :=
  B * R * B.transpose

/-- A Gram-factorized hidden response turns the feedback into the zero-time
Gram of the transformed coupling `B C`. -/
theorem feedbackWith_factorized
    (B : Matrix r h ℝ) (R C : Matrix h h ℝ)
    (hR : R = C * C.transpose) :
    feedbackWith B R = memoryAtZero (B * C) := by
  rw [feedbackWith, hR, memoryAtZero, Matrix.transpose_mul]
  simp [Matrix.mul_assoc]

/-- Under an explicit right inverse for the Gram factor, vanishing factorized
feedback is equivalent to vanishing coupling. -/
theorem feedbackWith_eq_zero_iff_of_factor_right_inverse
    (B : Matrix r h ℝ) (R C L : Matrix h h ℝ)
    (hR : R = C * C.transpose)
    (hCL : C * L = (1 : Matrix h h ℝ)) :
    feedbackWith B R = 0 ↔ B = 0 := by
  constructor
  · intro hfb
    have hgram : memoryAtZero (B * C) = 0 := by
      rw [← feedbackWith_factorized B R C hR]
      exact hfb
    have hBC : B * C = 0 := (memoryAtZero_eq_zero_iff (B * C)).mp hgram
    calc
      B = B * (1 : Matrix h h ℝ) := by simp
      _ = B * (C * L) := by rw [hCL]
      _ = (B * C) * L := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hBC]; simp
  · intro hB
    subst B
    simp [feedbackWith]

/-- Nonzero retained-hidden coupling cannot have zero factorized feedback under
the same explicit right-invertibility hypothesis. -/
theorem nonzero_coupling_gives_nonzero_factorized_feedback
    (B : Matrix r h ℝ) (R C L : Matrix h h ℝ)
    (hR : R = C * C.transpose)
    (hCL : C * L = (1 : Matrix h h ℝ))
    (hB : B ≠ 0) :
    feedbackWith B R ≠ 0 := by
  intro hzero
  exact hB ((feedbackWith_eq_zero_iff_of_factor_right_inverse B R C L hR hCL).mp hzero)

end UPGFeedback

#print axioms UPGFeedback.feedbackWith_factorized
#print axioms UPGFeedback.feedbackWith_eq_zero_iff_of_factor_right_inverse
#print axioms UPGFeedback.nonzero_coupling_gives_nonzero_factorized_feedback
