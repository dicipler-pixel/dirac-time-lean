import UPGResolventFeedback
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite positive-response feedback criterion

This module gives a direct finite quadratic-form criterion for retained feedback.
It does not assume a Gram factorization, a resolvent representation, or a
physical interpretation.
-/

open Matrix

namespace UPGFeedback

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- The diagonal of the retained feedback is the quadratic response of the
corresponding row of the coupling matrix. -/
theorem feedbackWith_diag
    (B : Matrix r h ℝ) (R : Matrix h h ℝ) (i : r) :
    feedbackWith B R i i = (B i) ⬝ᵥ (R *ᵥ B i) := by
  simp only [feedbackWith, Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- A positive-definite hidden response detects every nonzero retained-hidden
coupling through the full feedback matrix. -/
theorem feedbackWith_eq_zero_iff_of_posDef
    (B : Matrix r h ℝ) (R : Matrix h h ℝ)
    (hR : R.PosDef) :
    feedbackWith B R = 0 ↔ B = 0 := by
  constructor
  · intro hfeedback
    ext i j
    have hdiag : (feedbackWith B R) i i = 0 := by
      simpa using congr_fun (congr_fun hfeedback i) i
    have hquad : (B i) ⬝ᵥ (R *ᵥ B i) = 0 := by
      rw [← feedbackWith_diag B R i]
      exact hdiag
    by_contra hij
    have hrow : B i ≠ 0 := by
      intro hzero
      exact hij (congr_fun hzero j)
    have hpos : 0 < (B i) ⬝ᵥ (R *ᵥ B i) := by
      simpa using hR.dotProduct_mulVec_pos hrow
    exact (ne_of_gt hpos) hquad
  · intro hB
    subst B
    simp [feedbackWith]

/-- The contrapositive form used by the UPG finite feedback layer. -/
theorem nonzero_coupling_gives_nonzero_posDef_feedback
    (B : Matrix r h ℝ) (R : Matrix h h ℝ)
    (hR : R.PosDef) (hB : B ≠ 0) :
    feedbackWith B R ≠ 0 := by
  intro hzero
  exact hB ((feedbackWith_eq_zero_iff_of_posDef B R hR).mp hzero)

end UPGFeedback

#print axioms UPGFeedback.feedbackWith_diag
#print axioms UPGFeedback.feedbackWith_eq_zero_iff_of_posDef
#print axioms UPGFeedback.nonzero_coupling_gives_nonzero_posDef_feedback
