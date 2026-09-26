import UPGBlockFeedback

/-!
# Projector motion metric bridge

Finite exact algebra connecting retained/hidden coupling, the projector
commutator, and the zero-time feedback Gram. This file deliberately stops
before any spacetime or physical-sector identification.
-/

open Matrix BigOperators

namespace UPGFeedback

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- Squared Frobenius energy of a rectangular real matrix. -/
def couplingEnergy (B : Matrix r h ℝ) : ℝ :=
  ∑ i, ∑ j, (B i j) ^ 2

/-- The retained-sector feedback Gram has trace equal to the total squared
retained/hidden coupling. -/
theorem trace_memoryAtZero_eq_couplingEnergy (B : Matrix r h ℝ) :
    Matrix.trace (memoryAtZero B) = couplingEnergy B := by
  simp [memoryAtZero, couplingEnergy, Matrix.trace, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]

/-- The retained-to-hidden block of `[H,P]` is exactly `-B`. -/
theorem projectorCommutator_inl_inr
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (i : r) (j : h) :
    projectorCommutator A B D (Sum.inl i) (Sum.inr j) = - B i j := by
  rw [projectorCommutator_eq_blocks]
  simp

/-- The hidden-to-retained block of `[H,P]` is exactly `Bᵀ`. -/
theorem projectorCommutator_inr_inl
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (i : h) (j : r) :
    projectorCommutator A B D (Sum.inr i) (Sum.inl j) = B j i := by
  rw [projectorCommutator_eq_blocks]
  simp

/-- The squared energy in one oriented cross block of the projector commutator
is exactly the trace of the zero-time feedback Gram. -/
theorem projector_cross_energy_eq_memory_trace
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    (∑ i : r, ∑ j : h,
      (projectorCommutator A B D (Sum.inl i) (Sum.inr j)) ^ 2)
      = Matrix.trace (memoryAtZero B) := by
  rw [trace_memoryAtZero_eq_couplingEnergy]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  rw [projectorCommutator_inl_inr]
  ring

/-- The reverse oriented cross block carries the same squared coupling energy. -/
theorem projector_reverse_cross_energy_eq_couplingEnergy
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    (∑ i : h, ∑ j : r,
      (projectorCommutator A B D (Sum.inr i) (Sum.inl j)) ^ 2)
      = couplingEnergy B := by
  rw [couplingEnergy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [projectorCommutator_inr_inl]

/-- Sum of the two oriented cross-block square energies. -/
def projectorCrossEnergy
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) : ℝ :=
  (∑ i : r, ∑ j : h,
      (projectorCommutator A B D (Sum.inl i) (Sum.inr j)) ^ 2) +
  (∑ i : h, ∑ j : r,
      (projectorCommutator A B D (Sum.inr i) (Sum.inl j)) ^ 2)

/-- Exact factor-of-two identity for the two oriented cross blocks. -/
theorem projectorCrossEnergy_eq_two_mul_couplingEnergy
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCrossEnergy A B D = 2 * couplingEnergy B := by
  unfold projectorCrossEnergy
  rw [projector_cross_energy_eq_memory_trace,
      trace_memoryAtZero_eq_couplingEnergy,
      projector_reverse_cross_energy_eq_couplingEnergy]
  ring

/-- With the conventional one-half projector normalization, the cross-block
energy is exactly the retained-hidden coupling energy. -/
theorem half_projectorCrossEnergy_eq_couplingEnergy
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    (1 / 2 : ℝ) * projectorCrossEnergy A B D = couplingEnergy B := by
  rw [projectorCrossEnergy_eq_two_mul_couplingEnergy]
  ring

end UPGFeedback

#print axioms UPGFeedback.trace_memoryAtZero_eq_couplingEnergy
#print axioms UPGFeedback.projectorCommutator_inl_inr
#print axioms UPGFeedback.projectorCommutator_inr_inl
#print axioms UPGFeedback.projector_cross_energy_eq_memory_trace
#print axioms UPGFeedback.projector_reverse_cross_energy_eq_couplingEnergy
#print axioms UPGFeedback.projectorCrossEnergy_eq_two_mul_couplingEnergy
#print axioms UPGFeedback.half_projectorCrossEnergy_eq_couplingEnergy
