import UPGProjectorDynamics

/-!
# Interface-supported projector consequences

These are finite exact consequences of the already-certified retained/hidden
block model.  They sharpen the informal "interface memory" language without
adding a spacetime, material, light, or long-time-memory interpretation.

For

    H = [ A   B  ]      P = [ I  0 ]
        [ Bᵀ  D  ]          [ 0  0 ]

the projector commutator `[H,P]` depends only on the cross-sector block `B`.
Its conventional one-half squared cross-block energy is the same quantity as
the trace of the zero-time feedback Gram `B Bᵀ`.  Moreover, the retained block
of the negative commutator square is exactly that Gram.
-/

open Matrix BigOperators

namespace UPGFeedback

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- Changing either diagonal sector while keeping the interface coupling fixed
does not change the projector commutator. -/
theorem projectorCommutator_depends_only_on_coupling
    (A₁ A₂ : Matrix r r ℝ) (B : Matrix r h ℝ) (D₁ D₂ : Matrix h h ℝ) :
    projectorCommutator A₁ B D₁ = projectorCommutator A₂ B D₂ := by
  rw [projectorCommutator_eq_blocks, projectorCommutator_eq_blocks]

/-- The conventional one-half cross-block projector metric is independent of
both diagonal sectors and is determined entirely by the interface block. -/
theorem half_projectorCrossEnergy_independent_of_diagonal_blocks
    (A₁ A₂ : Matrix r r ℝ) (B : Matrix r h ℝ) (D₁ D₂ : Matrix h h ℝ) :
    (1 / 2 : ℝ) * projectorCrossEnergy A₁ B D₁ =
      (1 / 2 : ℝ) * projectorCrossEnergy A₂ B D₂ := by
  rw [half_projectorCrossEnergy_eq_couplingEnergy,
      half_projectorCrossEnergy_eq_couplingEnergy]

/-- Scalar zero-time memory strength equals the conventional one-half squared
cross-block projector-tangent energy. -/
theorem memory_trace_eq_half_projectorCrossEnergy
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    Matrix.trace (memoryAtZero B) =
      (1 / 2 : ℝ) * projectorCrossEnergy A B D := by
  rw [trace_memoryAtZero_eq_couplingEnergy,
      half_projectorCrossEnergy_eq_couplingEnergy]

/-- A nonzero zero-time feedback Gram forces a nonzero projector tangent
commutator. -/
theorem nonzero_memory_gives_nonzero_projectorCommutator
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (hK : memoryAtZero B ≠ 0) : projectorCommutator A B D ≠ 0 := by
  intro hC
  exact hK ((projector_commutes_iff_memory_zero A B D).mp hC)

/-- Squaring the projector commutator produces the two negative Gram blocks.
This is the exact quadratic bridge between the first-order interface tangent
and the second-order retained/hidden Gram structure. -/
theorem projectorCommutator_sq_eq_negative_grams
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCommutator A B D * projectorCommutator A B D =
      Matrix.fromBlocks (-(B * B.transpose)) 0 0 (-(B.transpose * B)) := by
  rw [projectorCommutator_eq_blocks]
  simp [Matrix.fromBlocks_multiply]

/-- Entrywise retained-sector form of the previous theorem: the zero-time
memory Gram is the retained block of minus the squared projector commutator. -/
theorem retained_memory_eq_neg_commutator_square
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (i j : r) :
    memoryAtZero B i j =
      -((projectorCommutator A B D * projectorCommutator A B D)
          (Sum.inl i) (Sum.inl j)) := by
  rw [projectorCommutator_sq_eq_negative_grams]
  simp [memoryAtZero]

end UPGFeedback

#print axioms UPGFeedback.projectorCommutator_depends_only_on_coupling
#print axioms UPGFeedback.half_projectorCrossEnergy_independent_of_diagonal_blocks
#print axioms UPGFeedback.memory_trace_eq_half_projectorCrossEnergy
#print axioms UPGFeedback.nonzero_memory_gives_nonzero_projectorCommutator
#print axioms UPGFeedback.projectorCommutator_sq_eq_negative_grams
#print axioms UPGFeedback.retained_memory_eq_neg_commutator_square
