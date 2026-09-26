import UPGFeedback
import Mathlib.Data.Matrix.Block

/-!
# Adapted retained/hidden block feedback equivalence

Finite real block-matrix completion of the UPG redistribution criterion.
For an adapted symmetric/Hermitian block Hamiltonian

    H = [ A   B  ]
        [ Bᵀ  D  ]

and retained projector

    P = [ I  0 ]
        [ 0  0 ],

this module proves that the off-diagonal redistribution operator is exactly
`(I-P)HP + PH(I-P)`, while `[H,P] = 0`, redistribution `= 0`, `B = 0`, and
the zero-time feedback Gram `BBᵀ = 0` are equivalent.

This is finite block algebra only. It does not formalize a time-dependent
memory kernel, a resolvent self-energy, CP-divisibility, or a material model.
-/

open Matrix

namespace UPGFeedback

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- Adapted real symmetric block Hamiltonian. -/
def blockHamiltonian (A : Matrix r r ℝ) (B : Matrix r h ℝ)
    (D : Matrix h h ℝ) : Matrix (Sum r h) (Sum r h) ℝ :=
  Matrix.fromBlocks A B B.transpose D

/-- Projector onto the retained block. -/
def retainedProjection : Matrix (Sum r h) (Sum r h) ℝ :=
  Matrix.fromBlocks 1 0 0 0

/-- The complementary projector has the expected adapted block form. -/
theorem one_sub_retainedProjection :
    (1 - retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) =
      Matrix.fromBlocks 0 0 0 1 := by
  ext i j
  cases i <;> cases j <;> simp [retainedProjection, Matrix.one_apply]

/-- Matrix commutator with the retained projector. -/
def projectorCommutator (A : Matrix r r ℝ) (B : Matrix r h ℝ)
    (D : Matrix h h ℝ) : Matrix (Sum r h) (Sum r h) ℝ :=
  blockHamiltonian A B D * retainedProjection -
    retainedProjection * blockHamiltonian A B D

/-- Exact block form of `[H,P]`. -/
theorem projectorCommutator_eq_blocks
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCommutator A B D = Matrix.fromBlocks 0 (-B) B.transpose 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [projectorCommutator, blockHamiltonian, retainedProjection,
      Matrix.fromBlocks_multiply]

/-- Commutation with the retained projector is exactly absence of retained-hidden
coupling in the adapted block basis. -/
theorem projectorCommutator_eq_zero_iff
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCommutator A B D = 0 ↔ B = 0 := by
  constructor
  · intro hC
    have hblocks := projectorCommutator_eq_blocks A B D
    rw [hC] at hblocks
    ext i j
    have h := congrArg
      (fun M : Matrix (Sum r h) (Sum r h) ℝ => M (Sum.inl i) (Sum.inr j))
      hblocks
    simpa using h
  · intro hB
    subst B
    simpa using (projectorCommutator_eq_blocks A (0 : Matrix r h ℝ) D)

/-- Off-diagonal redistribution written directly as a Peirce cross term. -/
def peirceRedistribution (A : Matrix r r ℝ) (B : Matrix r h ℝ)
    (D : Matrix h h ℝ) : Matrix (Sum r h) (Sum r h) ℝ :=
  (1 - retainedProjection) * blockHamiltonian A B D * retainedProjection +
    retainedProjection * blockHamiltonian A B D * (1 - retainedProjection)

/-- The Peirce cross term is exactly the redistribution matrix already
formalized in `UPGFeedback.lean`. -/
theorem peirceRedistribution_eq_redistribution
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    peirceRedistribution A B D = redistribution B := by
  rw [peirceRedistribution, one_sub_retainedProjection]
  ext i j
  cases i <;> cases j <;>
    simp [retainedProjection, blockHamiltonian, redistribution,
      Matrix.fromBlocks_multiply]

/-- Four equivalent finite diagnostics of retained-hidden coupling. -/
theorem adapted_feedback_equivalences
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCommutator A B D = 0 ↔
      peirceRedistribution A B D = 0 ∧ memoryAtZero B = 0 := by
  rw [projectorCommutator_eq_zero_iff]
  rw [peirceRedistribution_eq_redistribution]
  rw [redistribution_eq_zero_iff, memoryAtZero_eq_zero_iff]
  constructor
  · intro hB
    exact ⟨hB, hB⟩
  · rintro ⟨hB, _⟩
    exact hB

/-- Fully flattened equivalence: commutator zero iff redistribution zero. -/
theorem projector_commutes_iff_redistribution_zero
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCommutator A B D = 0 ↔ redistribution B = 0 := by
  rw [projectorCommutator_eq_zero_iff, redistribution_eq_zero_iff]

/-- Fully flattened equivalence: commutator zero iff zero-time feedback Gram
vanishes. -/
theorem projector_commutes_iff_memory_zero
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCommutator A B D = 0 ↔ memoryAtZero B = 0 := by
  rw [projectorCommutator_eq_zero_iff, memoryAtZero_eq_zero_iff]

end UPGFeedback

#print axioms UPGFeedback.one_sub_retainedProjection
#print axioms UPGFeedback.projectorCommutator_eq_blocks
#print axioms UPGFeedback.projectorCommutator_eq_zero_iff
#print axioms UPGFeedback.peirceRedistribution_eq_redistribution
#print axioms UPGFeedback.adapted_feedback_equivalences
#print axioms UPGFeedback.projector_commutes_iff_redistribution_zero
#print axioms UPGFeedback.projector_commutes_iff_memory_zero
