import UPGInterfacePersistence

/-!
# Interface Gram positivity consequences

Finite exact consequences of the retained/hidden interface Gram `B Bᵀ`.
These statements deliberately stay at the algebraic level: they do not identify
this Gram with biological memory, spacetime, light, or a material response.
-/

open Matrix BigOperators

namespace UPGFeedback

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- Each retained diagonal entry of the zero-time Gram is the sum of the
squared interface couplings leaving that retained channel. -/
theorem memoryAtZero_diag_eq_sum_sq (B : Matrix r h ℝ) (i : r) :
    memoryAtZero B i i = ∑ j : h, (B i j) ^ 2 := by
  simp [memoryAtZero, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

/-- Every retained diagonal channel strength is nonnegative. -/
theorem memoryAtZero_diag_nonneg (B : Matrix r h ℝ) (i : r) :
    0 ≤ memoryAtZero B i i := by
  rw [memoryAtZero_diag_eq_sum_sq]
  exact Finset.sum_nonneg (fun j _ => sq_nonneg (B i j))

/-- A retained channel has zero Gram weight exactly when every interface
coupling leaving that retained channel vanishes. -/
theorem memoryAtZero_diag_eq_zero_iff_row_zero (B : Matrix r h ℝ) (i : r) :
    memoryAtZero B i i = 0 ↔ ∀ j : h, B i j = 0 := by
  constructor
  · intro hdiag j
    have hsum : (∑ k : h, (B i k) ^ 2) = 0 := by
      simpa [memoryAtZero_diag_eq_sum_sq] using hdiag
    have hle : (B i j) ^ 2 ≤ ∑ k : h, (B i k) ^ 2 := by
      exact Finset.single_le_sum
        (fun k hk => sq_nonneg (B i k))
        (Finset.mem_univ j)
    rw [hsum] at hle
    have hsquare : (B i j) ^ 2 = 0 :=
      le_antisymm hle (sq_nonneg (B i j))
    exact sq_eq_zero_iff.mp hsquare
  · intro hrow
    rw [memoryAtZero_diag_eq_sum_sq]
    apply Finset.sum_eq_zero
    intro j hj
    simp [hrow j]

/-- The scalar interface coupling energy is nonnegative. -/
theorem couplingEnergy_nonneg (B : Matrix r h ℝ) :
    0 ≤ couplingEnergy B := by
  unfold couplingEnergy
  exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg (B i j)))

/-- The retained block of minus the commutator square has nonnegative diagonal
entries; this is the projector-tangent version of the previous Gram fact. -/
theorem neg_commutator_square_retained_diag_nonneg
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) (i : r) :
    0 ≤ -((projectorCommutator A B D * projectorCommutator A B D)
      (Sum.inl i) (Sum.inl i)) := by
  rw [← retained_memory_eq_neg_commutator_square A B D i i]
  exact memoryAtZero_diag_nonneg B i

/-- Vanishing interface coupling is equivalent to simultaneous vanishing of
the projector commutator and the retained zero-time Gram. -/
theorem coupling_zero_iff_tangent_and_memory_zero
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    B = 0 ↔ projectorCommutator A B D = 0 ∧ memoryAtZero B = 0 := by
  rw [← projectorCommutator_eq_zero_iff A B D]
  constructor
  · intro hC
    exact ⟨hC, (projector_commutes_iff_memory_zero A B D).mp hC⟩
  · rintro ⟨hC, _⟩
    exact hC

end UPGFeedback

#print axioms UPGFeedback.memoryAtZero_diag_eq_sum_sq
#print axioms UPGFeedback.memoryAtZero_diag_nonneg
#print axioms UPGFeedback.memoryAtZero_diag_eq_zero_iff_row_zero
#print axioms UPGFeedback.couplingEnergy_nonneg
#print axioms UPGFeedback.neg_commutator_square_retained_diag_nonneg
#print axioms UPGFeedback.coupling_zero_iff_tangent_and_memory_zero
