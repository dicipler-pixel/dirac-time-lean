import Mathlib

/-!
# UPG finite redistribution-feedback bridge

This isolated module formalizes the finite Hermitian block kernel behind the
written UPG/cascade feedback criterion. It does not formalize open-system
Markovianity, a material model, or an infinite-time memory claim.

For a retained-hidden coupling block `B`, the UPG redistribution operator is the
off-diagonal block matrix

    [ 0   B ]
    [ Bᵀ  0 ]

and the zero-time eliminated-sector memory matrix is `B Bᵀ`. Both vanish
exactly when `B` vanishes.
-/

open Matrix

namespace UPGFeedback

variable {r h : Type*} [Fintype r] [Fintype h]

/-- Hermitian/symmetric off-diagonal redistribution block. -/
def redistribution (B : Matrix r h ℝ) : Matrix (Sum r h) (Sum r h) ℝ :=
  Matrix.fromBlocks 0 B B.transpose 0

/-- Zero-time retained-sector feedback Gram. -/
def memoryAtZero (B : Matrix r h ℝ) : Matrix r r ℝ :=
  B * B.transpose

/-- The redistribution block is zero exactly when the retained-hidden coupling
block is zero. -/
theorem redistribution_eq_zero_iff (B : Matrix r h ℝ) :
    redistribution B = 0 ↔ B = 0 := by
  constructor
  · intro hB
    ext i j
    have h := congrArg (fun M : Matrix (Sum r h) (Sum r h) ℝ =>
      M (Sum.inl i) (Sum.inr j)) hB
    simpa [redistribution] using h
  · intro hB
    subst B
    simp [redistribution]

/-- The zero-time feedback Gram is zero exactly when the coupling block is
zero. The reverse direction is proved directly from the diagonal sum of
squares, avoiding any complex-conjugation representation choice. -/
theorem memoryAtZero_eq_zero_iff (B : Matrix r h ℝ) :
    memoryAtZero B = 0 ↔ B = 0 := by
  constructor
  · intro hK
    ext i j
    have hdiag := congrArg (fun M : Matrix r r ℝ => M i i) hK
    have hsum : (∑ k, (B i k)^2) = 0 := by
      simpa [memoryAtZero, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hdiag
    have hle : (B i j)^2 ≤ ∑ k, (B i k)^2 := by
      exact Finset.single_le_sum
        (fun k hk => sq_nonneg (B i k))
        (Finset.mem_univ j)
    rw [hsum] at hle
    have hsquare : (B i j)^2 = 0 :=
      le_antisymm hle (sq_nonneg (B i j))
    simpa using (sq_eq_zero_iff.mp hsquare)
  · intro hB
    subst B
    simp [memoryAtZero]

/-- Finite Hermitian feedback criterion: vanishing redistribution, vanishing
zero-time memory Gram, and vanishing retained-hidden coupling are equivalent. -/
theorem redistribution_zero_iff_memory_zero (B : Matrix r h ℝ) :
    redistribution B = 0 ↔ memoryAtZero B = 0 := by
  rw [redistribution_eq_zero_iff, memoryAtZero_eq_zero_iff]

/-- Nonzero coupling forces a nonzero redistribution operator. -/
theorem nonzero_coupling_gives_nonzero_redistribution (B : Matrix r h ℝ)
    (hB : B ≠ 0) : redistribution B ≠ 0 := by
  intro hF
  exact hB ((redistribution_eq_zero_iff B).mp hF)

/-- Nonzero coupling forces a nonzero zero-time memory Gram. -/
theorem nonzero_coupling_gives_nonzero_memory (B : Matrix r h ℝ)
    (hB : B ≠ 0) : memoryAtZero B ≠ 0 := by
  intro hK
  exact hB ((memoryAtZero_eq_zero_iff B).mp hK)

end UPGFeedback

#print axioms UPGFeedback.redistribution_eq_zero_iff
#print axioms UPGFeedback.memoryAtZero_eq_zero_iff
#print axioms UPGFeedback.redistribution_zero_iff_memory_zero
#print axioms UPGFeedback.nonzero_coupling_gives_nonzero_redistribution
#print axioms UPGFeedback.nonzero_coupling_gives_nonzero_memory
