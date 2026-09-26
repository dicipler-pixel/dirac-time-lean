import TailGapTransfer
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite Schur transfer at a candidate spectral floor

This module turns the exact finite Schur block algebra into a positivity-floor
certificate.  A real symmetric block matrix is shifted by a candidate floor
`μ`.  If the hidden shifted block is positive definite (hence invertible),
Mathlib's Schur-complement theorem says that positive semidefiniteness of the
full shifted block is equivalent to positive semidefiniteness of the retained
Schur complement.

This is a finite-dimensional transfer theorem only.  It does not prove that a
Yang--Mills Hamiltonian has the required hidden-block floor uniformly in volume,
does not supply the RG/polymer tail estimate, does not pass a lattice floor to
the continuum, and does not perform Osterwalder--Schrader reconstruction.
-/

open Matrix

namespace CrossTheorem

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- Retained block shifted by a candidate lower spectral floor `μ`. -/
def retainedAtFloor (A : Matrix r r ℝ) (μ : ℝ) : Matrix r r ℝ :=
  A - μ • (1 : Matrix r r ℝ)

/-- Hidden block shifted by the same candidate lower spectral floor `μ`. -/
def hiddenAtFloor (D : Matrix h h ℝ) (μ : ℝ) : Matrix h h ℝ :=
  D - μ • (1 : Matrix h h ℝ)

/-- The full symmetric block matrix after shifting both diagonal blocks by
`μ`; equivalently, the full block matrix shifted by `μ I`. -/
def floorBlock (A : Matrix r r ℝ) (B : Matrix r h ℝ)
    (D : Matrix h h ℝ) (μ : ℝ) : Matrix (Sum r h) (Sum r h) ℝ :=
  Matrix.fromBlocks (retainedAtFloor A μ) B B.transpose (hiddenAtFloor D μ)

/-- Effective retained operator at candidate floor `μ`, after eliminating the
strictly-positive hidden shifted block. -/
noncomputable def schurAtFloor (A : Matrix r r ℝ) (B : Matrix r h ℝ)
    (D : Matrix h h ℝ) (μ : ℝ) : Matrix r r ℝ :=
  retainedAtFloor A μ -
    B * (hiddenAtFloor D μ)⁻¹ * B.transpose

/-- Shifting the full block matrix by `μ I` is exactly the same as shifting its
two diagonal blocks by `μ`. -/
theorem floorBlock_eq_full_shift
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) (μ : ℝ) :
    floorBlock A B D μ =
      symBlock A B D - μ • (1 : Matrix (Sum r h) (Sum r h) ℝ) := by
  have hOne :
      (1 : Matrix (Sum r h) (Sum r h) ℝ) =
        Matrix.fromBlocks (1 : Matrix r r ℝ) 0 0 (1 : Matrix h h ℝ) := by
    symm
    exact Matrix.fromBlocks_one
  have hShift :
      μ • (1 : Matrix (Sum r h) (Sum r h) ℝ) =
        Matrix.fromBlocks
          (μ • (1 : Matrix r r ℝ)) 0 0 (μ • (1 : Matrix h h ℝ)) := by
    rw [hOne, Matrix.fromBlocks_smul]
    simp
  rw [hShift]
  ext i j
  cases i <;> cases j <;>
    simp [floorBlock, retainedAtFloor, hiddenAtFloor, symBlock]

/-- **Finite spectral-floor Schur transfer.**  If the hidden block remains
strictly positive after shifting by `μ`, then the full shifted block is positive
semidefinite exactly when the retained Schur complement at that floor is
positive semidefinite.

No eigenvalue counting theorem or infinite-volume assertion is hidden here:
this is the finite positivity equivalence consumed by such later arguments. -/
theorem floorBlock_posSemidef_iff_schur
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) (μ : ℝ)
    (hHidden : (hiddenAtFloor D μ).PosDef)
    [Invertible (hiddenAtFloor D μ)] :
    (floorBlock A B D μ).PosSemidef ↔
      (schurAtFloor A B D μ).PosSemidef := by
  simpa [floorBlock, schurAtFloor] using
    (Matrix.PosDef.fromBlocks₂₂ (retainedAtFloor A μ) B hHidden)

/-- Same transfer written directly as positivity of the full matrix above the
candidate floor `μ`. -/
theorem full_shift_posSemidef_iff_schur
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) (μ : ℝ)
    (hHidden : (hiddenAtFloor D μ).PosDef)
    [Invertible (hiddenAtFloor D μ)] :
    (symBlock A B D - μ • (1 : Matrix (Sum r h) (Sum r h) ℝ)).PosSemidef ↔
      (schurAtFloor A B D μ).PosSemidef := by
  rw [← floorBlock_eq_full_shift A B D μ]
  exact floorBlock_posSemidef_iff_schur A B D μ hHidden

end CrossTheorem

#print axioms CrossTheorem.floorBlock_eq_full_shift
#print axioms CrossTheorem.floorBlock_posSemidef_iff_schur
#print axioms CrossTheorem.full_shift_posSemidef_iff_schur
