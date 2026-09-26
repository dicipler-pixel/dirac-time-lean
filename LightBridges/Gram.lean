import Mathlib

/-! Orthogonal Gram statements only. These are NOT assertions about positivity of
arbitrary oblique Riesz projectors or indefinite intrinsic pairings.
STATUS: uncompiled candidate formalization; see STATUS.json. -/
set_option autoImplicit false
noncomputable section

namespace LightBridges
open Matrix
open scoped ComplexOrder

section Gram
variable {n m k a : Type*}
variable [Fintype n] [Fintype m] [Fintype k] [Fintype a]
variable [DecidableEq n] [DecidableEq m] [DecidableEq k] [DecidableEq a]

/-- Any finite Gram remains positive; purity is not a hypothesis. -/
theorem gram_posSemidef (B : Matrix n a ℂ) :
    (B.conjTranspose * B).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self B

/-- Vectorized marker amplitudes. W may have any rank. Physically rho=W W^*.
The marker transformations need not even be unitary for positivity. -/
def markerColumns (W : Matrix n m ℂ) (U : a → Matrix n n ℂ) :
    Matrix (n × m) a ℂ := fun ij label => (U label * W) ij.1 ij.2

def markerGram (W : Matrix n m ℂ) (U : a → Matrix n n ℂ) : Matrix a a ℂ :=
    (markerColumns W U).conjTranspose * markerColumns W U

/-- Mixed-state marker positivity from an explicit rectangular Gram factor. -/
theorem markerGram_posSemidef (W : Matrix n m ℂ) (U : a → Matrix n n ℂ) :
    (markerGram W U).PosSemidef := by
  exact gram_posSemidef (markerColumns W U)

/-- The orthogonal projector of an isometric frame. -/
theorem frame_projector_idempotent (Q : Matrix n k ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    (Q * Q.conjTranspose) * (Q * Q.conjTranspose) = Q * Q.conjTranspose := by
  calc
    _ = Q * (Q.conjTranspose * Q) * Q.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = Q * Q.conjTranspose := by rw [hQ]; simp

theorem frame_projector_selfadjoint (Q : Matrix n k ℂ) :
    (Q * Q.conjTranspose).conjTranspose = Q * Q.conjTranspose := by simp

/-- Algebra underlying the principal-angle sine-squared operator.
Identification of singular values with principal angles is not encoded here. -/
theorem frame_angle_kernel (Q0 Q1 : Matrix n k ℂ)
    (hQ1 : Q1.conjTranspose * Q1 = 1) :
    Q1.conjTranspose * (1 - Q0 * Q0.conjTranspose) * Q1 =
      1 - (Q0.conjTranspose * Q1).conjTranspose * (Q0.conjTranspose * Q1) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hQ1]

/-- Loss of definiteness cannot occur in B^*B, even when B loses rank.
This preserves the distinction: degeneracy is possible; negative directions are not. -/
theorem filtered_gram_posSemidef (B : Matrix n a ℂ) (F : Matrix m n ℂ) :
    ((F * B).conjTranspose * (F * B)).PosSemidef := by
  exact gram_posSemidef (F * B)

/-- Scaled displacement identity for a unitary/isometric square matrix. -/
theorem displacement_gram (U : Matrix n n ℂ)
    (hU : U.conjTranspose * U = 1) :
    (1 - U).conjTranspose * (1 - U) = 1 + 1 - U - U.conjTranspose := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  calc
    (1 - U.conjTranspose) * (1 - U) =
        1 - U - U.conjTranspose + U.conjTranspose * U := by noncomm_ring
    _ = 1 + 1 - U - U.conjTranspose := by rw [hU]; abel

/-- Complementary graph-overlap/displacement squares sum to four identities. -/
theorem graph_parallelogram (U : Matrix n n ℂ)
    (hU : U.conjTranspose * U = 1) :
    (1 + U).conjTranspose * (1 + U) +
      (1 - U).conjTranspose * (1 - U) = 1 + 1 + 1 + 1 := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  calc
    (1 + U.conjTranspose) * (1 + U) + (1 - U.conjTranspose) * (1 - U) =
      1 + 1 + U.conjTranspose * U + U.conjTranspose * U := by noncomm_ring
    _ = 1 + 1 + 1 + 1 := by rw [hU]

end Gram
end LightBridges
