import Mathlib

/-!
Boundary elimination and the matrix Smith transform.
All inverse assumptions are stated as matrix equations. None is inferred from
positive eigenvalues or normality. These are uncompiled Lean proof candidates.
-/
set_option autoImplicit false
noncomputable section

namespace LightBridges
open Matrix
open scoped ComplexOrder

section Reduction
variable {n k : Type*} [Fintype n] [Fintype k]
variable [DecidableEq n] [DecidableEq k]

/-- Interior part of the Schur lift for an explicitly given right inverse. -/
theorem schur_interior_residual (A X : Matrix n n ℂ) (B : Matrix n k ℂ)
    (hAX : A * X = 1) : A * (-(X * B)) + B = 0 := by
  rw [Matrix.mul_neg, ← Matrix.mul_assoc, hAX, Matrix.one_mul]
  exact neg_add_cancel B

/-- Boundary part of the same lift, with no adjoint relation between B and C. -/
theorem schur_boundary_residual (C : Matrix k n ℂ) (X : Matrix n n ℂ)
    (B : Matrix n k ℂ) (D : Matrix k k ℂ) :
    C * (-(X * B)) + D = D - C * X * B := by
  simp only [Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]
  exact add_comm _ _

/-- The harmonic-lift equations imply equality of the boundary quadratic form.
For an actual Schur complement J=[0;I], W=[-A^{-1}B;I]. -/
theorem boundary_lift_identity (L : Matrix n n ℂ)
    (W J : Matrix n k ℂ) (Z : Matrix k k ℂ)
    (hLW : L * W = J * Z) (hWJ : W.conjTranspose * J = 1) :
    W.conjTranspose * L * W = Z := by
  rw [Matrix.mul_assoc, hLW, ← Matrix.mul_assoc, hWJ, Matrix.one_mul]

/-- The same identity for the full Hermitian part, without dividing by two. -/
theorem boundary_hermitian_identity (L : Matrix n n ℂ)
    (W J : Matrix n k ℂ) (Z : Matrix k k ℂ)
    (hLW : L * W = J * Z) (hWJ : W.conjTranspose * J = 1) :
    W.conjTranspose * (L + L.conjTranspose) * W = Z + Z.conjTranspose := by
  have h := boundary_lift_identity L W J Z hLW hWJ
  have hs : W.conjTranspose * L.conjTranspose * W = Z.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using congrArg Matrix.conjTranspose h
  rw [Matrix.mul_add, Matrix.add_mul, h, hs]

/-- Accretivity passes through the boundary reduction, even for nonnormal L. -/
theorem boundary_accretive (L : Matrix n n ℂ)
    (W J : Matrix n k ℂ) (Z : Matrix k k ℂ)
    (hLW : L * W = J * Z) (hWJ : W.conjTranspose * J = 1)
    (hL : (L + L.conjTranspose).PosSemidef) :
    (Z + Z.conjTranspose).PosSemidef := by
  have hp := hL.conjTranspose_mul_mul_same W
  rw [boundary_hermitian_identity L W J Z hLW hWJ] at hp
  exact hp

end Reduction

section Cayley
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Inverse witness W is explicit: the caller must supply (Z+I)W=I. -/
def cayleyWith (Z W : Matrix n n ℂ) : Matrix n n ℂ := (Z - 1) * W

/-- Exact matrix identity. Written as Q+Q to avoid scalar-normalization ambiguity. -/
theorem cayley_defect_identity (Z W : Matrix n n ℂ)
    (hW : (Z + 1) * W = 1) :
    1 - (cayleyWith Z W).conjTranspose * cayleyWith Z W =
      W.conjTranspose * (Z + Z.conjTranspose) * W +
      W.conjTranspose * (Z + Z.conjTranspose) * W := by
  have hone :
      W.conjTranspose * ((Z + 1).conjTranspose * (Z + 1)) * W = 1 := by
    calc
      _ = ((Z + 1) * W).conjTranspose * ((Z + 1) * W) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hW]; simp
  have hpoly :
      (Z + 1).conjTranspose * (Z + 1) -
      (Z - 1).conjTranspose * (Z - 1) =
      (Z + Z.conjTranspose) + (Z + Z.conjTranspose) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one]
    noncomm_ring
  unfold cayleyWith
  calc
    1 - ((Z - 1) * W).conjTranspose * ((Z - 1) * W) =
      W.conjTranspose * ((Z + 1).conjTranspose * (Z + 1) -
        (Z - 1).conjTranspose * (Z - 1)) * W := by
      have hdist (X Y : Matrix n n ℂ) :
          W.conjTranspose * (X-Y) * W =
          W.conjTranspose * X * W - W.conjTranspose * Y * W := by
        noncomm_ring
      rw [hdist, hone]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hpoly, Matrix.mul_add, Matrix.add_mul]

/-- A response with positive Hermitian part maps to a contractive form.
No inference from eigenvalues alone is present in the premises. -/
theorem cayley_contractivity (Z W : Matrix n n ℂ)
    (hW : (Z + 1) * W = 1)
    (hZ : (Z + Z.conjTranspose).PosSemidef) :
    (1 - (cayleyWith Z W).conjTranspose * cayleyWith Z W).PosSemidef := by
  rw [cayley_defect_identity Z W hW]
  have hp := hZ.conjTranspose_mul_mul_same W
  exact hp.add hp

end Cayley

section FullBoundaryChain
variable {n k : Type*} [Fintype n] [Fintype k]
variable [DecidableEq n] [DecidableEq k]

/-- The full non-return form is the pullback of the interior Hermitian form
along the driven harmonic lift W*V. This joins elimination to the Smith map. -/
theorem boundary_loss_pullback (L : Matrix n n ℂ)
    (W J : Matrix n k ℂ) (Z V : Matrix k k ℂ)
    (hLW : L * W = J * Z) (hWJ : W.conjTranspose * J = 1)
    (hV : (Z + 1) * V = 1) :
    1 - (cayleyWith Z V).conjTranspose * cayleyWith Z V =
      (W * V).conjTranspose * (L + L.conjTranspose) * (W * V) +
      (W * V).conjTranspose * (L + L.conjTranspose) * (W * V) := by
  rw [cayley_defect_identity Z V hV,
    ← boundary_hermitian_identity L W J Z hLW hWJ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- End-to-end algebraic passivity, with arbitrary complex finite matrices. -/
theorem passive_boundary_chain (L : Matrix n n ℂ)
    (W J : Matrix n k ℂ) (Z V : Matrix k k ℂ)
    (hLW : L * W = J * Z) (hWJ : W.conjTranspose * J = 1)
    (hV : (Z + 1) * V = 1)
    (hL : (L + L.conjTranspose).PosSemidef) :
    (1 - (cayleyWith Z V).conjTranspose * cayleyWith Z V).PosSemidef := by
  exact cayley_contractivity Z V hV (boundary_accretive L W J Z hLW hWJ hL)

end FullBoundaryChain
end LightBridges
