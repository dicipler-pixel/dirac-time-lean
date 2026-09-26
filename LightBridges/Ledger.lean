import Mathlib

/-!
Transpose symmetry and the exact finite determinant.
The analytic passage to a contour integral and all odd derivatives is supplied in
the written note, not falsely advertised as encoded by these declarations.
STATUS: uncompiled candidate; no kernel acceptance is claimed.
-/
set_option autoImplicit false
noncomputable section

namespace LightBridges
open Matrix

section InverseUniqueness
variable {R : Type*} [Monoid R]

/-- Every explicitly given left/right inverse pair agrees. -/
theorem inverse_pair_unique (A X Y : R) (hXA : X * A = 1) (hAY : A * Y = 1) :
    X = Y := by
  calc
    X = X * (A * Y) := by rw [hAY, mul_one]
    _ = (X * A) * Y := by rw [mul_assoc]
    _ = Y := by rw [hXA, one_mul]
end InverseUniqueness

section MatrixTranspose
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Transpose (not conjugate transpose) is the exact parity hypothesis. -/
theorem fixed_family_transpose (A E : Matrix n n ℂ) (t : ℂ)
    (hA : A.transpose = A) (hE : E.transpose = -E) :
    (A + t • E).transpose = A + (-t) • E := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, hA, hE]
  simp

/-- The entire finite determinant is even under the fixed skew deformation. -/
theorem fixed_family_det_even (A E : Matrix n n ℂ) (t : ℂ)
    (hA : A.transpose = A) (hE : E.transpose = -E) :
    (A + (-t) • E).det = (A + t • E).det := by
  calc
    _ = ((A + t • E).transpose).det := by
      rw [fixed_family_transpose A E t hA hE]
    _ = (A + t • E).det := Matrix.det_transpose _

/-- Exact resolvent parity from explicit inverse equations. -/
theorem inverse_transpose_pair (A B X Y : Matrix n n ℂ)
    (hB : B = A.transpose) (hXA : X * A = 1) (hYB : Y * B = 1) :
    Y = X.transpose := by
  have hBX : B * X.transpose = 1 := by
    rw [hB]
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose hXA
  exact inverse_pair_unique B Y X.transpose hYB hBX

/-- The trace sees no difference between the two paired resolvents. -/
theorem inverse_transpose_trace (A B X Y : Matrix n n ℂ)
    (hB : B = A.transpose) (hXA : X * A = 1) (hYB : Y * B = 1) :
    Y.trace = X.trace := by
  rw [inverse_transpose_pair A B X Y hB hXA hYB, Matrix.trace_transpose]

/-- Odd trace pairing: this is the first-order scalar cancellation mechanism. -/
theorem trace_symmetric_skew_zero (A E : Matrix n n ℂ)
    (hA : A.transpose = A) (hE : E.transpose = -E) :
    (A * E).trace = 0 := by
  have h : (A * E).trace = -(A * E).trace := by
    calc
      (A * E).trace = ((A * E).transpose).trace := (Matrix.trace_transpose _).symm
      _ = (-E * A).trace := by rw [Matrix.transpose_mul, hA, hE]
      _ = -(E * A).trace := by rw [neg_mul, Matrix.trace_neg]
      _ = -(A * E).trace := by rw [Matrix.trace_mul_comm E A]
  linear_combination (1 / 2 : ℂ) * h

end MatrixTranspose

/-- The earlier integer pairing certificate lifted to an actual real-valued
measurement. Geometry-to-pairing and the logarithmic level map remain separate. -/
theorem real_pairing_zero {α : Type*} (sigma : α → α) (f : α → ℝ)
    (hf : ∀ a, f (sigma a) = -f a) (l : List α)
    (hs : l.Perm (l.map sigma)) : (l.map f).sum = 0 := by
  have hp : (l.map f).sum = ((l.map sigma).map f).sum := (hs.map f).sum_eq
  have hn : ((l.map sigma).map f).sum = -(l.map f).sum := by
    clear hs hp
    induction l with
    | nil => simp
    | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, hf, ih]
      abel
  rw [hn] at hp
  linarith

end LightBridges
