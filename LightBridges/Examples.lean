import Mathlib

/-! Exact counterexamples protecting the scope of the light-paper statements.
NOT COMPILED here. No native evaluation is used in any proof script. -/
set_option autoImplicit false
noncomputable section

namespace LightBridges
open Matrix

/-- Two genuinely idempotent but not both orthogonal projectors. -/
def obliqueP0 : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]
def obliqueP1 : Matrix (Fin 2) (Fin 2) ℚ := !![2, -2; 1, -1]

theorem obliqueP0_idempotent : obliqueP0 * obliqueP0 = obliqueP0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueP0, Matrix.mul_apply, Fin.sum_univ_two]

theorem obliqueP1_idempotent : obliqueP1 * obliqueP1 = obliqueP1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [obliqueP1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Trace of two oblique projectors can exceed one; it is not a cosine squared. -/
theorem oblique_trace_two : (obliqueP0 * obliqueP1).trace = 2 := by
  norm_num [obliqueP0, obliqueP1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Three pairwise separated unit vectors already fit in two dimensions. -/
def separatedVectors : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 3/5, 3/5; 0, 4/5, -4/5]

def separatedGram : Matrix (Fin 3) (Fin 3) ℚ :=
  separatedVectors.transpose * separatedVectors

theorem separatedGram_value :
    separatedGram = !![1, 3/5, 3/5; 3/5, 1, -7/25; 3/5, -7/25, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [separatedGram, separatedVectors, Matrix.mul_apply, Fin.sum_univ_two]

theorem separatedGram_singular : separatedGram.det = 0 := by
  rw [separatedGram_value]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.vecHead, Matrix.vecTail]

/-- All three pairwise squared-sine separations exceed or equal 16/25. -/
theorem pairwise_separation_values :
    1-(3/5:ℚ)^2=16/25 ∧ 1-(-7/25:ℚ)^2=576/625 ∧ (16/25:ℚ) ≤ 576/625 := by
  norm_num

/-- A rank-two pure-marker Gram can obey D^2+V^2=1: use orthogonal markers. -/
theorem orthogonal_marker_det : (1 : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by simp

/-- Raw commutator stress has no automatic sine-squared normalization. -/
def stressC : Matrix (Fin 2) (Fin 2) ℚ := !![0, 2; 0, 0]

theorem stress_commutator :
    stressC * stressC.transpose - stressC.transpose * stressC = !![4,0;0,-4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stressC, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem stress_exceeds_one : (1/2:ℚ) * (4^2 + (-4)^2) = 16 := by norm_num

/-- Probe-symmetry yields nonnegative real round-trip expressions only with
real, positive normalization factors. No complex spectral assertion is made. -/
theorem real_round_trip_nonnegative (s ni nj gap : ℝ)
    (hi : 0 < ni) (hj : 0 < nj) :
    0 ≤ s^2 / (ni * nj * gap^2) := by positivity

end LightBridges
