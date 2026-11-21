/-
Theorem P1(3) in metric/curvature form (p. 79 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

For block tangents `V = [[0, X], [X†, 0]]` and `W = [[0, Y], [Y†, 0]]`,
`g_P(V, W) = ½ Re Tr(V W)` and `Ω_P(V, W) = i Tr(P [V, W])` satisfy
`|Ω_P(V, W)| ≤ 2 √(g_P(V, V) g_P(W, W) − g_P(V, W)²)`.
-/
import DiracTime.ProjectorBlocks
import DiracTime.ProjectorTangent

namespace DiracTime.BlockCurvature

open Matrix Complex DiracTime.ProjectorBlocks DiracTime.ProjectorTangent
open scoped InnerProductSpace

variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]

/-- Frobenius identification of a block with a Euclidean vector. -/
noncomputable def toEuc (X : Matrix m p ℂ) : EuclideanSpace ℂ (m × p) :=
  WithLp.toLp 2 fun ij => X ij.1 ij.2

theorem scalar_inner (a b : ℂ) : ⟪a, b⟫_ℂ = star a * b := by
  simp [inner, mul_comm]

omit [DecidableEq m] [DecidableEq p] in
theorem toEuc_inner (X Y : Matrix m p ℂ) :
    ⟪toEuc X, toEuc Y⟫_ℂ = trace (Xᴴ * Y) := by
  classical
  simp only [toEuc, PiLp.inner_apply, scalar_inner]
  rw [Fintype.sum_prod_type, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

omit [DecidableEq m] [DecidableEq p] in
theorem toEuc_norm_sq (X : Matrix m p ℂ) : ‖toEuc X‖ ^ 2 = (trace (X * Xᴴ)).re := by
  have h := toEuc_inner X X
  rw [inner_self_eq_norm_sq_to_K, ← Matrix.trace_mul_comm] at h
  have hre := congrArg re h
  have hcast : ((‖toEuc X‖ : ℂ) ^ 2).re = ‖toEuc X‖ ^ 2 := by
    rw [pow_two, mul_re, ofReal_re, ofReal_im]
    ring
  exact hcast.symm.trans hre

/-- **Theorem P1(3).** `|Ω_P(V, W)| ≤ 2 √(g(V,V) g(W,W) − g(V,W)²)` for block tangents. -/
theorem metric_curvature_blocks (X Y : Matrix m p ℂ) :
    ‖I * trace (occ * (tangentBlock X * tangentBlock Y - tangentBlock Y * tangentBlock X))‖ ≤
      2 * Real.sqrt ((trace (tangentBlock X * tangentBlock X)).re / 2 *
          ((trace (tangentBlock Y * tangentBlock Y)).re / 2) -
        ((trace (tangentBlock X * tangentBlock Y)).re / 2) ^ 2) := by
  have hcs := metric_curvature_inequality (toEuc X) (toEuc Y)
  rw [curvature_block X Y]
  have hleft : ‖(-2 : ℂ) * ((trace (X * Yᴴ)).im : ℂ)‖ =
      |2 * (⟪toEuc X, toEuc Y⟫_ℂ).im| := by
    have him : (⟪toEuc X, toEuc Y⟫_ℂ).im = - (trace (X * Yᴴ)).im := by
      rw [toEuc_inner, trace_adjoint_left, star_def, conj_im]
    rw [him]
    simp [Complex.norm_real, abs_mul, abs_neg]
  have hgX : (trace (tangentBlock X * tangentBlock X)).re / 2 = ‖toEuc X‖ ^ 2 := by
    rw [metric_block, toEuc_norm_sq]
  have hgY : (trace (tangentBlock Y * tangentBlock Y)).re / 2 = ‖toEuc Y‖ ^ 2 := by
    rw [metric_block, toEuc_norm_sq]
  have hg : (trace (tangentBlock X * tangentBlock Y)).re / 2 = (⟪toEuc X, toEuc Y⟫_ℂ).re := by
    rw [metric_block, toEuc_inner, trace_adjoint_left, star_def, conj_re]
  rw [hleft, hgX, hgY, hg]
  exact hcs

end DiracTime.BlockCurvature
