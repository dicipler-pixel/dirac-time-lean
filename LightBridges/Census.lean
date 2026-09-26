import Mathlib
import LightBridges.Algebra

/-! A finite transition-window census inequality. It bounds that census, not an
unfiltered collection of pairwise separated needles. NOT COMPILED here. -/
set_option autoImplicit false

namespace LightBridges

/-- The exact scalar estimate needed for a transition-window census. -/
theorem transition_weight_lower (eps x : ℝ)
    (hxlo : eps ≤ x) (hxhi : x ≤ 1 - eps) :
    eps * (1 - eps) ≤ x * (1 - x) := by
  have hp : 0 ≤ (x - eps) * (1 - eps - x) :=
    mul_nonneg (sub_nonneg.mpr hxlo) (sub_nonneg.mpr hxhi)
  nlinarith

/-- No division is used, so empty and degenerate windows remain well-defined. -/
theorem transition_census_budget {ι : Type*} [Fintype ι]
    (nu : ι → ℝ) (eps : ℝ) (hnu : ∀ i, 0 ≤ nu i ∧ nu i ≤ 1) :
    (∑ i, (if eps ≤ nu i ∧ nu i ≤ 1 - eps then (1 : ℝ) else 0)) *
        (eps * (1 - eps)) ≤ ∑ i, nu i * (1 - nu i) := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hw : eps ≤ nu i ∧ nu i ≤ 1 - eps
  · simp only [if_pos hw, one_mul]
    exact transition_weight_lower eps (nu i) hw.1 hw.2
  · simp only [if_neg hw, zero_mul]
    exact mul_nonneg (hnu i).1 (sub_nonneg.mpr (hnu i).2)

/-- Positive resolution provides a legitimate denominator for the budget. -/
theorem transition_denominator_pos (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1) :
    0 < eps * (1 - eps) := by
  exact mul_pos h0 (sub_pos.mpr h1)


/-- Exact window-to-coupling threshold equivalence; no fit or asymptotic is used. -/
theorem transition_window_iff_weight (eps x : ℝ) (heps : eps ≤ 1/2) :
    (eps ≤ x ∧ x ≤ 1-eps) ↔ eps*(1-eps) ≤ x*(1-x) := by
  constructor
  · intro hx
    exact transition_weight_lower eps x hx.1 hx.2
  · intro hw
    constructor
    · by_contra h
      have hx : x < eps := lt_of_not_ge h
      have hp : 0 < (eps-x)*(1-eps-x) :=
        mul_pos (sub_pos.mpr hx) (by linarith)
      nlinarith
    · by_contra h
      have hx : 1-eps < x := lt_of_not_ge h
      have hp : 0 < (x-eps)*(x-(1-eps)) :=
        mul_pos (by linarith) (sub_pos.mpr hx)
      nlinarith

/-- Once the eigenvalues of BB^* are nu(1-nu), the two finite counts coincide.
The matrix spectral mapping step is proved in the written supplement. -/
theorem census_equals_coupling_count {ι : Type*} [Fintype ι]
    (nu : ι → ℝ) (eps : ℝ) (heps : eps ≤ 1/2) :
    (∑ i, if eps ≤ nu i ∧ nu i ≤ 1-eps then (1 : ℕ) else 0) =
      ∑ i, if eps*(1-eps) ≤ nu i*(1-nu i) then (1 : ℕ) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  simp only [transition_window_iff_weight eps (nu i) heps]

/-- Boundary mixing is maximal at half occupation. -/
theorem boundary_mixing_peak (x : ℝ) :
    x*(1-x) = 1/4 - (x-1/2)^2 := by ring


/-- The actual block-matrix premise P^2=P supplies C-C^2=BB^*.
Self-adjointness of the off-diagonal pair is encoded by B.conjTranspose. -/
theorem projector_block_coupling {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (C : Matrix n n ℂ) (B : Matrix n m ℂ) (D : Matrix m m ℂ)
    (hP : Matrix.fromBlocks C B B.conjTranspose D *
      Matrix.fromBlocks C B B.conjTranspose D = Matrix.fromBlocks C B B.conjTranspose D) :
    C - C*C = B * B.conjTranspose := by
  have h := congrArg Matrix.toBlocks₁₁ hP
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁] at h
  exact boundary_defect_of_block_idempotence C (B * B.conjTranspose) h

end LightBridges

namespace LightBridges
section FilterRange
variable {V W : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]

/-- Filtering constrains the range of the response, not an unfiltered family. -/
theorem filtered_response_range (F : V →ₗ[ℂ] V) (T : W →ₗ[ℂ] V) :
    LinearMap.range (F.comp T) ≤ LinearMap.range F := by
  rintro y ⟨x, rfl⟩
  exact ⟨T x, rfl⟩

/-- The finite-dimensional boundary channel rank is at most the filter rank.
The singular-value threshold interpretation is in the written supplement. -/
theorem filtered_response_finrank [FiniteDimensional ℂ V]
    (F : V →ₗ[ℂ] V) (T : W →ₗ[ℂ] V) :
    Module.finrank ℂ (LinearMap.range (F.comp T)) ≤
      Module.finrank ℂ (LinearMap.range F) := by
  exact Submodule.finrank_mono (filtered_response_range F T)

end FilterRange
end LightBridges
