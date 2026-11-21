/-
Two-level speed identity and chirality bound (§16.4, DT-C168 and DT-C169, of
"The Dirac Time of the Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978630).

Along `d(s) ≠ 0`, `ρ = ‖d‖` has derivative `⟪d, ḋ⟫ / ρ`, and the direction `n = d/ρ` is a unit vector.
The identities `‖ḋ‖² = ρ̇² + Δ² g_ss` and `ρ² χ̇² ≤ Δ² g_ss` are not proved in this file.
-/
import Mathlib

namespace DiracTime.TwoLevelPath

open InnerProductSpace

variable {d : ℝ → EuclideanSpace ℝ (Fin 3)} {d' : ℝ → EuclideanSpace ℝ (Fin 3)}

theorem rho_hasDerivAt (hd : ∀ s, HasDerivAt d (d' s) s) (h0 : ∀ s, d s ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => ‖d s‖) (⟪d s, d' s⟫_ℝ / ‖d s‖) s := by
  have hsq := (hd s).norm_sq
  have hpos : ‖d s‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (h0 s))
  have hsqrt := (Real.hasDerivAt_sqrt hpos).scomp s hsq
  have hfun : (fun u => Real.sqrt (‖d u‖ ^ 2)) = fun u => ‖d u‖ := by
    ext u
    exact Real.sqrt_sq (norm_nonneg _)
  refine (hsqrt.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun.symm)).congr_deriv ?_
  rw [Real.sqrt_sq (norm_nonneg _)]
  field_simp
  ring

noncomputable def direction (d : ℝ → EuclideanSpace ℝ (Fin 3)) (s : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (‖d s‖)⁻¹ • d s

theorem direction_norm {s : ℝ} (h0 : d s ≠ 0) : ‖direction d s‖ = 1 := by
  rw [direction, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr h0), mul_comm]
  exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0)

end DiracTime.TwoLevelPath
