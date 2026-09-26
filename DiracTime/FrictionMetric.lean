/-
Friction on projector rotations (§12.6 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978631).

For a slowly driven nondegenerate spectrum in contact with a bath, the excess-work tensor
has, for each level pair `m ≠ n`, the term `c_mn |Ḣ_mn|² (p_m − p_n)/(E_n − E_m)`, while the
intrinsic metric of the pair is `g_mn = |Ḣ_mn|²/(E_n − E_m)²`.

Proved here, for the declared relaxation model's pairwise formulas:
* the pair friction counted in both orders is `ζ_mn = 2 c_mn (p_m − p_n)(E_n − E_m) g_mn`;
* with Gibbs weights `p ∝ e^{−βE}` and `β ≥ 0` every pair weight `(p_m − p_n)(E_n − E_m)` is
  nonnegative;
* two levels: the population gap is `p₋ − p₊ = tanh(β∆/2)`;
* zero temperature: a weighted sum `Σ wₙ gₙ` with `gₙ ≥ 0` lies between `(min w) Σ gₙ` and
  `(max w) Σ gₙ` — a band, not a proportionality.

The derivation of the pairwise formulas from the relaxation model (first order in the
driving rate) is not formalized here.
-/
import Mathlib

namespace DiracTime.FrictionMetric

/-- The friction of a level pair, counted in both orders, is the intrinsic metric of that
pair reweighted by twice the population difference times the gap times the relaxation
factor. -/
theorem pair_friction_eq_weighted_metric (c h2 pm pn Em En : ℝ) (hE : En ≠ Em) :
    2 * (c * h2 * ((pm - pn) / (En - Em))) =
      2 * c * (pm - pn) * (En - Em) * (h2 / (En - Em) ^ 2) := by
  have h : En - Em ≠ 0 := sub_ne_zero.mpr hE
  field_simp

/-- Gibbs weights decrease with energy, so every pair weight is nonnegative. -/
theorem gibbs_pair_weight_nonneg (β Em En : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (Real.exp (-β * Em) - Real.exp (-β * En)) * (En - Em) := by
  rcases le_total Em En with h | h
  · apply mul_nonneg
    · have hle : -β * En ≤ -β * Em := by nlinarith
      linarith [Real.exp_le_exp.mpr hle]
    · linarith
  · apply mul_nonneg_of_nonpos_of_nonpos
    · have hle : -β * Em ≤ -β * En := by nlinarith
      linarith [Real.exp_le_exp.mpr hle]
    · linarith

/-- Two levels: the Gibbs population gap is `tanh(β∆/2)` (here `x = β∆/2`). -/
theorem two_level_population_gap (x : ℝ) :
    Real.exp x / (Real.exp x + Real.exp (-x)) - Real.exp (-x) / (Real.exp x + Real.exp (-x)) =
      Real.tanh x := by
  have h : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  field_simp

/-- Zero temperature: a band, not a proportionality. -/
theorem weighted_sum_band {ι : Type*} (s : Finset ι) (w g : ι → ℝ) (lo hi : ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hw : ∀ i ∈ s, lo ≤ w i ∧ w i ≤ hi) :
    lo * ∑ i ∈ s, g i ≤ ∑ i ∈ s, w i * g i ∧ ∑ i ∈ s, w i * g i ≤ hi * ∑ i ∈ s, g i := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_right (hw i hi').1 (hg i hi')
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_right (hw i hi').2 (hg i hi')

end DiracTime.FrictionMetric
