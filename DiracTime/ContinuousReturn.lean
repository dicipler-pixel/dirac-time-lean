/-
The continuous-time form of the finite return criterion (Theorem P5 of "The Dirac Time of the
Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978630).

A difference `Δ` evolves as `e^{tL} Δ` and is read by `R`. It stays hidden from the reading at
every time exactly when every discrete step `R Lᵏ Δ` vanishes:

  (∀ t, R e^{tL} Δ = 0)  ↔  (∀ k, R Lᵏ Δ = 0).

Forward: the `k`-th time derivative of `R Lᵏ e^{tL} Δ` at `t = 0` is `R Lᵏ Δ`. Backward: the
exponential series. Together with `FiniteReturn` (the discrete condition needs only the first
`dim V` steps), a hidden present distinction becomes future-readable in continuous time exactly
when it does so within `dim V` discrete steps.
-/
import Mathlib

namespace DiracTime.ContinuousReturn

open NormedSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Reading an operator through `Δ` and `R`: `M ↦ R (M Δ)`. -/
noncomputable def reading (R : V →L[ℝ] W) (Δ : V) : (V →L[ℝ] V) →L[ℝ] W :=
  R.comp (ContinuousLinearMap.apply ℝ V Δ)

theorem reading_apply (R : V →L[ℝ] W) (Δ : V) (M : V →L[ℝ] V) :
    reading R Δ M = R (M Δ) := rfl

/-- The `k`-th derivative profile `t ↦ R (Lᵏ e^{tL} Δ)`. -/
noncomputable def profile (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V) (k : ℕ) (t : ℝ) : W :=
  reading R Δ (L ^ k * exp (t • L))

theorem profile_hasDerivAt (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V) (k : ℕ) (t : ℝ) :
    HasDerivAt (profile R L Δ k) (profile R L Δ (k + 1) t) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) L t).const_mul (L ^ k)
  have h2 := (reading R Δ).hasFDerivAt.comp_hasDerivAt t h
  unfold profile
  convert h2 using 1
  rw [pow_succ, mul_assoc]
  rfl

/-- **Continuous-time return criterion.** The reading of `e^{tL} Δ` vanishes at every time
exactly when every discrete step `R Lᵏ Δ` vanishes. -/
theorem hidden_forever_iff (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V) :
    (∀ t : ℝ, R (exp (t • L) Δ) = 0) ↔ ∀ k : ℕ, R ((L ^ k) Δ) = 0 := by
  constructor
  · intro h
    have hall : ∀ k : ℕ, ∀ t : ℝ, profile R L Δ k t = 0 := by
      intro k
      induction k with
      | zero =>
        intro t
        simp only [profile, reading_apply, pow_zero, one_mul]
        exact h t
      | succ k ih =>
        intro t
        have hd := profile_hasDerivAt R L Δ k t
        have hz : profile R L Δ k = fun _ => 0 := funext ih
        rw [hz] at hd
        exact (hd.unique (hasDerivAt_const t (0 : W))).trans rfl
    intro k
    have := hall k 0
    simpa [profile, reading_apply] using this
  · intro h t
    have hsum := expSeries_summable' (𝕂 := ℝ) (t • L)
    rw [exp_eq_tsum ℝ]
    show reading R Δ (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (t • L) ^ n) = 0
    rw [(reading R Δ).map_tsum hsum]
    have hz : ∀ n : ℕ, reading R Δ (((n.factorial : ℝ)⁻¹) • (t • L) ^ n) = 0 := by
      intro n
      rw [smul_pow, map_smul, map_smul, reading_apply, h n, smul_zero, smul_zero]
    simp only [hz, tsum_zero]

end DiracTime.ContinuousReturn
