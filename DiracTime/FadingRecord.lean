/-
Fading-record bounds (§23.2, DT-C305, of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

For `ν > 0`, `u ≥ 0` and `f ≥ 0` integrable on `[t₀, t₀ + u]`,
`A = ∫ f` and `A_ν = ∫ e^{−ν(t₀+u−s)} f(s) ds` satisfy
`e^{−νu} A ≤ A_ν ≤ A` and `0 ≤ A − A_ν ≤ (1 − e^{−νu}) A ≤ ν u A`.
-/
import Mathlib

namespace DiracTime.FadingRecord

open intervalIntegral MeasureTheory

theorem one_sub_exp_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

theorem fading_record_bounds {f : ℝ → ℝ} {ν u t0 : ℝ}
    (hν : 0 < ν) (hu : 0 ≤ u)
    (hf : IntervalIntegrable f volume t0 (t0 + u))
    (hfn : ∀ s ∈ Set.Icc t0 (t0 + u), 0 ≤ f s) :
    let weight := fun s => Real.exp (-ν * (t0 + u - s))
    let A := ∫ s in t0..(t0 + u), f s
    let Aν := ∫ s in t0..(t0 + u), weight s * f s
    Real.exp (-ν * u) * A ≤ Aν ∧ Aν ≤ A ∧ 0 ≤ A - Aν ∧
      A - Aν ≤ (1 - Real.exp (-ν * u)) * A ∧
      (1 - Real.exp (-ν * u)) * A ≤ ν * u * A := by
  intro weight A Aν
  have hle : t0 ≤ t0 + u := by linarith
  have hweight : Continuous weight := by
    unfold weight
    fun_prop
  have hwint : IntervalIntegrable (fun s => weight s * f s) volume t0 (t0 + u) :=
    hf.continuousOn_mul hweight.continuousOn
  have hlow : ∀ s ∈ Set.Icc t0 (t0 + u), Real.exp (-ν * u) * f s ≤ weight s * f s := by
    intro s hs
    have hspan : 0 ≤ t0 + u - s ∧ t0 + u - s ≤ u := by
      constructor <;> linarith [hs.1, hs.2]
    have hexp : Real.exp (-ν * u) ≤ weight s := by
      unfold weight
      apply Real.exp_le_exp.mpr
      have : -ν * u ≤ -ν * (t0 + u - s) := by nlinarith [hν]
      linarith
    have hf0 : 0 ≤ f s := hfn s hs
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hexp hf0
  have hhigh : ∀ s ∈ Set.Icc t0 (t0 + u), weight s * f s ≤ f s := by
    intro s hs
    have hexp : weight s ≤ 1 := by
      unfold weight
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ t0 + u - s := by linarith [hs.2]
      nlinarith [hν, this]
    have hf0 : 0 ≤ f s := hfn s hs
    have := mul_le_mul_of_nonneg_right hexp hf0
    simpa using this
  have hAνlow := integral_mono_on hle (hf.const_mul (Real.exp (-ν * u))) hwint hlow
  have hAνhigh := integral_mono_on hle hwint hf hhigh
  have hbracket : (1 - Real.exp (-ν * u)) * A ≤ ν * u * A := by
    have hfac := one_sub_exp_le (ν * u)
    have hA : 0 ≤ A := integral_nonneg hle fun s hs => hfn s hs
    simpa [mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_right hfac hA
  refine ⟨?_, ?_, ?_, ?_, hbracket⟩
  · simpa [A, Aν, intervalIntegral.integral_const_mul] using hAνlow
  · simpa [A, Aν] using hAνhigh
  · linarith
  · have hdiff : A - Aν ≤ (1 - Real.exp (-ν * u)) * A := by
      have hscale : Real.exp (-ν * u) * A ≤ Aν := by
        simpa [A, Aν, intervalIntegral.integral_const_mul] using hAνlow
      nlinarith
    exact hdiff

end DiracTime.FadingRecord
