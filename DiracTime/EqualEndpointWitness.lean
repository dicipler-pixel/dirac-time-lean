/-
The exact equal-endpoint witness (§11.4 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978631).

A path qubit and a record qubit share one excitation; a gauge history writes its Wilson
phase `Φ` onto the arm-1 branch. After a later exchange acting for a time with `θ = g t`,
the two amplitudes are, up to the common factor `1/√2`,

  w₀ = cos θ − i e^{iΦ} sin θ,       w₁ = e^{iΦ} cos θ − i sin θ.

Proved here:
* the key identity `|a − i b e^{iΦ}|² = a² + b² + 2ab sin Φ`;
* `|w₀|² = 1 + sin 2θ sin Φ` and `|w₁|² = 1 − sin 2θ sin Φ`, so `⟨Z_P⟩(θ) = sin 2θ sin Φ`;
* at `θ = 0` both populations equal `1` whatever `Φ` is: no present record distinguishes
  the histories;
* the probe reads `sin Φ` only, so histories with `Φ` and `π − Φ` stay equivalent under it:
  the history quotient depends on the declared probe.
-/
import Mathlib

namespace DiracTime.EqualEndpointWitness

open Complex

/-- The key identity: `|a − i b e^{iΦ}|² = a² + b² + 2 a b sin Φ`. -/
theorem normSq_sub_I_mul_exp (a b Φ : ℝ) :
    normSq ((a : ℂ) - I * (b : ℂ) * exp (Φ * I)) = a ^ 2 + b ^ 2 + 2 * a * b * Real.sin Φ := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, normSq_apply]
  simp [mul_re, mul_im, cos_ofReal_re, sin_ofReal_re]
  linear_combination b ^ 2 * Real.sin_sq_add_cos_sq Φ

/-- Arm-0 amplitude (times `√2`). -/
noncomputable def w₀ (θ Φ : ℝ) : ℂ := (Real.cos θ : ℂ) - I * exp (Φ * I) * (Real.sin θ : ℂ)

/-- Arm-1 amplitude (times `√2`). -/
noncomputable def w₁ (θ Φ : ℝ) : ℂ := exp (Φ * I) * (Real.cos θ : ℂ) - I * (Real.sin θ : ℂ)

theorem normSq_w₀ (θ Φ : ℝ) : normSq (w₀ θ Φ) = 1 + Real.sin (2 * θ) * Real.sin Φ := by
  rw [w₀, Real.sin_two_mul, exp_mul_I, ← ofReal_cos, ← ofReal_sin, normSq_apply]
  simp [mul_re, mul_im, cos_ofReal_re, sin_ofReal_re]
  linear_combination Real.sin_sq_add_cos_sq θ + Real.sin θ ^ 2 * Real.sin_sq_add_cos_sq Φ

theorem normSq_w₁ (θ Φ : ℝ) : normSq (w₁ θ Φ) = 1 - Real.sin (2 * θ) * Real.sin Φ := by
  rw [w₁, Real.sin_two_mul, exp_mul_I, ← ofReal_cos, ← ofReal_sin, normSq_apply]
  simp [mul_re, mul_im, cos_ofReal_re, sin_ofReal_re]
  linear_combination Real.sin_sq_add_cos_sq θ + Real.cos θ ^ 2 * Real.sin_sq_add_cos_sq Φ

/-- The later readout: `⟨Z_P⟩(θ) = (|w₀|² − |w₁|²) / 2 = sin 2θ sin Φ`. -/
theorem expectation_Z (θ Φ : ℝ) :
    (normSq (w₀ θ Φ) - normSq (w₁ θ Φ)) / 2 = Real.sin (2 * θ) * Real.sin Φ := by
  rw [normSq_w₀, normSq_w₁]
  ring

/-- Before the exchange (`θ = 0`) both populations are equal whatever the Wilson phase:
no present record distinguishes the histories. -/
theorem present_populations_equal (Φ₁ Φ₂ : ℝ) :
    normSq (w₀ 0 Φ₁) = normSq (w₀ 0 Φ₂) ∧ normSq (w₁ 0 Φ₁) = normSq (w₁ 0 Φ₂) := by
  simp [normSq_w₀, normSq_w₁]

/-- A nonzero Wilson phase is read later: at `θ = π/4`, `⟨Z_P⟩ = sin Φ`. -/
theorem later_readout (Φ : ℝ) :
    (normSq (w₀ (Real.pi / 4) Φ) - normSq (w₁ (Real.pi / 4) Φ)) / 2 = Real.sin Φ := by
  rw [expectation_Z, show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two, one_mul]

/-- The history quotient depends on the probe: this probe cannot separate `Φ` from `π − Φ`. -/
theorem probe_blind_to_supplement (θ Φ : ℝ) :
    (normSq (w₀ θ Φ) - normSq (w₁ θ Φ)) / 2 =
      (normSq (w₀ θ (Real.pi - Φ)) - normSq (w₁ θ (Real.pi - Φ))) / 2 := by
  rw [expectation_Z, expectation_Z, Real.sin_pi_sub]

end DiracTime.EqualEndpointWitness
