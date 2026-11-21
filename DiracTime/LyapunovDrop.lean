/-
Lyapunov dissipation (§23, DT-C297, of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

If `ȧ = v`, `m v̇ = -γ v - ∂_a U`, `η_y ẏ = -∂_y U`, `η_r ṙ = -∂_r U` and
`H = m v²/2 + U`, then `Ḣ = -γ v² - η_y ẏ² - η_r ṙ²`. Nonnegativity of the
coefficients, required for `Ḣ ≤ 0`, is an explicit hypothesis. LaSalle's
invariance principle is not formalized.
-/
import Mathlib

namespace DiracTime.LyapunovDrop

theorem lyapunov_derivative (m γ ηy ηr : ℝ) (hm : m ≠ 0)
    {v U : ℝ → ℝ} {a' v' y' r' U' dA dY dR : ℝ → ℝ}
    (hdv : ∀ t, HasDerivAt v (v' t) t)
    (hdU : ∀ t, HasDerivAt U (U' t) t)
    (hchain : ∀ t, U' t = dA t * a' t + dY t * y' t + dR t * r' t)
    (hva : ∀ t, a' t = v t)
    (hvv : ∀ t, m * v' t = -γ * v t - dA t)
    (hy : ∀ t, ηy * y' t = -dY t) (hr : ∀ t, ηr * r' t = -dR t) (t : ℝ) :
    HasDerivAt (fun t => m / 2 * (v t) ^ 2 + U t)
      (-γ * (v t) ^ 2 - ηy * (y' t) ^ 2 - ηr * (r' t) ^ 2) t := by
  have hv2 := (hdv t).pow 2
  have hkin := (hasDerivAt_const t (m / 2)).mul hv2
  have hH := hkin.add (hdU t)
  rw [hchain t, hva t] at hH
  have hy' : dY t * y' t = -(ηy * (y' t) ^ 2) := by
    have h := hy t
    calc
      dY t * y' t = -(-dY t) * y' t := by ring
      _ = -(ηy * y' t) * y' t := by rw [← h]
      _ = -(ηy * (y' t) ^ 2) := by ring
  have hr' : dR t * r' t = -(ηr * (r' t) ^ 2) := by
    have h := hr t
    calc
      dR t * r' t = -(-dR t) * r' t := by ring
      _ = -(ηr * r' t) * r' t := by rw [← h]
      _ = -(ηr * (r' t) ^ 2) := by ring
  rw [hy', hr'] at hH
  convert hH using 1
  have hv := hvv t
  have hv' : v' t = (-γ * v t - dA t) / m := by
    field_simp [hm]
    linear_combination hv
  rw [hv']
  field_simp [hm]
  ring

theorem lyapunov_nonpos {γ ηy ηr v y' r' : ℝ}
    (hγ : 0 ≤ γ) (hηy : 0 ≤ ηy) (hηr : 0 ≤ ηr) :
    -γ * v ^ 2 - ηy * y' ^ 2 - ηr * r' ^ 2 ≤ 0 := by
  nlinarith [sq_nonneg v, sq_nonneg y', sq_nonneg r']

end DiracTime.LyapunovDrop
