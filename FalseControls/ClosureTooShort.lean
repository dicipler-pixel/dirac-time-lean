/- FALSE CONTROL: finite closure needs all dim V steps, not dim V − 1.
   Nilpotent shift on ℚ³: e₀ ↦ e₁ ↦ e₂, observe the third coordinate. The vector e₀ is
   unseen at steps 0 and 1 but seen at step 2, so checking only 2 = dim − 1 steps is not
   enough. This file must not compile. -/
import Mathlib

def shift3 (v : Fin 3 → ℚ) : Fin 3 → ℚ := ![0, v 0, v 1]

theorem two_steps_suffice :
    ∀ v : Fin 3 → ℚ, v 2 = 0 → (shift3 v) 2 = 0 → (shift3 (shift3 v)) 2 = 0 := by
  intro v h0 h1
  simp [shift3] at h0 h1 ⊢
