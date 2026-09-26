/- FALSE CONTROL: the present observation alone does not decide the future.
   Shift on ℚ²: e₀ ↦ e₁. Observe the second coordinate. e₀ is invisible now but
   seen one step later, so "R v = 0 → R (L v) = 0" fails. This file must not compile. -/
import Mathlib

def shift (v : Fin 2 → ℚ) : Fin 2 → ℚ := ![0, v 0]

theorem present_reading_closes :
    ∀ v : Fin 2 → ℚ, v 1 = 0 → (shift v) 1 = 0 := by
  intro v hv
  simp [shift]
