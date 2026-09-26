/- FALSE CONTROL: the weak-value bound needs a normalized postselected state.
   One dimension, f = 2, i = 1, A = identity: |⟨f|A|i⟩|² = 4 but ⟨i|A²|i⟩ = 1.
   This file must not compile. -/
import Mathlib

theorem unnormalized_bound : ‖(2 : ℂ) * 1‖ ^ 2 ≤ ‖(1 : ℂ)‖ ^ 2 := by
  simp
