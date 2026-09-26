/- FALSE CONTROL: a summary that misses an observable direction is not sufficient.
   Keep only the first coordinate of ℚ², observe the second. Two states with equal
   summaries can be read differently. This file must not compile. -/
import Mathlib

theorem first_coordinate_suffices :
    ∀ v w : Fin 2 → ℚ, v 0 = w 0 → v 1 = w 1 := by
  intro v w h
  simp [h]
