/- FALSE CONTROL: not every direction is tangent to a projector.
   P = diag(1, 0) and V = 1: the occupied block P V P = P is not zero, so V is not a
   tangent at P. This file must not compile. -/
import Mathlib

theorem identity_is_tangent :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) * 1 * !![1, 0; 0, 0] = 0 := by
  simp
