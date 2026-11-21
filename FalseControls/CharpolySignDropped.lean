-- FALSE CONTROL: DT-C032 drops (-1)^n. For n = 1, χ(-x) = -χ(x), not χ(x).
import Mathlib
theorem charpoly_without_sign (x : ℚ) : (-x - (1 : ℚ)) = (x - 1) := by
  linarith
