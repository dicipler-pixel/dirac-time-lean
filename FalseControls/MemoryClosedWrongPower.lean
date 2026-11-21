-- FALSE CONTROL: DT-C222 closed form with exponent n+1.
import Mathlib
theorem memory_off_by_one_power :
    (0 : ℚ) + (1 - 1 / 2) ^ (0 + 1) * (2 - 0) = 2 := by
  norm_num
