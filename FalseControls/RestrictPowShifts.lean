-- FALSE CONTROL: DT-C008 real restriction of a square shifts the exponent.
import Mathlib
theorem restrict_pow_shift : ((2 : ℚ) ^ 2) = 2 ^ 3 := by
  norm_num
