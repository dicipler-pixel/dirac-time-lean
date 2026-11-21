-- FALSE CONTROL: DT-C008 some positive time with value 1 forces that value to be 0.
import Mathlib
theorem positive_value_is_zero : (1 : ℚ) = 0 := by
  norm_num
