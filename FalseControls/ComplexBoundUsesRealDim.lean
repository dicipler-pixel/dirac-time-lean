-- FALSE CONTROL: DT-C008 the complex jet bound is twice the complex dimension.
import Mathlib
theorem complex_bound_doubled : (2 : ℚ) * 1 < 1 := by
  norm_num
