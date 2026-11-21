-- FALSE CONTROL: DT-C032 an odd power of a chirally odd matrix has trace 2.
import Mathlib
theorem odd_trace_nonzero : ((-1 : ℚ) * 1 + -1 * -1) = 2 := by
  norm_num
