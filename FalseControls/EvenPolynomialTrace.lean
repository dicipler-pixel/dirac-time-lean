-- FALSE CONTROL: DT-C032 the claim for an even polynomial (X^2).
import Mathlib
theorem even_poly_trace_zero : ((1 : ℚ) ^ 2 + (-1) ^ 2) = 0 := by
  norm_num
