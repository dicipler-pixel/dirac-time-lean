-- FALSE CONTROL: DT-C305 with the inequality 1 - exp(-x) ≤ x reversed to a negative bound.
import Mathlib
theorem one_sub_exp_negative : (1 : ℚ) ≤ 0 := by
  norm_num
