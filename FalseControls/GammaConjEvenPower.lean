-- FALSE CONTROL: DT-C032 conjugation sign for an even power is -1.
import Mathlib
theorem even_power_picks_minus : ((-1 : ℚ) ^ 2) = -1 := by
  norm_num
