-- FALSE CONTROL: DT-C032 conjugation multiplies the determinant by 2.
import Mathlib
theorem det_conj_scales : ((1 : ℚ) * 3 * 1) = 2 * 3 := by
  norm_num
