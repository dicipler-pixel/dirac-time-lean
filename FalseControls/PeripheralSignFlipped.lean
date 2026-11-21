-- FALSE CONTROL: DT-C116 peripheral law with (-1)^{a+1}.
import Mathlib
theorem peripheral_wrong_sign :
    ((-1 : ℤ) ^ (0 : ℤ) : ℚ) * ((2 : ℚ)⁻¹) ^ 2 = - ((2 : ℚ)⁻¹) ^ 2 := by
  norm_num
