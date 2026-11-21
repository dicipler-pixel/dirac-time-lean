-- FALSE CONTROL: DT-C116 inverse power uses M^k rather than M^{-k}.
import Mathlib
theorem inv_power_not_negative : ((-2 : ℚ)⁻¹) ^ 2 = (-2) ^ 2 := by
  norm_num
