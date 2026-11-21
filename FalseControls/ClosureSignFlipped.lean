-- FALSE CONTROL: DT-C220 with ΔE_M added instead of subtracted.
import Mathlib
theorem closure_sign_flipped :
    (1 - (0 : ℚ)) * (((1 - 1) * (1 : ℚ) + 1 * 0) - 0) =
      1 * (1 - 0) + (0 : ℚ) * (0 - ((1 - 1) * 1 + 1 * 0)) + 1 * 1 * (1 - 0) := by
  norm_num
