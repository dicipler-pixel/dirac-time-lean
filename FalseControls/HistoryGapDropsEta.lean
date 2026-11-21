-- FALSE CONTROL: DT-C222 history gap without the factor η.
import Mathlib
theorem history_gap_without_eta :
    ((2 : ℚ) - 0) * (1 / 2) * (1 - 1 / 2) ^ 0 * (3 - 1) = (2 - 0) * (1 - 1 / 2) ^ 0 * (3 - 1) := by
  norm_num
