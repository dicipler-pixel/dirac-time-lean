-- FALSE CONTROL: DT-C222 work ignores the memory correction.
import Mathlib
theorem work_without_memory :
    ((1 : ℚ) - 0) * (1 - 0 + 1 * (1 - 1) ^ 0 * (0 - 1)) = (1 - 0) * (1 - 0) := by
  norm_num
