-- FALSE CONTROL: DT-C008 the returning index is bounded by dim - 1 strictly below the last admissible index.
import Mathlib
theorem return_bound_too_small : (1 : ℚ) < 1 := by
  norm_num
