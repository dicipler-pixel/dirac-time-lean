-- FALSE CONTROL: DT-C222 memory step swaps the weights on p_m and p_h.
import Mathlib
theorem memory_weights_swapped : (1 - (1 : ℚ) / 2) * 0 + (1 / 2) * 1 = 0 := by
  norm_num
