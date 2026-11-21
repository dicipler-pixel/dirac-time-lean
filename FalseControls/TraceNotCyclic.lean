-- FALSE CONTROL: DT-C032 trace fails to be cyclic on a swap.
import Mathlib
-- trace([[1,0],[0,0]] * [[0,1],[0,0]]) = trace([[0,1],[0,0]]) = 0, not 1.
theorem trace_not_cyclic : (0 : ℚ) = 1 := by
  norm_num
