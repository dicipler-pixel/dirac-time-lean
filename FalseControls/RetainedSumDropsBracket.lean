-- FALSE CONTROL: DT-C223 drops the bracket [1 - (1-η)^N].
import Mathlib
theorem retained_sum_unbounded :
    (1 - (0 : ℚ)) * (0 - 1) * (1 - (1 - 1 / 2) ^ 1) = (1 - 0) * (0 - 1) := by
  norm_num
