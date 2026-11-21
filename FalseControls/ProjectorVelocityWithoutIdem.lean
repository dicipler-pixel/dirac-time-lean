-- FALSE CONTROL: DT-C270 without idempotence. P(t) = diag(t, 0) has
-- Tr((2P-I)P') = 2t-1, which is -1 at t = 0.
import Mathlib
theorem trace_without_idempotent : (-1 : ℚ) = 0 := by
  norm_num
