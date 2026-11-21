-- FALSE CONTROL: DT-C270 claiming the velocity of a Hermitian curve stays
-- equal to its negative.
import Mathlib
theorem hermitian_velocity_negated : (1 : ℚ) = -1 := by
  norm_num
