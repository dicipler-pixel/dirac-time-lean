-- FALSE CONTROL: DT-C270 the differentiated projector equation does not hold for a curve
-- that is not idempotent. At the evaluated scalar level the two sides differ by 1.
import Mathlib

theorem projector_equation_without_square : (0 : ℚ) = 1 := by
  norm_num
