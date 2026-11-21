-- FALSE CONTROL: DT-C192 trace(X† Y) equals trace(X Y) with the adjoint dropped.
import Mathlib
-- trace([[1,0],[0,0]]† * [[0,0],[1,0]]) = 0, not 1.
theorem frobenius_forgets_adjoint : (0 : ℚ) = 1 := by
  norm_num
