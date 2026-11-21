-- FALSE CONTROL: DT-C008 a nonzero constant jet still vanishes for t > 0.
import Mathlib
theorem nonzero_jet_vanishes : (1 : ℚ) = 0 := by
  norm_num
