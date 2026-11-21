-- FALSE CONTROL: DT-C192 ‖X‖² equals the imaginary part of the trace.
import Mathlib
theorem norm_sq_is_im : ((1 : ℂ) * 1).im = 1 := by
  norm_num
