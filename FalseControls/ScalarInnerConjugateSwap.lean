-- FALSE CONTROL: DT-C192 Frobenius inner is linear in the first slot.
import Mathlib
theorem inner_linear_in_first : (star (Complex.I) * (1 : ℂ)) = Complex.I * 1 := by
  norm_num
