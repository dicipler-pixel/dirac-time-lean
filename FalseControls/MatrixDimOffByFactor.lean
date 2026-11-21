-- FALSE CONTROL: DT-C008 dim M_2(ℂ) = 2 rather than 4.
import Mathlib
theorem matrix_dim_linear : (2 : ℚ) * 2 = 2 := by
  norm_num
