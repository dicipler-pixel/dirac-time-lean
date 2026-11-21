-- FALSE CONTROL: DT-C116 inverse eigenvector uses M instead of M⁻¹.
import Mathlib
theorem inv_eigen_not_reciprocal : ((2 : ℚ)⁻¹) = 2 := by
  norm_num
