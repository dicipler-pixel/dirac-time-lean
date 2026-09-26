/- FALSE CONTROL: the Gibbs sign needs β ≥ 0.
   β = −1, E_m = 0, E_n = 1: (e^{0} − e^{1}) · 1 < 0. This file must not compile. -/
import Mathlib

theorem negative_beta_weight_nonneg : 0 ≤ (Real.exp 0 - Real.exp 1) * 1 := by
  simp
