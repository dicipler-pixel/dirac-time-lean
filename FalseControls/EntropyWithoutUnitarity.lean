/- FALSE CONTROL: P6 needs the total entropy to be conserved.
   No reservoirs, ΔS_S = 1, and the total entropy also rises by 1: then ΔI = 0, so the
   identity would read 1 = 0. This file must not compile. -/
import Mathlib

theorem identity_without_unitarity : (1 : ℝ) - 0 = ((0 + 1) - (0 + 0)) - (1 - 0) := by
  norm_num
