/- FALSE CONTROL: a coupled sector is not autonomous.
   P = diag(1, 0), H = [[0, 1], [1, 0]]: (1 − P) H P ≠ 0. This file must not compile. -/
import Mathlib

theorem coupled_sector_autonomous :
    (1 - !![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, 1; 1, 0] * !![1, 0; 0, 0] = 0 := by
  simp
