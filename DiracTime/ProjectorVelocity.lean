/-
Trace of a projector velocity (§19.2, DT-C270, of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

If `P(t)² = P(t)` and `P` is entrywise differentiable, then `Tr((2P − I) Ṗ) = 0`.
Self-adjointness of `P` is not required for this trace; a companion statement records that a
Hermitian curve has a Hermitian velocity.
-/
import Mathlib
import DiracTime.ProjectorTangent

namespace DiracTime.ProjectorVelocity

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.unusedSectionVars false in
theorem entry_mul_hasDerivAt {A B : ℝ → Matrix n n ℂ} {A' B' : Matrix n n ℂ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : n) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  have hterm : ∀ k, HasDerivAt (fun s => A s i k * B s k j)
      (A' i k * B t k j + A t i k * B' k j) t := fun k => (hA i k).mul (hB k j)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (A := fun k s => A s i k * B s k j)
    (A' := fun k => A' i k * B t k j + A t i k * B' k j) fun k _ => hterm k
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using hsum

set_option linter.unusedSectionVars false in
theorem entry_proj_deriv {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ} {t : ℝ}
    (hP : ∀ s, P s * P s = P s)
    (hd : ∀ i j, HasDerivAt (fun s => P s i j) (P' i j) t) :
    P' * P t + P t * P' = P' := by
  have hsq := entry_mul_hasDerivAt hd hd
  ext i j
  have hfun : (fun s => (P s * P s) i j) = fun s => P s i j := by
    funext s
    exact congr_fun (congr_fun (hP s) i) j
  have hleft := (hsq i j).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun.symm)
  exact hleft.unique (hd i j)

/-- **DT-C270.** `Tr((2P − I) Ṗ) = 0` for an entrywise differentiable projector curve.
Self-adjointness is not used. -/
theorem trace_projector_velocity {P : ℝ → Matrix n n ℂ} {P' : ℝ → Matrix n n ℂ}
    (hP : ∀ t, P t * P t = P t)
    (hd : ∀ t i j, HasDerivAt (fun s => P s i j) (P' t i j) t) (t : ℝ) :
    trace ((2 • P t - 1) * P' t) = 0 := by
  have hvel : P' t * P t + P t * P' t = P' t := entry_proj_deriv hP (hd t)
  have hcomm : P t * P' t + P' t * P t = P' t := by rw [add_comm]; exact hvel
  have hblock : P t * P' t * P t = 0 :=
    DiracTime.ProjectorTangent.occupied_block_zero (hP t) hcomm
  have htr : trace (P t * P' t) = 0 := by
    have hassoc : P' t * P t = P' t * P t * P t := by rw [mul_assoc, hP t]
    calc
      trace (P t * P' t) = trace (P' t * P t) := by rw [trace_mul_comm]
      _ = trace (P' t * P t * P t) := by nth_rw 1 [hassoc]
      _ = trace (P t * (P' t * P t)) := by rw [trace_mul_comm]
      _ = trace ((P t * P' t) * P t) := by rw [mul_assoc]
      _ = trace (0 : Matrix n n ℂ) := by rw [hblock]
      _ = 0 := by simp
  have htr' : trace (P' t) = 0 := by
    calc
      trace (P' t) = trace (P' t * P t + P t * P' t) := by rw [hvel]
      _ = trace (P' t * P t) + trace (P t * P' t) := trace_add _ _
      _ = trace (P t * P' t) + trace (P t * P' t) := by rw [trace_mul_comm]
      _ = 0 := by rw [htr, add_zero]
  calc
    trace ((2 • P t - 1) * P' t) = trace ((2 • P t) * P' t - (1 : Matrix n n ℂ) * P' t) := by
      rw [sub_mul]
    _ = trace (2 • (P t * P' t) - P' t) := by rw [smul_mul_assoc, Matrix.one_mul]
    _ = trace (2 • (P t * P' t)) - trace (P' t) := trace_sub _ _
    _ = 2 • trace (P t * P' t) - trace (P' t) := by rw [trace_smul]
    _ = 2 * trace (P t * P' t) - trace (P' t) := by simp
    _ = 0 := by rw [htr, htr', mul_zero, sub_zero]

set_option linter.unusedSectionVars false in
/-- A Hermitian entrywise differentiable curve has a Hermitian velocity. -/
theorem projector_velocity_hermitian {P : ℝ → Matrix n n ℂ} {P' : ℝ → Matrix n n ℂ}
    (hH : ∀ t, (P t)ᴴ = P t)
    (hd : ∀ t i j, HasDerivAt (fun s => P s i j) (P' t i j) t) (t : ℝ) :
    (P' t)ᴴ = P' t := by
  ext i j
  have hstar : HasDerivAt (fun s => star (P s j i)) (star (P' t j i)) t :=
    (hd t j i).star
  have hfun : (fun s => star (P s j i)) = fun s => P s i j := by
    funext s
    have hs := congr_fun (congr_fun (hH s) i) j
    simpa [Matrix.conjTranspose_apply] using hs
  have hd' := hstar.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun.symm)
  have heq := hd'.unique (hd t i j)
  simpa [Matrix.conjTranspose_apply] using heq

end DiracTime.ProjectorVelocity
