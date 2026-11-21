/-
Flat chirality of a spectrum (§5.3 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630), finite-dimensional parts.

If `Γ` is an involution and `Γ D Γ = −D`, the characteristic polynomial is even up to the
degree sign, `χ_D(−x) = (−1)^n χ_D(x)`, and every odd polynomial in `D` has trace zero.
The spectral projectors `P₊`, `P₋` are not constructed here.
-/
import Mathlib

namespace DiracTime.ChiralSpectrum

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem gamma_conj_pow {D Γ : Matrix n n ℂ} (hΓ : Γ * Γ = 1) (hD : Γ * D * Γ = -D)
    (m : ℕ) : Γ * D ^ m * Γ = (-1 : ℂ) ^ m • D ^ m := by
  induction m with
  | zero => simp [hΓ]
  | succ m ih =>
    have hstep : Γ * D ^ (m + 1) * Γ = (Γ * D ^ m * Γ) * (Γ * D * Γ) := by
      rw [pow_succ]
      have h1 : Γ * (D ^ m * D) * Γ = Γ * D ^ m * (1 * D) * Γ := by noncomm_ring
      rw [h1, ← hΓ]
      noncomm_ring
    calc
      Γ * D ^ (m + 1) * Γ = (Γ * D ^ m * Γ) * (Γ * D * Γ) := hstep
      _ = ((-1 : ℂ) ^ m • D ^ m) * (-D) := by rw [ih, hD]
      _ = (-1 : ℂ) ^ (m + 1) • D ^ (m + 1) := by
        simp [pow_succ, mul_neg]

theorem trace_gamma_conj {Γ A : Matrix n n ℂ} (hΓ : Γ * Γ = 1) :
    trace (Γ * A * Γ) = trace A := by
  calc
    trace (Γ * A * Γ) = trace (Γ * (A * Γ)) := by rw [mul_assoc]
    _ = trace ((A * Γ) * Γ) := trace_mul_comm _ _
    _ = trace (A * (Γ * Γ)) := by rw [mul_assoc]
    _ = trace A := by rw [hΓ, mul_one]

/-- An odd power of a chirally odd matrix is traceless. -/
theorem trace_odd_pow {D Γ : Matrix n n ℂ} (hΓ : Γ * Γ = 1) (hD : Γ * D * Γ = -D)
    {m : ℕ} (hm : Odd m) : trace (D ^ m) = 0 := by
  have h := trace_gamma_conj (A := D ^ m) hΓ
  rw [gamma_conj_pow hΓ hD m, trace_smul, Odd.neg_one_pow hm, neg_one_smul] at h
  -- `h : -trace (D ^ m) = trace (D ^ m)`
  have htwo : (2 : ℂ) * trace (D ^ m) = 0 := by
    calc
      (2 : ℂ) * trace (D ^ m) = trace (D ^ m) + trace (D ^ m) := by ring
      _ = -trace (D ^ m) + trace (D ^ m) := by nth_rw 1 [← h]
      _ = 0 := by ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- **§5.3(2), odd traces.** `Tr f(D) = 0` for an odd polynomial `f`. -/
theorem trace_odd_polynomial {D Γ : Matrix n n ℂ} (hΓ : Γ * Γ = 1) (hD : Γ * D * Γ = -D)
    (f : ℂ[X]) (hodd : ∀ k, Even k → f.coeff k = 0) :
    trace (aeval D f) = 0 := by
  rw [aeval_eq_sum_range, trace_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases he : Even k
  · rw [hodd k he, zero_smul, trace_zero]
  · rw [trace_smul, trace_odd_pow hΓ hD (Nat.not_even_iff_odd.mp he), smul_zero]

theorem det_conj {Γ M : Matrix n n ℂ} (hΓ : Γ * Γ = 1) : (Γ * M * Γ).det = M.det := by
  calc
    (Γ * M * Γ).det = Γ.det * M.det * Γ.det := by rw [det_mul, det_mul]
    _ = M.det * (Γ.det * Γ.det) := by ring
    _ = M.det * (Γ * Γ).det := by rw [det_mul]
    _ = M.det := by rw [hΓ, det_one, mul_one]

/-- **§5.3(1).** `χ_D(−x) = (−1)^n χ_D(x)`, written as `det((−x)I − D)`. -/
theorem charpoly_neg_eval {D Γ : Matrix n n ℂ} (hΓ : Γ * Γ = 1) (hD : Γ * D * Γ = -D)
    (x : ℂ) :
    ((-x) • (1 : Matrix n n ℂ) - D).det =
      (-1 : ℂ) ^ Fintype.card n * (x • 1 - D).det := by
  have hneg : (-x) • (1 : Matrix n n ℂ) - D = -(x • 1 + D) := by
    rw [neg_smul, sub_eq_add_neg, ← neg_add]
  rw [hneg, det_neg]
  have hsim : Γ * (x • 1 - D) * Γ = x • 1 + D := by
    calc
      Γ * (x • 1 - D) * Γ = Γ * (x • 1) * Γ - Γ * D * Γ := by noncomm_ring
      _ = x • (Γ * Γ) - -D := by
        rw [hD]
        simp [mul_one]
      _ = x • 1 + D := by rw [hΓ, sub_neg_eq_add]
  rw [← hsim, det_conj hΓ]

end DiracTime.ChiralSpectrum
