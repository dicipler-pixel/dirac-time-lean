/-
The corollaries of the covariant common-clock theorem (Corollaries P4.1–P4.3 of "The Dirac
Time of the Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978631).

Proved here, for complex matrices:
* P4.1, common gap scaling: if the frame generator is `G = τ̇ H₀ + a I`, every eigenvector of
  `H₀` with eigenvalue `E` is an eigenvector of `G` with eigenvalue `τ̇ E + a`, so every gap
  of `G` is `τ̇` times the matching gap of `H₀`;
* P4.2, uniqueness: if `H₀` is not a scalar matrix, `c H₀ + a I = c' H₀ + a' I` forces
  `c = c'` and `a = a'`;
* P4.3, projector geometry cannot fix the rate: for `s ≠ 0`, `s H` has exactly the same
  eigenvectors as `H`, while every gap is multiplied by `s`.
-/
import Mathlib

namespace DiracTime.CommonClock

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An eigenvector of `H₀` is an eigenvector of the frame generator `τ̇ H₀ + a I`. -/
theorem generator_eigen (G H₀ : Matrix n n ℂ) (τdot a E : ℂ) (v : n → ℂ)
    (hG : G = τdot • H₀ + a • (1 : Matrix n n ℂ)) (hv : H₀ *ᵥ v = E • v) :
    G *ᵥ v = (τdot * E + a) • v := by
  rw [hG, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hv, smul_smul, add_smul]

/-- **Corollary P4.1.** All gaps of the frame generator share the one scale factor `τ̇`. -/
theorem common_gap_scaling (G H₀ : Matrix n n ℂ) (τdot a Ej Ek : ℂ) (v w : n → ℂ)
    (hG : G = τdot • H₀ + a • (1 : Matrix n n ℂ))
    (hv : H₀ *ᵥ v = Ej • v) (hw : H₀ *ᵥ w = Ek • w) :
    G *ᵥ v = (τdot * Ej + a) • v ∧ G *ᵥ w = (τdot * Ek + a) • w ∧
      (τdot * Ej + a) - (τdot * Ek + a) = τdot * (Ej - Ek) :=
  ⟨generator_eigen G H₀ τdot a Ej v hG hv, generator_eigen G H₀ τdot a Ek w hG hw, by ring⟩

/-- **Corollary P4.2.** For a non-scalar `H₀`, the rate and the scalar shift are unique. -/
theorem rate_shift_unique (H₀ : Matrix n n ℂ) (hns : ∀ c : ℂ, H₀ ≠ c • (1 : Matrix n n ℂ))
    (c c' a a' : ℂ)
    (h : c • H₀ + a • (1 : Matrix n n ℂ) = c' • H₀ + a' • (1 : Matrix n n ℂ)) :
    c = c' ∧ a = a' := by
  have hcc : c = c' := by
    by_contra hc
    have h1 : (c - c') • H₀ = (a' - a) • (1 : Matrix n n ℂ) := by
      rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, h, add_comm]
    apply hns ((a' - a) / (c - c'))
    rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc),
      one_smul]
  subst hcc
  refine ⟨rfl, ?_⟩
  have h2 : a • (1 : Matrix n n ℂ) = a' • (1 : Matrix n n ℂ) := add_left_cancel h
  have hne : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    exact hns 0 (by ext i j; exact isEmptyElim i)
  obtain ⟨i⟩ := hne
  have h3 := congrFun (congrFun h2 i) i
  simpa using h3

/-- **Corollary P4.3.** Rescaling `H ↦ s H` (`s ≠ 0`) keeps every eigenvector. -/
theorem rescale_same_eigenvectors (H : Matrix n n ℂ) (s E : ℂ) (hs : s ≠ 0) (v : n → ℂ) :
    (s • H) *ᵥ v = (s * E) • v ↔ H *ᵥ v = E • v := by
  rw [smul_mulVec, mul_smul]
  exact ⟨fun h => smul_right_injective _ hs h, fun h => by rw [h]⟩

/-- **Corollary P4.3.** … while every gap is multiplied by `s`. -/
theorem rescale_scales_gaps (s Ej Ek : ℂ) : s * Ej - s * Ek = s * (Ej - Ek) := by ring

end DiracTime.CommonClock
