/-
Theorem 13.1(1), the peripheral eigenvalue law (p. 39 of "The Dirac Time of the
Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978630).

On the arc `(a, b)`, the paper's preferred longitude is the word `λ = x^p μ^{−pq}` and the
representation sends `x^p` to `(-1)^a I`. If `μ v = M v` with `M ≠ 0`, then
`λ v = (-1)^a M^{−pq} v`.

The torus-knot group, irreducibility, and the condition `Im M > 0` are not used: the identity is
the word computation. Coprimeness of `p, q` is the existence of the meridian word, not an input
to this equality.
-/
import Mathlib

namespace DiracTime.PeripheralLaw

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem inv_eigenvector {A : Matrix n n ℂ} {v : n → ℂ} {M : ℂ}
    (hA : A *ᵥ v = M • v) (hM : M ≠ 0) (hdet : IsUnit A.det) :
    A⁻¹ *ᵥ v = M⁻¹ • v := by
  have hinv : A⁻¹ * A = 1 := nonsing_inv_mul A hdet
  have hv : v = M • (A⁻¹ *ᵥ v) := by
    calc
      v = (A⁻¹ * A) *ᵥ v := by rw [hinv, one_mulVec]
      _ = A⁻¹ *ᵥ (A *ᵥ v) := by rw [← mulVec_mulVec]
      _ = A⁻¹ *ᵥ (M • v) := by rw [hA]
      _ = M • (A⁻¹ *ᵥ v) := by rw [mulVec_smul]
  have hscale := congrArg (fun w : n → ℂ => M⁻¹ • w) hv
  simpa [smul_smul, inv_mul_cancel₀ hM] using hscale.symm

theorem inv_pow_eigenvector {A : Matrix n n ℂ} {v : n → ℂ} {M : ℂ}
    (hA : A *ᵥ v = M • v) (hM : M ≠ 0) (hdet : IsUnit A.det) (k : ℕ) :
    A⁻¹ ^ k *ᵥ v = M⁻¹ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      A⁻¹ ^ (k + 1) *ᵥ v = A⁻¹ ^ k *ᵥ (A⁻¹ *ᵥ v) := by rw [pow_succ, ← mulVec_mulVec]
      _ = A⁻¹ ^ k *ᵥ (M⁻¹ • v) := by rw [inv_eigenvector hA hM hdet]
      _ = M⁻¹ • (A⁻¹ ^ k *ᵥ v) := by rw [mulVec_smul]
      _ = M⁻¹ • (M⁻¹ ^ k • v) := by rw [ih]
      _ = (M⁻¹ * M⁻¹ ^ k) • v := by rw [smul_smul]
      _ = M⁻¹ ^ (k + 1) • v := by rw [← pow_succ']

/-- **Theorem 13.1(1).** `λ = X^p μ^{−pq}` acts on a `μ`-eigenvector by `(-1)^a M^{−pq}`. -/
theorem peripheral_law (p q : ℕ) (a : ℤ) (X μ : Matrix n n ℂ) (v : n → ℂ) (M : ℂ)
    (hX : X ^ p = ((-1 : ℤ) ^ a : ℂ) • (1 : Matrix n n ℂ))
    (hμ : μ *ᵥ v = M • v) (hM : M ≠ 0) (hdet : IsUnit μ.det) :
    (X ^ p * μ⁻¹ ^ (p * q)) *ᵥ v =
      (((-1 : ℤ) ^ a : ℂ) * M⁻¹ ^ (p * q)) • v := by
  rw [← mulVec_mulVec, inv_pow_eigenvector hμ hM hdet (p * q), mulVec_smul, hX, smul_mulVec,
    one_mulVec, smul_smul, mul_comm]

end DiracTime.PeripheralLaw
