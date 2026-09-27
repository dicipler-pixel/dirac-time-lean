/-
Weak-value success-probability bound (Theorem P2 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

For a normalized postselected state `f`, a preselected state `i` with `⟨f|i⟩ ≠ 0` and a
self-adjoint observable `A`, the weak value is `A_w = ⟨f|A|i⟩ / ⟨f|i⟩` and the
postselection probability is `p₀ = |⟨f|i⟩|²`. Then

  p₀ |A_w|² ≤ ⟨i|A²|i⟩.

An arbitrarily large weak value therefore costs a correspondingly small postselection
probability unless the second moment of `A` grows.
-/
import Mathlib

namespace DiracTime.WeakValue

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `p₀ |A_w|² = |⟨f|A|i⟩|²` whenever `⟨f|i⟩ ≠ 0`. -/
theorem postselected_weak_value_sq (f i : E) (A : E →ₗ[ℂ] E) (h : ⟪f, i⟫_ℂ ≠ 0) :
    ‖⟪f, i⟫_ℂ‖ ^ 2 * ‖⟪f, A i⟫_ℂ / ⟪f, i⟫_ℂ‖ ^ 2 = ‖⟪f, A i⟫_ℂ‖ ^ 2 := by
  have hn : ‖⟪f, i⟫_ℂ‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [norm_div]
  field_simp

/-- **Theorem P2.** The weak-value success-probability bound. -/
theorem weak_value_bound (f i : E) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    (hf : ‖f‖ = 1) (h : ⟪f, i⟫_ℂ ≠ 0) :
    ‖⟪f, i⟫_ℂ‖ ^ 2 * ‖⟪f, A i⟫_ℂ / ⟪f, i⟫_ℂ‖ ^ 2 ≤ (⟪i, A (A i)⟫_ℂ).re := by
  rw [postselected_weak_value_sq f i A h]
  have h1 : ‖⟪f, A i⟫_ℂ‖ ≤ ‖A i‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) f (A i)
    rwa [hf, one_mul] at this
  have h2 : ‖A i‖ ^ 2 = (⟪i, A (A i)⟫_ℂ).re := by
    rw [← hA i (A i)]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (A i)).symm
  rw [← h2]
  gcongr

end DiracTime.WeakValue
