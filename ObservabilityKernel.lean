import Mathlib

/-!
# Finite observability / hidden-forcing kernel

These are presentation-independent linear-algebra statements used to determine
whether retained probes can miss a target direction.  They are finite and do
not assert observability of the full Yang--Mills Hilbert space.
-/

namespace YangMillsFinite

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- A hidden forcing direction changes the target while remaining invisible to `A`. -/
def CanForce (A : V →ₗ[K] W) (b : V →ₗ[K] K) : Prop :=
  ∃ c, A c = 0 ∧ b c ≠ 0

/-- Hidden forcing exists exactly when the probe kernel is not contained in the target kernel. -/
theorem forcing_iff_kernel_not_le (A : V →ₗ[K] W) (b : V →ₗ[K] K) :
    CanForce A b ↔ ¬ LinearMap.ker A ≤ LinearMap.ker b := by
  classical
  constructor
  · rintro ⟨c, hc, hb⟩ hle
    exact hb (hle hc)
  · intro h
    by_contra hn
    apply h
    intro c hc
    change A c = 0 at hc
    change b c = 0
    by_contra hb
    exact hn ⟨c, hc, hb⟩

/-- An explicit dual reconstruction certificate rules out hidden forcing. -/
theorem dual_certificate (A : V →ₗ[K] W) (b : V →ₗ[K] K)
    (y : W →ₗ[K] K) (h : b = y.comp A) : ¬ CanForce A b := by
  rintro ⟨c, hc, hb⟩
  apply hb
  rw [h, LinearMap.comp_apply, hc, map_zero]

/-- Hidden-forcing status is invariant under invertible changes of presentation. -/
theorem presentation_invariant {U : Type*} [AddCommGroup U] [Module K U]
    (A : V →ₗ[K] W) (b : V →ₗ[K] K) (e : U ≃ₗ[K] V) :
    CanForce (A.comp e.toLinearMap) (b.comp e.toLinearMap) ↔ CanForce A b := by
  constructor
  · rintro ⟨c, hc, hb⟩
    exact ⟨e c, hc, hb⟩
  · rintro ⟨c, hc, hb⟩
    refine ⟨e.symm c, ?_, ?_⟩
    · simpa using hc
    · simpa using hb

end YangMillsFinite

#print axioms YangMillsFinite.forcing_iff_kernel_not_le
#print axioms YangMillsFinite.dual_certificate
#print axioms YangMillsFinite.presentation_invariant
