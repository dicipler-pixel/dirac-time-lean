/-
Finite retained-history return (the finite core of Theorem P5 of "The Dirac Time of the
Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978630).

Two histories that differ by `Δ` become distinguishable through the observation `R` at
some later step exactly when they do so within the first `d = dim V` steps: if the
difference has not returned to the observed sector by step `d - 1`, it never will.

The paper states P5 for continuous time, `R e^{tL} Δ ≠ 0` for some `t > 0`, with the
dimension of the operator space in place of `d`. This file proves the discrete-step
statement that its proof rests on. The passage through the exponential is in
`ContinuousReturn` (for all real `t`); the operator-space dimension bound is not formalized.
-/
import DiracTime.PredictiveQuotient

namespace DiracTime.FiniteReturn

open Module DiracTime.PredictiveQuotient

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- A difference that is silent for the first `dim V` steps is silent forever. -/
theorem silent_forever_iff [FiniteDimensional K V] (L : V →ₗ[K] V) (R : V →ₗ[K] W)
    (Δ : V) :
    (∀ n : ℕ, R ((L ^ n) Δ) = 0) ↔ ∀ n < finrank K V, R ((L ^ n) Δ) = 0 := by
  rw [← mem_unobservable L R, ← ker_observability L R, LinearMap.mem_ker]
  constructor
  · intro h n hn
    have h' := congrFun h ⟨n, hn⟩
    rw [observability_apply] at h'
    exact h'
  · intro h
    funext i
    rw [observability_apply]
    exact h i i.2

/-- **Finite return criterion.** A difference returns to the observed sector at some step
exactly when it returns within the first `dim V` steps. -/
theorem finite_return_iff [FiniteDimensional K V] (L : V →ₗ[K] V) (R : V →ₗ[K] W)
    (Δ : V) :
    (∃ n : ℕ, R ((L ^ n) Δ) ≠ 0) ↔ ∃ n < finrank K V, R ((L ^ n) Δ) ≠ 0 := by
  constructor
  · rintro ⟨n, hn⟩
    by_contra hcon
    push Not at hcon
    exact hn ((silent_forever_iff L R Δ).mpr hcon n)
  · rintro ⟨n, -, hn⟩
    exact ⟨n, hn⟩

end DiracTime.FiniteReturn
