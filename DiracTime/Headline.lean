/-
Headline results in plain Mathlib terms: every statement below uses only Lean core and
Mathlib notions, so no definition from this project is needed to read it. Each is proved
by citing the library.
-/
import DiracTime.PredictiveQuotient

namespace DiracTime.Headline

open Module DiracTime.PredictiveQuotient

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- **Finite closure (§2.3).** Two states give the same observations forever exactly when
they give the same observations for the first `dim V` steps. -/
theorem future_decided_by_first_dim_steps [FiniteDimensional K V]
    (L : V →ₗ[K] V) (R : V →ₗ[K] W) (v w : V) :
    (∀ n : ℕ, R ((L ^ n) v) = R ((L ^ n) w)) ↔
      ∀ i < finrank K V, R ((L ^ i) v) = R ((L ^ i) w) := by
  rw [← sub_mem_unobservable_iff, ← ker_observability, LinearMap.mem_ker]
  constructor
  · intro h i hi
    have h' := congrFun h ⟨i, hi⟩
    rw [observability_apply, Pi.zero_apply, map_sub, map_sub, sub_eq_zero] at h'
    exact h'
  · intro h
    funext i
    rw [observability_apply, Pi.zero_apply, map_sub, map_sub, sub_eq_zero]
    exact h i i.2

/-- **Minimal predictor (§2.3).** A linear summary of the present state that determines
every future observation has rank at least `dim (V ⧸ N∞)`, where `N∞` is the set of states
no future observation can see. -/
theorem minimal_predictor_dimension [FiniteDimensional K V] {S : Type*} [AddCommGroup S]
    [Module K S] (L : V →ₗ[K] V) (R : V →ₗ[K] W) (F : V →ₗ[K] S)
    (hF : ∀ v w, F v = F w → ∀ n : ℕ, R ((L ^ n) v) = R ((L ^ n) w)) :
    finrank K (V ⧸ ⨅ n : ℕ, LinearMap.ker (R ∘ₗ L ^ n)) ≤ finrank K (LinearMap.range F) :=
  finrank_quotient_le_of_sufficient L R F hF

/-- **Closure of the present observation (§2.4).** The present reading needs no memory
exactly when the dynamics can be read off it: `R L = A R` for some linear `A`. -/
theorem present_observation_closes_iff (L : V →ₗ[K] V) (R : V →ₗ[K] W) :
    (∀ v, R v = 0 → R (L v) = 0) ↔ ∃ A : W →ₗ[K] W, ∀ v, R (L v) = A (R v) := by
  have h := closes_iff L R
  constructor
  · intro hc
    obtain ⟨A, hA⟩ := h.mp fun v hv => by
      rw [Submodule.mem_comap, LinearMap.mem_ker]
      exact hc v (LinearMap.mem_ker.mp hv)
    exact ⟨A, fun v => LinearMap.congr_fun hA v⟩
  · rintro ⟨A, hA⟩ v hv
    rw [hA v, hv, map_zero]

end DiracTime.Headline
