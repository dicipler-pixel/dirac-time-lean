/-
The exact predictive quotient (Section 2 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978631).

Setting. `V` is a finite-dimensional vector space over a field `K`, `L : V → V` is a
linear continuation map and `R : V → W` is the declared observation. Two present
states are predictively equivalent when no future observation `R Lⁿ` separates them.

Proved here:
* 2.1  `v - w ∈ N∞` exactly when every future observation of `v` and `w` agrees.
* 2.2  `N∞` is invariant under `L`, so `L` descends to the quotient `V ⧸ N∞`, and the
       quotient dynamics with the descended readout reproduce every future observation.
* 2.3  Finite closure (Cayley–Hamilton): `N∞` is the kernel of the finite observability
       map `v ↦ (R v, R L v, …, R L^(d-1) v)`, `d = dim V`, so `dim (V ⧸ N∞)` is its rank.
       Any linear summary that determines all future outputs has rank at least `dim (V ⧸ N∞)`.
* 2.4  The present observation closes on its own (`L (ker R) ⊆ ker R`) exactly when
       `R L = A R` for some linear `A`, and then `N∞ = ker R`.
-/
import Mathlib

namespace DiracTime.PredictiveQuotient

open Module Polynomial

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable (L : V →ₗ[K] V) (R : V →ₗ[K] W)

/-- The predictively unobservable subspace `N∞ = {v | R Lⁿ v = 0 for all n}`. -/
def unobservable : Submodule K V :=
  ⨅ n : ℕ, LinearMap.ker (R ∘ₗ L ^ n)

theorem mem_unobservable {v : V} :
    v ∈ unobservable L R ↔ ∀ n : ℕ, R ((L ^ n) v) = 0 := by
  simp [unobservable, Submodule.mem_iInf]

/-! ## 2.1 Predictive equivalence -/

/-- Two present states differ by an unobservable vector exactly when every future
observation agrees on them. -/
theorem sub_mem_unobservable_iff (v w : V) :
    v - w ∈ unobservable L R ↔ ∀ n : ℕ, R ((L ^ n) v) = R ((L ^ n) w) := by
  rw [mem_unobservable]
  refine forall_congr' fun n => ?_
  rw [map_sub, map_sub, sub_eq_zero]

/-! ## 2.2 Autonomous predictive state -/

/-- The unobservable subspace is invariant under the continuation map. -/
theorem map_mem_unobservable {v : V} (hv : v ∈ unobservable L R) :
    L v ∈ unobservable L R := by
  rw [mem_unobservable] at hv ⊢
  intro n
  have h := hv (n + 1)
  rwa [pow_succ, Module.End.mul_apply] at h

theorem unobservable_le_comap : unobservable L R ≤ (unobservable L R).comap L :=
  fun _ hv => map_mem_unobservable L R hv

/-- Every unobservable vector is invisible to the present observation. -/
theorem unobservable_le_ker : unobservable L R ≤ LinearMap.ker R := fun v hv => by
  have h := (mem_unobservable L R).mp hv 0
  simpa using h

/-- The descended dynamics on the predictive state space `V ⧸ N∞`. -/
def predictiveDynamics : (V ⧸ unobservable L R) →ₗ[K] (V ⧸ unobservable L R) :=
  (unobservable L R).mapQ (unobservable L R) L (unobservable_le_comap L R)

/-- The observation read off the predictive state. -/
def predictiveReadout : (V ⧸ unobservable L R) →ₗ[K] W :=
  (unobservable L R).liftQ R (unobservable_le_ker L R)

theorem predictiveDynamics_mk (v : V) :
    predictiveDynamics L R (Submodule.Quotient.mk v) = Submodule.Quotient.mk (L v) :=
  rfl

theorem predictiveDynamics_pow_mk (n : ℕ) (v : V) :
    (predictiveDynamics L R ^ n) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((L ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (predictiveDynamics L R) n, Module.End.mul_apply, predictiveDynamics_mk, ih,
      pow_succ L n, Module.End.mul_apply]

/-- The quotient model reproduces every future observation of the full state. -/
theorem readout_predictiveDynamics_pow (n : ℕ) (v : V) :
    predictiveReadout L R ((predictiveDynamics L R ^ n) (Submodule.Quotient.mk v)) =
      R ((L ^ n) v) := by
  rw [predictiveDynamics_pow_mk]
  rfl

/-- Two full states have the same predictive state exactly when every future observation
agrees on them: the quotient forgets nothing the future can see and keeps nothing it cannot. -/
theorem mk_eq_mk_iff (v w : V) :
    (Submodule.Quotient.mk v : V ⧸ unobservable L R) = Submodule.Quotient.mk w ↔
      ∀ n : ℕ, R ((L ^ n) v) = R ((L ^ n) w) := by
  rw [Submodule.Quotient.eq, sub_mem_unobservable_iff]

/-! ## 2.3 Finite closure -/

/-- Cayley–Hamilton: every power of `L` is a combination of `L⁰, …, L^(d-1)`, `d = dim V`. -/
theorem pow_eq_sum_lower [FiniteDimensional K V] (m : ℕ) :
    ∃ c : ℕ → K, L ^ m = ∑ i ∈ Finset.range (finrank K V), c i • L ^ i := by
  have hp : L.charpoly.Monic := L.charpoly_monic
  have hsplit : L ^ m = aeval L ((X ^ m : K[X]) %ₘ L.charpoly) := by
    have h := modByMonic_add_div (X ^ m : K[X]) L.charpoly
    calc L ^ m = aeval L (X ^ m : K[X]) := by rw [aeval_X_pow]
      _ = aeval L ((X ^ m : K[X]) %ₘ L.charpoly +
            L.charpoly * ((X ^ m : K[X]) /ₘ L.charpoly)) := by rw [h]
      _ = aeval L ((X ^ m : K[X]) %ₘ L.charpoly) := by
          rw [map_add, map_mul, LinearMap.aeval_self_charpoly, zero_mul, add_zero]
  by_cases hr0 : (X ^ m : K[X]) %ₘ L.charpoly = 0
  · refine ⟨fun _ => 0, ?_⟩
    rw [hsplit, hr0, map_zero]
    simp
  · refine ⟨((X ^ m : K[X]) %ₘ L.charpoly).coeff, ?_⟩
    rw [hsplit]
    refine aeval_eq_sum_range' ?_ L
    rw [← LinearMap.charpoly_natDegree L]
    exact natDegree_lt_natDegree hr0 (degree_modByMonic_lt _ hp)

/-- The finite observability map `v ↦ (R v, R L v, …, R L^(d-1) v)`. -/
def observability (d : ℕ) : V →ₗ[K] (Fin d → W) :=
  LinearMap.pi fun i : Fin d => R ∘ₗ L ^ (i : ℕ)

theorem observability_apply (d : ℕ) (v : V) (i : Fin d) :
    observability L R d v i = R ((L ^ (i : ℕ)) v) :=
  rfl

/-- Finite closure: the first `d = dim V` observations already decide predictive
equivalence. -/
theorem ker_observability [FiniteDimensional K V] :
    LinearMap.ker (observability L R (finrank K V)) = unobservable L R := by
  ext v
  rw [LinearMap.mem_ker, mem_unobservable]
  constructor
  · intro h m
    have hi : ∀ i < finrank K V, R ((L ^ i) v) = 0 := fun i hi => by
      have h' := congrFun h ⟨i, hi⟩
      rw [observability_apply] at h'
      exact h'
    obtain ⟨c, hc⟩ := pow_eq_sum_lower L m
    rw [hc, LinearMap.sum_apply, map_sum]
    refine Finset.sum_eq_zero fun i hi' => ?_
    rw [LinearMap.smul_apply, map_smul, hi i (Finset.mem_range.mp hi'), smul_zero]
  · intro h
    funext i
    rw [observability_apply]
    exact h i

/-- The predictive state space has exactly the dimension of the rank of the finite
observability map. -/
theorem finrank_quotient_unobservable [FiniteDimensional K V] :
    finrank K (V ⧸ unobservable L R) =
      finrank K (LinearMap.range (observability L R (finrank K V))) := by
  rw [← ker_observability]
  exact (observability L R (finrank K V)).quotKerEquivRange.finrank_eq

/-- Any linear summary that determines all future observations forgets no more than
`N∞`. -/
theorem ker_le_unobservable_of_sufficient {S : Type*} [AddCommGroup S] [Module K S]
    (F : V →ₗ[K] S) (hF : ∀ v w, F v = F w → ∀ n : ℕ, R ((L ^ n) v) = R ((L ^ n) w)) :
    LinearMap.ker F ≤ unobservable L R := by
  intro v hv
  rw [mem_unobservable]
  intro n
  have h := hF v 0 (by rw [LinearMap.mem_ker.mp hv, map_zero]) n
  simpa using h

/-- Minimality: the predictive quotient is the smallest linear autonomous predictor. -/
theorem finrank_quotient_le_of_sufficient [FiniteDimensional K V] {S : Type*}
    [AddCommGroup S] [Module K S] (F : V →ₗ[K] S)
    (hF : ∀ v w, F v = F w → ∀ n : ℕ, R ((L ^ n) v) = R ((L ^ n) w)) :
    finrank K (V ⧸ unobservable L R) ≤ finrank K (LinearMap.range F) := by
  have h1 := Submodule.finrank_quotient_add_finrank (unobservable L R)
  have h2 := LinearMap.finrank_range_add_finrank_ker F
  have h3 := Submodule.finrank_mono (ker_le_unobservable_of_sufficient L R F hF)
  omega

/-! ## 2.4 When the present observation closes -/

/-- The present observation is already an autonomous state exactly when `L` keeps
`ker R` inside `ker R`, equivalently when `R L = A R` for a linear map `A`. -/
theorem closes_iff :
    LinearMap.ker R ≤ (LinearMap.ker R).comap L ↔ ∃ A : W →ₗ[K] W, R ∘ₗ L = A ∘ₗ R := by
  constructor
  · intro h
    have hk : LinearMap.ker R ≤ LinearMap.ker (R ∘ₗ L) := fun v hv => by
      have h' : L v ∈ LinearMap.ker R := h hv
      rw [LinearMap.mem_ker] at h' ⊢
      exact h'
    let g : LinearMap.range R →ₗ[K] W :=
      ((LinearMap.ker R).liftQ (R ∘ₗ L) hk) ∘ₗ R.quotKerEquivRange.symm.toLinearMap
    obtain ⟨A, hA⟩ := LinearMap.exists_extend g
    refine ⟨A, ?_⟩
    ext v
    have h1 : A (R v) = g ⟨R v, LinearMap.mem_range_self R v⟩ :=
      LinearMap.congr_fun hA ⟨R v, LinearMap.mem_range_self R v⟩
    have key : A (R v) = R (L v) := by
      rw [h1]
      simp [g, LinearMap.quotKerEquivRange_symm_apply_image]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, key]
  · rintro ⟨A, hA⟩ v hv
    rw [Submodule.mem_comap, LinearMap.mem_ker] at *
    have h := LinearMap.congr_fun hA v
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    rw [h, hv, map_zero]

/-- When the present observation closes, it is the whole predictive state: `N∞ = ker R`. -/
theorem unobservable_eq_ker_of_closes (h : LinearMap.ker R ≤ (LinearMap.ker R).comap L) :
    unobservable L R = LinearMap.ker R := by
  refine le_antisymm (unobservable_le_ker L R) fun v hv => ?_
  have hpow : ∀ n : ℕ, (L ^ n) v ∈ LinearMap.ker R := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact h ih
  rw [mem_unobservable]
  exact fun n => LinearMap.mem_ker.mp (hpow n)

end DiracTime.PredictiveQuotient
