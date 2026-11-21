/-
One-sided finite return (Theorem P5 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

`ContinuousReturn.hidden_forever_iff` quantifies over every real time. The reading
`t ↦ R (e^{tL} Δ)` is real-analytic, so vanishing on `(0, ∞)` forces every derivative at `0`
to vanish. With `R Δ = 0`, the first nonzero jet lies in `{1, …, dim − 1}`.

Over `ℂ` the jet bound is the complex dimension. On `M_d(ℂ)` that dimension is `d²`.
The generator `ℒ(X) = −i[H, X]` is complex-linear for every `H`; self-adjointness of `H` is
not required for the equivalence.
-/
import DiracTime.ContinuousReturn
import DiracTime.FiniteReturn

namespace DiracTime.PositiveReturn

open NormedSpace Filter DiracTime.ContinuousReturn DiracTime.FiniteReturn

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [CompleteSpace V] in
lemma reading_pow (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V) (k : ℕ) :
    R ((L ^ k) Δ) = R.toLinearMap ((L.toLinearMap ^ k) Δ) := by
  rw [← ContinuousLinearMap.toLinearMap_pow]
  rfl

theorem profile_zero_of_positive (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V)
    (hpos : ∀ t > (0 : ℝ), R (exp (t • L) Δ) = 0) :
    ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → profile R L Δ k t = 0 := by
  intro k
  induction k with
  | zero =>
    intro t ht
    rcases ht.eq_or_lt with rfl | ht
    · have hcont : ContinuousAt (profile R L Δ 0) 0 :=
        (profile_hasDerivAt R L Δ 0 0).continuousAt
      have hright : Tendsto (profile R L Δ 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : W)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        simpa [profile, reading_apply, pow_zero, one_mul, eq_comm] using hpos u hu
      have hlim : Tendsto (profile R L Δ 0) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (profile R L Δ 0 0)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique hlim hright
    · simpa [profile, reading_apply, pow_zero, one_mul, eq_comm] using hpos t ht
  | succ k ih =>
    intro t ht
    rcases ht.eq_or_lt with rfl | ht
    · have hd := profile_hasDerivAt R L Δ k 0
      have hright := hd.tendsto_slope_zero_right
      have hzero : Tendsto (fun u : ℝ => u⁻¹ • (profile R L Δ k (0 + u) - profile R L Δ k 0))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : W)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu0 : 0 < u := hu
        have hpu : profile R L Δ k u = 0 := ih u hu0.le
        have hp0 : profile R L Δ k 0 = 0 := ih 0 le_rfl
        simp [zero_add, hpu, hp0]
      exact tendsto_nhds_unique hright hzero
    · have hd := profile_hasDerivAt R L Δ k t
      have hev : profile R L Δ k =ᶠ[nhds t] fun _ => (0 : W) := by
        filter_upwards [Ioo_mem_nhds (by linarith : t / 2 < t) (lt_add_one t)] with s hs
        exact ih s (le_of_lt (by linarith [hs.1]))
      exact hd.unique ((hasDerivAt_const t (0 : W)).congr_of_eventuallyEq hev)

/-- Vanishing on `(0, ∞)` is the same as vanishing of every jet `R Lᵏ Δ`. -/
theorem hidden_on_positive_iff (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V) :
    (∀ t > (0 : ℝ), R (exp (t • L) Δ) = 0) ↔
      ∀ k : ℕ, R ((L ^ k : V →L[ℝ] V) Δ) = 0 := by
  constructor
  · intro hpos k
    simpa [profile, reading_apply, exp_zero] using
      profile_zero_of_positive R L Δ hpos k 0 le_rfl
  · intro hall t ht
    exact (hidden_forever_iff R L Δ).mpr hall t

/-- A positive-time return is the same as some jet being nonzero. -/
theorem positive_jet_iff (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V) :
    (∃ t > (0 : ℝ), R (exp (t • L) Δ) ≠ 0) ↔
      ∃ k : ℕ, R ((L ^ k : V →L[ℝ] V) Δ) ≠ 0 := by
  constructor
  · intro ⟨t, ht, hne⟩
    by_contra hall
    push Not at hall
    exact hne ((hidden_on_positive_iff R L Δ).mpr hall t ht)
  · intro ⟨k, hk⟩
    by_contra hall
    push Not at hall
    exact hk ((hidden_on_positive_iff R L Δ).mp hall k)

/-- **Theorem P5, one-sided, real dimension.** -/
theorem positive_return_iff [FiniteDimensional ℝ V] (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V) :
    (∃ t > (0 : ℝ), R (exp (t • L) Δ) ≠ 0) ↔
      ∃ k < Module.finrank ℝ V, R ((L ^ k : V →L[ℝ] V) Δ) ≠ 0 := by
  rw [positive_jet_iff]
  constructor
  · intro ⟨k, hk⟩
    have hsome : ∃ n : ℕ, R.toLinearMap ((L.toLinearMap ^ n) Δ) ≠ 0 := by
      refine ⟨k, ?_⟩
      rw [← reading_pow]
      exact hk
    obtain ⟨n, hn, hne⟩ := (finite_return_iff L.toLinearMap R.toLinearMap Δ).mp hsome
    refine ⟨n, hn, ?_⟩
    rw [reading_pow]
    exact hne
  · intro ⟨k, hk, hne⟩
    exact ⟨k, hne⟩

/-- With `R Δ = 0`, the returning jet has order in `{1, …, dim V − 1}`. -/
theorem positive_return_silent_present_iff [FiniteDimensional ℝ V]
    (R : V →L[ℝ] W) (L : V →L[ℝ] V) (Δ : V) (h0 : R Δ = 0) :
    (∃ t > (0 : ℝ), R (exp (t • L) Δ) ≠ 0) ↔
      ∃ k, 0 < k ∧ k < Module.finrank ℝ V ∧ R ((L ^ k : V →L[ℝ] V) Δ) ≠ 0 := by
  rw [positive_return_iff]
  constructor
  · rintro ⟨k, hk, hne⟩
    have hk0 : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      apply hne
      simpa [hkzero, pow_zero] using h0
    exact ⟨k, hk0, hk, hne⟩
  · rintro ⟨k, -, hk, hne⟩
    exact ⟨k, hk, hne⟩

section Complex

variable {Vc Wc : Type*} [NormedAddCommGroup Vc] [NormedSpace ℂ Vc] [CompleteSpace Vc]
  [NormedAddCommGroup Wc] [NormedSpace ℂ Wc]

omit [CompleteSpace Vc] in
lemma reading_pow_complex (R : Vc →L[ℂ] Wc) (L : Vc →L[ℂ] Vc) (Δ : Vc) (k : ℕ) :
    R ((L ^ k) Δ) = R.toLinearMap ((L.toLinearMap ^ k) Δ) := by
  rw [← ContinuousLinearMap.toLinearMap_pow]
  rfl

omit [CompleteSpace Vc] in
theorem restrictScalars_pow (L : Vc →L[ℂ] Vc) (k : ℕ) :
    (L.restrictScalars ℝ) ^ k = (L ^ k).restrictScalars ℝ := by
  induction k with
  | zero =>
    ext v
    simp [ContinuousLinearMap.coe_restrictScalars']
  | succ k ih =>
    ext v
    simp [pow_succ, ih, ContinuousLinearMap.coe_restrictScalars']

/-- **Theorem P5 over `ℂ`.** The bound is the complex dimension, and `R Δ = 0` starts the
count at order `1`. -/
theorem positive_return_complex_iff [FiniteDimensional ℂ Vc]
    (R : Vc →L[ℂ] Wc) (L : Vc →L[ℂ] Vc) (Δ : Vc) (h0 : R Δ = 0) :
    (∃ t > (0 : ℝ), R (exp (t • L.restrictScalars ℝ) Δ) ≠ 0) ↔
      ∃ k, 0 < k ∧ k < Module.finrank ℂ Vc ∧ R ((L ^ k : Vc →L[ℂ] Vc) Δ) ≠ 0 := by
  have hjet := positive_jet_iff (R.restrictScalars ℝ) (L.restrictScalars ℝ) Δ
  have hfin := finite_return_iff L.toLinearMap R.toLinearMap Δ
  have happ : ∀ k, (R.restrictScalars ℝ) (((L.restrictScalars ℝ) ^ k) Δ) =
      R.toLinearMap ((L.toLinearMap ^ k) Δ) := by
    intro k
    rw [restrictScalars_pow]
    have hcoe : (R.restrictScalars ℝ) (((L ^ k).restrictScalars ℝ) Δ) = R ((L ^ k) Δ) := rfl
    rw [hcoe, reading_pow_complex]
  constructor
  · rintro ⟨t, ht, hne⟩
    have hex : ∃ k : ℕ, (R.restrictScalars ℝ) (((L.restrictScalars ℝ) ^ k) Δ) ≠ 0 :=
      hjet.mp ⟨t, ht, by rwa [ContinuousLinearMap.coe_restrictScalars']⟩
    obtain ⟨k, hk⟩ := hex
    have hlin : ∃ n : ℕ, R.toLinearMap ((L.toLinearMap ^ n) Δ) ≠ 0 :=
      ⟨k, by rwa [← happ]⟩
    obtain ⟨n, hn, hne'⟩ := hfin.mp hlin
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne' (by simpa [pow_zero] using h0)
    refine ⟨n, Nat.pos_of_ne_zero hn0, hn, ?_⟩
    rwa [reading_pow_complex]
  · rintro ⟨k, -, hk, hne⟩
    have hlin : ∃ n < Module.finrank ℂ Vc, R.toLinearMap ((L.toLinearMap ^ n) Δ) ≠ 0 :=
      ⟨k, hk, by
        rw [← reading_pow_complex]
        exact hne⟩
    have hunb : ∃ n : ℕ, R.toLinearMap ((L.toLinearMap ^ n) Δ) ≠ 0 := hfin.mpr hlin
    obtain ⟨n, hne'⟩ := hunb
    have hreal : ∃ m : ℕ, (R.restrictScalars ℝ) (((L.restrictScalars ℝ) ^ m) Δ) ≠ 0 :=
      ⟨n, by rwa [happ]⟩
    obtain ⟨t, ht, htne⟩ := hjet.mpr hreal
    exact ⟨t, ht, htne⟩

end Complex

/-- Complex dimension of a square matrix space: `dim_ℂ M_n = n²`. -/
theorem matrix_complex_dim (n : Type*) [Fintype n] :
    Module.finrank ℂ (Matrix n n ℂ) = Fintype.card n * Fintype.card n := by
  simp [Module.finrank_matrix, Module.finrank_self]

end DiracTime.PositiveReturn
