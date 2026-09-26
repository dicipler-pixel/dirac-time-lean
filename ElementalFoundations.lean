import Mathlib

/- Finite algebraic certificates for the combined paper. Standard identities
   are formalized as dependencies, not counted as new physical laws. -/
namespace ElementalFoundations

section Peirce
variable {R : Type*} [Ring R]
def cross (h p : R) : R := (1-p)*h*p+p*h*(1-p)

theorem cross_expansion (h p : R) :
    cross h p = h*p+p*h-(p*h*p+p*h*p) := by
  unfold cross
  noncomm_ring

theorem cross_commutator (h p : R) (hp : p*p=p) :
    p * cross h p - cross h p * p = p*h-h*p := by
  have hpph : p*p*h=p*h := by rw [hp]
  have hhpp : h*p*p=h*p := by rw [mul_assoc, hp]
  have hpphp : p*p*h*p=p*h*p := by rw [hp]
  have hphpp : p*h*p*p=p*h*p := by rw [mul_assoc (p*h), hp]
  calc
    p * cross h p - cross h p * p =
      p*p*h-h*p*p-2*(p*p*h*p)+2*(p*h*p*p) := by
        unfold cross
        noncomm_ring
    _ = p*h-h*p := by rw [hpph, hhpp, hphpp]; noncomm_ring

theorem cross_zero_iff_commutes (h p : R) (hp : p*p=p) :
    cross h p=0 ↔ p*h=h*p := by
  constructor
  · intro hf
    have q := cross_commutator h p hp
    rw [hf, mul_zero, zero_mul, sub_self] at q
    exact sub_eq_zero.mp q.symm
  · intro hc
    have hphp : p*h*p = p*h := by
      rw [hc, mul_assoc, hp]
    rw [cross_expansion, hphp, hc]
    noncomm_ring
end Peirce

noncomputable section

def characteristic (s x : ℝ) : ℝ := x^2-s*x-1
def denominator (s x : ℝ) : ℝ := (characteristic s x)^2+(x-s)^2
def transmission (s x : ℝ) : ℝ := (x-s)^2 / denominator s x
def isolatedStrength (s : ℝ) : ℝ := 1/(s^2+4)

theorem centered_characteristic (s x : ℝ) :
    characteristic s (x+s/2)=x^2-(s^2+4)/4 := by
  unfold characteristic
  ring

theorem denominator_positive (s x : ℝ) : 0 < denominator s x := by
  by_cases h : x-s=0
  · have hx : x=s := sub_eq_zero.mp h
    subst x
    norm_num [denominator, characteristic, pow_two]
  · have q := sq_pos_of_ne_zero h
    have z := sq_nonneg (characteristic s x)
    unfold denominator
    linarith

theorem denominator_expansion (s x : ℝ) :
    denominator s x = x^4-2*s*x^3+2+(s^2-1)*(x^2+1) := by
  unfold denominator characteristic
  ring

theorem mirror_transmission (x : ℝ) :
    transmission (-1) x = transmission 1 (-x) := by
  unfold transmission denominator characteristic
  congr 1 <;> ring

theorem initial_plus : transmission 1 0 = 1/2 := by
  norm_num [transmission, denominator, characteristic]

theorem initial_minus : transmission (-1) 0 = 1/2 := by
  norm_num [transmission, denominator, characteristic]

theorem isolated_optical_equal : isolatedStrength 1 = isolatedStrength (-1) := by
  norm_num [isolatedStrength]

theorem plus_later : transmission 1 (1/10) = 8100/19981 := by
  norm_num [transmission, denominator, characteristic]

theorem minus_later : transmission (-1) (1/10) = 12100/20021 := by
  norm_num [transmission, denominator, characteristic]

theorem later_distinct : transmission 1 (1/10) ≠ transmission (-1) (1/10) := by
  rw [plus_later, minus_later]
  norm_num

-- These identities certify the algebraic remainder. The manuscript uses
-- positivity and ordinary continuity to take the derivative limit.
theorem plus_first_order_remainder (x : ℝ) :
    2*denominator 1 x*(transmission 1 x-1/2+x) =
      x^2*(2+2*x-5*x^2+2*x^3) := by
  have hd := ne_of_gt (denominator_positive 1 x)
  unfold transmission
  field_simp
  unfold denominator characteristic
  ring

theorem minus_first_order_remainder (x : ℝ) :
    2*denominator (-1) x*(transmission (-1) x-1/2-x) =
      x^2*(2-2*x-5*x^2-2*x^3) := by
  have hd := ne_of_gt (denominator_positive (-1) x)
  unfold transmission
  field_simp
  unfold denominator characteristic
  ring

theorem no_conductance_only_predictor :
    ¬ ∃ f : ℝ → ℝ, ∀ s : ℝ, s=1 ∨ s=(-1) →
      f (transmission s 0)=transmission s (1/10) := by
  rintro ⟨f,h⟩
  have hp := h 1 (Or.inl rfl)
  have hm := h (-1) (Or.inr rfl)
  rw [initial_plus] at hp
  rw [initial_minus] at hm
  exact later_distinct (hp.symm.trans hm)

/-! ## V4: joint records and exact prediction margins

These declarations formalize the stronger finite-model statement already used
in the later manuscript: equal initial conductance plus equal isolated optical
strength still does not determine the displaced transmission. -/

def commonRecord (s : ℝ) : ℝ × ℝ :=
  (transmission s 0, isolatedStrength s)

theorem common_record_plus_minus :
    commonRecord 1 = commonRecord (-1) := by
  ext <;> norm_num [commonRecord, transmission, denominator, characteristic,
    isolatedStrength]

theorem no_common_record_predictor :
    ¬ ∃ f : (ℝ × ℝ) → ℝ, ∀ s : ℝ, s=1 ∨ s=(-1) →
      f (commonRecord s)=transmission s (1/10) := by
  rintro ⟨f,h⟩
  have hp := h 1 (Or.inl rfl)
  have hm := h (-1) (Or.inr rfl)
  rw [common_record_plus_minus] at hp
  exact later_distinct (hp.symm.trans hm)

theorem plus_later_lt_half : transmission 1 (1/10) < 1/2 := by
  rw [plus_later]
  norm_num

theorem half_lt_minus_later : 1/2 < transmission (-1) (1/10) := by
  rw [minus_later]
  norm_num

theorem later_gap_exact :
    transmission (-1) (1/10) - transmission 1 (1/10) =
      79600000/400039601 := by
  rw [minus_later, plus_later]
  norm_num

/-- Any single prediction assigned to the common record incurs at least half
of the exact pair separation as worst-case absolute error. -/
theorem two_model_minimax_bound (p : ℝ) :
    (transmission (-1) (1/10) - transmission 1 (1/10))/2 ≤
      max |p-transmission 1 (1/10)| |p-transmission (-1) (1/10)| := by
  have hp : p-transmission 1 (1/10) ≤ |p-transmission 1 (1/10)| :=
    le_abs_self _
  have hm : transmission (-1) (1/10)-p ≤ |p-transmission (-1) (1/10)| := by
    have h := neg_le_abs (p-transmission (-1) (1/10))
    linarith
  have hpm : |p-transmission 1 (1/10)| ≤
      max |p-transmission 1 (1/10)| |p-transmission (-1) (1/10)| :=
    le_max_left _ _
  have hmm : |p-transmission (-1) (1/10)| ≤
      max |p-transmission 1 (1/10)| |p-transmission (-1) (1/10)| :=
    le_max_right _ _
  linarith

/-- Separation survives independent additive perturbations whenever twice the
per-model error budget is smaller than the exact model separation. -/
theorem robust_separation {u v eps : ℝ}
    (hu : |u-transmission 1 (1/10)| ≤ eps)
    (hv : |v-transmission (-1) (1/10)| ≤ eps)
    (heps : 2*eps <
      transmission (-1) (1/10)-transmission 1 (1/10)) :
    u < v := by
  rcases abs_le.mp hu with ⟨huL, huU⟩
  rcases abs_le.mp hv with ⟨hvL, hvU⟩
  linarith

theorem robust_pair_margin {u v : ℝ}
    (hu : |u-transmission 1 (1/10)| ≤ 1/20)
    (hv : |v-transmission (-1) (1/10)| ≤ 1/20) :
    u < v := by
  apply robust_separation hu hv
  rw [later_gap_exact]
  norm_num

/-! ## V4: label-preserving boundary ledger

The following scalar inequalities are the finite algebra needed to keep a
positive contribution's denominator label until after inversion. They are not
Yang--Mills statements: the same resolvent bookkeeping applies to any declared
positive boundary/self-energy comparison. -/

def inverseChord (a b x : ℝ) : ℝ := (a+b-x)/(a*b)

theorem inverse_chord_identity (a b x : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) :
    inverseChord a b x - 1/x =
      ((x-a)*(b-x))/(a*b*x) := by
  unfold inverseChord
  field_simp [ha, hb, hx]
  ring

/-- The endpoint chord is a safe upper bound for the inverse on a positive
energy bin. This is the one-sided step needed before summing positive residues. -/
theorem inverse_le_chord {a b x : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    1/x ≤ inverseChord a b x := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hb : 0 < b := lt_of_lt_of_le hx hxb
  have hid := inverse_chord_identity a b x (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hx)
  have hnum : 0 ≤ (x-a)*(b-x) :=
    mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hxb)
  have hden : 0 ≤ a*b*x := le_of_lt (mul_pos (mul_pos ha hb) hx)
  have hfrac : 0 ≤ ((x-a)*(b-x))/(a*b*x) := div_nonneg hnum hden
  linarith

/-- Larger hidden energy lowers a nonnegative inverse-energy penalty. -/
theorem inverse_penalty_monotone {w d₀ d₁ z : ℝ}
    (hw : 0 ≤ w) (hz : z < d₀) (hd : d₀ ≤ d₁) :
    w/(d₁-z) ≤ w/(d₀-z) := by
  have h0 : 0 < d₀-z := sub_pos.mpr hz
  have h1 : 0 < d₁-z := by linarith
  apply (div_le_div_iff₀ h1 h0).2
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hd z) hw

/-- Keeping two positive denominator labels is never worse than replacing both
by one common lower floor. -/
theorem resolved_two_channel_le_floor {w₁ w₂ d₀ d₁ d₂ z : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hz : z < d₀) (h₁ : d₀ ≤ d₁) (h₂ : d₀ ≤ d₂) :
    w₁/(d₁-z)+w₂/(d₂-z) ≤ (w₁+w₂)/(d₀-z) := by
  have q₁ := inverse_penalty_monotone hw₁ hz h₁
  have q₂ := inverse_penalty_monotone hw₂ hz h₂
  calc
    w₁/(d₁-z)+w₂/(d₂-z) ≤ w₁/(d₀-z)+w₂/(d₀-z) := add_le_add q₁ q₂
    _ = (w₁+w₂)/(d₀-z) := by ring

/-- Two positive residues can be safely coarsened using only their zeroth and
first energy moments inside a declared positive bin. -/
theorem two_channel_chord_coarsening {a b x₁ x₂ w₁ w₂ : ℝ}
    (ha : 0 < a)
    (hax₁ : a ≤ x₁) (hx₁b : x₁ ≤ b)
    (hax₂ : a ≤ x₂) (hx₂b : x₂ ≤ b)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    w₁/x₁+w₂/x₂ ≤
      ((a+b)*(w₁+w₂)-(w₁*x₁+w₂*x₂))/(a*b) := by
  have q₁ := inverse_le_chord ha hax₁ hx₁b
  have q₂ := inverse_le_chord ha hax₂ hx₂b
  have wq₁ := mul_le_mul_of_nonneg_left q₁ hw₁
  have wq₂ := mul_le_mul_of_nonneg_left q₂ hw₂
  calc
    w₁/x₁+w₂/x₂ = w₁*(1/x₁)+w₂*(1/x₂) := by ring
    _ ≤ w₁*inverseChord a b x₁+w₂*inverseChord a b x₂ := add_le_add wq₁ wq₂
    _ = ((a+b)*(w₁+w₂)-(w₁*x₁+w₂*x₂))/(a*b) := by
      unfold inverseChord
      ring

/-- Exact negative control: replacing two inverse-energy contributions at
10 and 14 by their arithmetic-mean energy 12 underestimates the penalty. -/
theorem mean_before_inverse_underestimates :
    (2:ℝ)/12 < 1/10+1/14 := by
  norm_num

end
end ElementalFoundations

#print axioms ElementalFoundations.cross_expansion
#print axioms ElementalFoundations.cross_commutator
#print axioms ElementalFoundations.cross_zero_iff_commutes
#print axioms ElementalFoundations.centered_characteristic
#print axioms ElementalFoundations.denominator_positive
#print axioms ElementalFoundations.denominator_expansion
#print axioms ElementalFoundations.mirror_transmission
#print axioms ElementalFoundations.initial_plus
#print axioms ElementalFoundations.initial_minus
#print axioms ElementalFoundations.isolated_optical_equal
#print axioms ElementalFoundations.plus_later
#print axioms ElementalFoundations.minus_later
#print axioms ElementalFoundations.later_distinct
#print axioms ElementalFoundations.plus_first_order_remainder
#print axioms ElementalFoundations.minus_first_order_remainder
#print axioms ElementalFoundations.no_conductance_only_predictor
#print axioms ElementalFoundations.common_record_plus_minus
#print axioms ElementalFoundations.no_common_record_predictor
#print axioms ElementalFoundations.plus_later_lt_half
#print axioms ElementalFoundations.half_lt_minus_later
#print axioms ElementalFoundations.later_gap_exact
#print axioms ElementalFoundations.two_model_minimax_bound
#print axioms ElementalFoundations.robust_separation
#print axioms ElementalFoundations.robust_pair_margin
#print axioms ElementalFoundations.inverse_chord_identity
#print axioms ElementalFoundations.inverse_le_chord
#print axioms ElementalFoundations.inverse_penalty_monotone
#print axioms ElementalFoundations.resolved_two_channel_le_floor
#print axioms ElementalFoundations.two_channel_chord_coarsening
#print axioms ElementalFoundations.mean_before_inverse_underestimates
