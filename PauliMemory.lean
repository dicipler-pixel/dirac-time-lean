import Mathlib

/-! Algebraic certificates for exclusion and a common retained coordinate.
These theorems do not derive a material Hamiltonian, an optical force, or a
geometric-phase interpretation. Coordinates below are real and imaginary
parts of two orbital samples. The memory law is an explicit affine model. -/
set_option autoImplicit false
noncomputable section
namespace PauliMemory

/-- Density from two complex orbital values at one position. -/
def density (ar ai br bi : ℝ) : ℝ := ar^2 + ai^2 + br^2 + bi^2

def coherenceReal (ar ai br bi cr ci dr di : ℝ) : ℝ :=
  ar*cr + ai*ci + br*dr + bi*di

def coherenceImag (ar ai br bi cr ci dr di : ℝ) : ℝ :=
  ai*cr - ar*ci + bi*dr - br*di

def wedgeReal (ar ai br bi cr ci dr di : ℝ) : ℝ :=
  ar*dr - ai*di - br*cr + bi*ci

def wedgeImag (ar ai br bi cr ci dr di : ℝ) : ℝ :=
  ar*di + ai*dr - br*ci - bi*cr

/-- The exchange-subtracted pair density. No chosen exclusion length occurs. -/
def pairDensity (ar ai br bi cr ci dr di : ℝ) : ℝ :=
  density ar ai br bi * density cr ci dr di -
  (coherenceReal ar ai br bi cr ci dr di)^2 -
  (coherenceImag ar ai br bi cr ci dr di)^2

/-- Complex two-orbital Gram determinant equals squared antisymmetric amplitude. -/
theorem pauli_gram_identity (ar ai br bi cr ci dr di : ℝ) :
    pairDensity ar ai br bi cr ci dr di =
    (wedgeReal ar ai br bi cr ci dr di)^2 +
    (wedgeImag ar ai br bi cr ci dr di)^2 := by
  unfold pairDensity density coherenceReal coherenceImag wedgeReal wedgeImag
  ring

theorem pair_density_nonnegative (ar ai br bi cr ci dr di : ℝ) :
    0 ≤ pairDensity ar ai br bi cr ci dr di := by
  rw [pauli_gram_identity]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Coincidence is exactly forbidden for the same spin sector in this algebra. -/
theorem coincident_pair_density_zero (ar ai br bi : ℝ) :
    pairDensity ar ai br bi ar ai br bi = 0 := by
  unfold pairDensity density coherenceReal coherenceImag
  ring

theorem silent_pair_iff_zero_wedge (ar ai br bi cr ci dr di : ℝ) :
    pairDensity ar ai br bi cr ci dr di = 0 ↔
    wedgeReal ar ai br bi cr ci dr di = 0 ∧
    wedgeImag ar ai br bi cr ci dr di = 0 := by
  rw [pauli_gram_identity]
  constructor
  · intro h
    have hr := sq_nonneg (wedgeReal ar ai br bi cr ci dr di)
    have hi := sq_nonneg (wedgeImag ar ai br bi cr ci dr di)
    constructor <;> nlinarith
  · rintro ⟨hr, hi⟩
    rw [hr, hi]
    norm_num

/-- Antisymmetry does not forbid pairs at all distinct orbital samples. -/
theorem noncoincident_pair_witness : pairDensity 1 0 0 0 0 0 1 0 = 1 := by
  norm_num [pairDensity, density, coherenceReal, coherenceImag]

/-- A change in one shared retained coordinate drives both declared readouts. -/
def affineReadout (base slope q : ℝ) : ℝ := base + slope*q

def delayedCoordinate (q0 velocity kernel : ℝ) : ℝ := q0 + velocity*kernel

def delayedReadout (base slope q0 velocity kernel : ℝ) : ℝ :=
  affineReadout base slope (delayedCoordinate q0 velocity kernel)

theorem instantaneous_velocity_invisible (base slope q0 v : ℝ) :
    delayedReadout base slope q0 v 0 =
    delayedReadout base slope q0 (-v) 0 := by
  simp [delayedReadout, delayedCoordinate, affineReadout]

theorem delayed_opposite_velocity_difference (base slope q0 v kernel : ℝ) :
    delayedReadout base slope q0 v kernel -
    delayedReadout base slope q0 (-v) kernel = 2*slope*v*kernel := by
  unfold delayedReadout delayedCoordinate affineReadout
  ring

/-- Exact ratio-free paired-signal constraint; valid also at zero slopes. -/
theorem paired_signal_constraint (baseG slopeG baseO slopeO q0 v kernel : ℝ) :
    slopeO * (delayedReadout baseG slopeG q0 v kernel -
      delayedReadout baseG slopeG q0 (-v) kernel) =
    slopeG * (delayedReadout baseO slopeO q0 v kernel -
      delayedReadout baseO slopeO q0 (-v) kernel) := by
  unfold delayedReadout delayedCoordinate affineReadout
  ring

theorem delayed_readouts_differ (base slope q0 v kernel : ℝ)
    (hs : slope ≠ 0) (hv : v ≠ 0) (hk : kernel ≠ 0) :
    delayedReadout base slope q0 v kernel ≠
    delayedReadout base slope q0 (-v) kernel := by
  intro h
  have hd := delayed_opposite_velocity_difference base slope q0 v kernel
  rw [h, sub_self] at hd
  have hp : 2*slope*v*kernel ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs) hv) hk
  exact hp hd.symm

/-- A single instantaneous affine reading cannot predict this declared future
across the two opposite retained velocities. -/
theorem no_instantaneous_only_predictor (base slope q0 v kernel : ℝ)
    (hs : slope ≠ 0) (hv : v ≠ 0) (hk : kernel ≠ 0) :
    ¬ ∃ f : ℝ → ℝ, ∀ w : ℝ, w = v ∨ w = -v →
      f (delayedReadout base slope q0 w 0) =
        delayedReadout base slope q0 w kernel := by
  rintro ⟨f, hf⟩
  have hp := hf v (Or.inl rfl)
  have hm := hf (-v) (Or.inr rfl)
  rw [instantaneous_velocity_invisible base slope q0 v] at hp
  exact delayed_readouts_differ base slope q0 v kernel hs hv hk (hp.symm.trans hm)

/-- At stationary positive box lengths with a common pressure, the spinless
(two lowest levels) and double-ground-state reference lengths obey this cube
ratio. The calculus giving the stationarity hypotheses is outside this lemma. -/
theorem exclusion_box_cube_ratio (pressure c lengthF lengthB : ℝ)
    (hp : pressure ≠ 0)
    (hF : pressure*lengthF^3 = 2*c*5)
    (hB : pressure*lengthB^3 = 2*c*2) :
    2*lengthF^3 = 5*lengthB^3 := by
  have hmul : pressure * (2*lengthF^3) = pressure * (5*lengthB^3) := by
    nlinarith [hF, hB]
  exact mul_left_cancel₀ hp hmul

/-- Positive lengths make the exclusion-induced increase strict. -/
theorem exclusion_box_length_increases (lengthF lengthB : ℝ)
    (hB : 0 < lengthB) (hF : 0 ≤ lengthF)
    (hr : 2*lengthF^3 = 5*lengthB^3) : lengthB < lengthF := by
  by_contra h
  have hle : lengthF ≤ lengthB := le_of_not_gt h
  have hcube : lengthF^3 ≤ lengthB^3 := pow_le_pow_left₀ hF hle 3
  have hpos : 0 < lengthB^3 := pow_pos hB 3
  nlinarith

/-- Synthetic four-bin linear observer; coefficients are not CIE calibrations. -/
def colorObserver (s : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i => s (Fin.castSucc i) + s 3

def spectrumA : Fin 4 → ℝ := fun i => if i.val = 3 then 0 else 1
def spectrumB : Fin 4 → ℝ := fun i => if i.val = 3 then 1 else 0
def passiveFilter (s : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => (if i.val = 0 then 1 else if i.val = 1 then 1/2 else if i.val = 2 then 1/4 else 3/4) * s i

theorem equal_initial_color : colorObserver spectrumA = colorObserver spectrumB := by
  ext i
  fin_cases i <;> norm_num [colorObserver, spectrumA, spectrumB, Fin.castSucc]

theorem next_surface_color_differs :
    colorObserver (passiveFilter spectrumA) ≠ colorObserver (passiveFilter spectrumB) := by
  intro h
  have h0 := congrFun h 0
  norm_num [colorObserver, passiveFilter, spectrumA, spectrumB, Fin.castSucc] at h0

/-- Equal first-observer records do not universally determine the next-filter record. -/
theorem no_color_only_next_filter_predictor :
    ¬ ∃ f : (Fin 3 → ℝ) → (Fin 3 → ℝ), ∀ s : Fin 4 → ℝ,
      f (colorObserver s) = colorObserver (passiveFilter s) := by
  rintro ⟨f, hf⟩
  have ha := hf spectrumA
  have hb := hf spectrumB
  rw [equal_initial_color] at ha
  exact next_surface_color_differs (ha.symm.trans hb)

/-- Declared two-level projector metric and zero-time force-memory coefficient. -/
def coordinateMetric (g a R : ℝ) : ℝ := g^2*a^2/(4*R^4)
def forceMemoryWeight (g a R : ℝ) : ℝ := g^2*a^2/R^3

/-- This certifies the coefficient relation after the physical derivations of
metric, gap 2R and force kernel have been supplied. -/
theorem force_memory_is_gap_weighted_metric (g a R : ℝ) (hR : R ≠ 0) :
    forceMemoryWeight g a R = 2*(2*R)*coordinateMetric g a R := by
  unfold forceMemoryWeight coordinateMetric
  field_simp [hR]
  <;> ring

theorem force_memory_weight_positive (g a R : ℝ)
    (hg : g ≠ 0) (ha : a ≠ 0) (hR : 0 < R) :
    0 < forceMemoryWeight g a R := by
  unfold forceMemoryWeight
  exact div_pos (mul_pos (sq_pos_of_ne_zero hg) (sq_pos_of_ne_zero ha)) (pow_pos hR 3)

end PauliMemory
