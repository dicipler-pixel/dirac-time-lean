/-
Appendix E memory engine (pp. 92–93 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978630).

After a memory contact of strength `η`,
`p* = (1 − η) p_h + η p_m` and `p'_m = (1 − η) p_m + η p_h`. The ledger is
`W_out = (ε_h − ε_c) (p* − p_c)`, `Q_h = ε_h (p_h − p_c)`, `Q_c = ε_c (p_c − p*)`,
`ΔE_M = ε_h η (p_h − p_m)`, with `W_out = Q_h + Q_c − ΔE_M`.

Iterating the memory update gives
`p_m^{(n)} = p_h + (1 − η)^n (p_m^{(0)} − p_h)` and
`W_n = (ε_h − ε_c) [p_h − p_c + η (1 − η)^n (p_m^{(0)} − p_h)]`.
Two histories with the same working state therefore differ by
`W_n^{(a)} − W_n^{(b)} = (ε_h − ε_c) η (1 − η)^n (p_{m,a}^{(0)} − p_{m,b}^{(0)})`,
and the retained excess sums to
`∑_{n < N} (W_n − W_∞) = (ε_h − ε_c) (p_m^{(0)} − p_h) [1 − (1 − η)^N]`.
-/
import Mathlib

namespace DiracTime.MemoryEngine

/-- Working population after the memory contact. -/
def pStar (η ph pm : ℝ) : ℝ := (1 - η) * ph + η * pm

/-- Memory population after the contact. -/
def pMemStep (η ph pm : ℝ) : ℝ := (1 - η) * pm + η * ph

/-- Output work `W_out = (ε_h − ε_c) (p* − p_c)`. -/
def wOut (εh εc ph pc pm η : ℝ) : ℝ := (εh - εc) * (pStar η ph pm - pc)

/-- Hot heat `Q_h = ε_h (p_h − p_c)`. -/
def qHot (εh ph pc : ℝ) : ℝ := εh * (ph - pc)

/-- Cold heat `Q_c = ε_c (p_c − p*)`. -/
def qCold (εc ph pc pm η : ℝ) : ℝ := εc * (pc - pStar η ph pm)

/-- Memory energy change `ΔE_M = ε_h η (p_h − p_m)`. -/
def deltaEM (εh η ph pm : ℝ) : ℝ := εh * η * (ph - pm)

/-- **DT-C220.** Exact closure `W_out = Q_h + Q_c − ΔE_M`. -/
theorem work_heat_closure (εh εc ph pc pm η : ℝ) :
    wOut εh εc ph pc pm η =
      qHot εh ph pc + qCold εc ph pc pm η - deltaEM εh η ph pm := by
  simp only [wOut, qHot, qCold, deltaEM, pStar]
  ring

/-- Memory population after `n` contacts with a fixed hot population. -/
def pMem (η ph p0 : ℝ) : ℕ → ℝ
  | 0 => p0
  | n + 1 => (1 - η) * pMem η ph p0 n + η * ph

theorem pMem_succ (η ph p0 : ℝ) (n : ℕ) :
    pMem η ph p0 (n + 1) = pMemStep η ph (pMem η ph p0 n) := by
  simp [pMem, pMemStep]

/-- **DT-C222, population.** `p_m^{(n)} = p_h + (1 − η)^n (p_m^{(0)} − p_h)`. -/
theorem pMem_closed (η ph p0 : ℝ) (n : ℕ) :
    pMem η ph p0 n = ph + (1 - η) ^ n * (p0 - ph) := by
  induction n with
  | zero => simp [pMem]
  | succ n ih =>
    rw [pMem, ih]
    ring

/-- Work at step `n`, `W_n = (ε_h − ε_c) [p_h − p_c + η (1 − η)^n (p_m^{(0)} − p_h)]`. -/
def wStep (εh εc ph pc η p0 : ℝ) (n : ℕ) : ℝ :=
  (εh - εc) * (ph - pc + η * (1 - η) ^ n * (p0 - ph))

/-- Steady work after the memory has equilibrated, `W_∞ = (ε_h − ε_c) (p_h − p_c)`. -/
def wInf (εh εc ph pc : ℝ) : ℝ := (εh - εc) * (ph - pc)

theorem wStep_eq_wOut (εh εc ph pc η p0 : ℝ) (n : ℕ) :
    wOut εh εc ph pc (pMem η ph p0 n) η = wStep εh εc ph pc η p0 n := by
  simp only [wOut, wStep, pStar, pMem_closed]
  ring

/-- **DT-C222, work gap.** Histories with the same present working state differ by the
retained memory. -/
theorem work_history_difference (εh εc ph pc η p0a p0b : ℝ) (n : ℕ) :
    wStep εh εc ph pc η p0a n - wStep εh εc ph pc η p0b n =
      (εh - εc) * η * (1 - η) ^ n * (p0a - p0b) := by
  simp only [wStep]
  ring

theorem geom_sum_mul (x : ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, x ^ i) * (x - 1) = x ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

theorem eta_geom_sum (η : ℝ) (N : ℕ) :
    η * ∑ n ∈ Finset.range N, (1 - η) ^ n = 1 - (1 - η) ^ N := by
  have h := geom_sum_mul (1 - η) N
  have hr : (1 - η) - 1 = -η := by ring
  rw [hr] at h
  have hneg := congrArg Neg.neg h
  simpa [neg_mul, neg_neg, neg_sub, mul_comm] using hneg

/-- **DT-C223.** The retained excess is finite:
`∑_{n < N} (W_n − W_∞) = (ε_h − ε_c) (p_m^{(0)} − p_h) [1 − (1 − η)^N]`. -/
theorem retained_memory_sum (εh εc ph pc η p0 : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (wStep εh εc ph pc η p0 n - wInf εh εc ph pc) =
      (εh - εc) * (p0 - ph) * (1 - (1 - η) ^ N) := by
  have hterm : ∀ n ∈ Finset.range N,
      wStep εh εc ph pc η p0 n - wInf εh εc ph pc =
        (εh - εc) * (p0 - ph) * (η * (1 - η) ^ n) := by
    intro n _
    simp only [wStep, wInf]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hpull : ∑ n ∈ Finset.range N, η * (1 - η) ^ n =
      η * ∑ n ∈ Finset.range N, (1 - η) ^ n := by
    rw [Finset.mul_sum]
  rw [hpull, eta_geom_sum, mul_assoc]

end DiracTime.MemoryEngine
