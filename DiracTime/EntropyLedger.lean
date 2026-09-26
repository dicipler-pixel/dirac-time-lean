/-
Finite entropy/correlation ledger (Theorem P6 and Corollary P6.1 of "The Dirac Time of the
Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978631).

A retained system `S` exchanges energy with reservoirs `r` (here any finite index set) with
fixed Gibbs references `τ_r = e^{−β_r H_r}/Z_r`, and the whole evolves unitarily. With heat
`Q_r = −ΔE_r` and multi-information `I = S_S + Σ_r S_r − S_total`,

  ΔS_S − Σ_r β_r Q_r = ΔI + Σ_r ΔD(ρ_r ‖ τ_r).

The proof uses two operator facts, taken here as hypotheses in the exact form the proof
uses them:
* Gibbs reference: `D(ρ_r ‖ τ_r) = −S(ρ_r) + β_r E(ρ_r) + log Z_r`, from
  `log τ_r = −β_r H_r − log Z_r` and `Tr ρ_r = 1`;
* unitary evolution preserves the total entropy, `ΔS_total = 0`.
Given those, the identity and the integrated second-law corollary are proved exactly.
Deriving the two operator facts in Lean (unitary invariance of von Neumann entropy, the
logarithm of a Gibbs state) is not done here.
-/
import Mathlib

namespace DiracTime.EntropyLedger

variable {ι : Type*} (s : Finset ι)

/-- With a Gibbs reference, the change of relative entropy is `ΔD = β ΔE − ΔS`: the
normalization `log Z` drops out of the difference. -/
theorem delta_relative_entropy (β logZ S₀ S₁ E₀ E₁ D₀ D₁ : ℝ)
    (h₀ : D₀ = -S₀ + β * E₀ + logZ) (h₁ : D₁ = -S₁ + β * E₁ + logZ) :
    D₁ - D₀ = β * (E₁ - E₀) - (S₁ - S₀) := by
  rw [h₀, h₁]
  ring

/-- **Theorem P6.** The exact finite entropy/correlation identity. -/
theorem entropy_correlation_identity (β logZ : ι → ℝ)
    (SS₀ SS₁ Stot₀ Stot₁ : ℝ) (Sr₀ Sr₁ Er₀ Er₁ Dr₀ Dr₁ : ι → ℝ)
    (hD₀ : ∀ r ∈ s, Dr₀ r = -Sr₀ r + β r * Er₀ r + logZ r)
    (hD₁ : ∀ r ∈ s, Dr₁ r = -Sr₁ r + β r * Er₁ r + logZ r)
    (hU : Stot₁ = Stot₀) :
    let I₀ := SS₀ + ∑ r ∈ s, Sr₀ r - Stot₀
    let I₁ := SS₁ + ∑ r ∈ s, Sr₁ r - Stot₁
    let Q := fun r => -(Er₁ r - Er₀ r)
    (SS₁ - SS₀) - ∑ r ∈ s, β r * Q r = (I₁ - I₀) + ∑ r ∈ s, (Dr₁ r - Dr₀ r) := by
  intro I₀ I₁ Q
  have hD : ∀ r ∈ s, Dr₁ r - Dr₀ r = β r * (Er₁ r - Er₀ r) - (Sr₁ r - Sr₀ r) := fun r hr =>
    delta_relative_entropy (β r) (logZ r) _ _ _ _ _ _ (hD₀ r hr) (hD₁ r hr)
  rw [Finset.sum_congr rfl hD]
  simp only [I₀, I₁, Q, hU, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
  ring

/-- **Corollary P6.1.** Starting uncorrelated with every reservoir in its Gibbs state (so the
initial multi-information and relative entropies vanish), and using that multi-information
and relative entropy are nonnegative, the integrated entropy production is nonnegative. -/
theorem integrated_second_law (β : ι → ℝ) (dSS I₁ : ℝ) (Q D₁ : ι → ℝ)
    (hP6 : dSS - ∑ r ∈ s, β r * Q r = (I₁ - 0) + ∑ r ∈ s, (D₁ r - 0))
    (hI : 0 ≤ I₁) (hD : ∀ r ∈ s, 0 ≤ D₁ r) :
    0 ≤ dSS - ∑ r ∈ s, β r * Q r := by
  rw [hP6]
  have : 0 ≤ ∑ r ∈ s, (D₁ r - 0) := Finset.sum_nonneg fun r hr => by
    rw [sub_zero]
    exact hD r hr
  linarith

end DiracTime.EntropyLedger
