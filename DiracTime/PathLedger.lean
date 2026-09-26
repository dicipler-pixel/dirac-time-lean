/-
Path-ledger descent (Theorem P3 and programme item T3 of "The Dirac Time of the
Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978631).

Admitted paths between configurations carry a ledger in an abelian group `A` that adds
under concatenation and changes sign under reversal (spectral flow is the case `A = ℤ`).
On a connected configuration space the ledger is an endpoint potential,
`ℓ(γ) = n(y) - n(x)`, exactly when every admitted closed loop has zero ledger.

Also proved: positive-ledger reachability is not a time order. A path of ledger `r > 0`
and a loop of ledger `N > r` at its end give a path back of ledger `N - r > 0`.
-/
import Mathlib

namespace DiracTime.PathLedger

variable {X A : Type*} [AddCommGroup A] {P : X → X → Type*}

/-- **Theorem P3.** A path ledger is an endpoint potential exactly when every loop is
silent. -/
theorem descent_iff (comp : ∀ {x y z : X}, P x y → P y z → P x z)
    (rev : ∀ {x y : X}, P x y → P y x) (ℓ : ∀ {x y : X}, P x y → A)
    (hcomp : ∀ {x y z : X} (p : P x y) (q : P y z), ℓ (comp p q) = ℓ p + ℓ q)
    (hrev : ∀ {x y : X} (p : P x y), ℓ (rev p) = -ℓ p)
    (hconn : ∀ x y : X, Nonempty (P x y)) :
    (∃ n : X → A, ∀ {x y : X} (γ : P x y), ℓ γ = n y - n x) ↔
      ∀ {x : X} (c : P x x), ℓ c = 0 := by
  constructor
  · rintro ⟨n, hn⟩ x c
    rw [hn c, sub_self]
  · intro hloop
    by_cases hX : Nonempty X
    · obtain ⟨x0⟩ := hX
      let p : ∀ y, P x0 y := fun y => Classical.choice (hconn x0 y)
      refine ⟨fun y => ℓ (p y), fun {x y} γ => ?_⟩
      have h := hloop (comp (comp (p x) γ) (rev (p y)))
      rw [hcomp, hcomp, hrev] at h
      show ℓ γ = ℓ (p y) - ℓ (p x)
      calc ℓ γ = (ℓ (p x) + ℓ γ + -ℓ (p y)) + (ℓ (p y) - ℓ (p x)) := by abel
        _ = ℓ (p y) - ℓ (p x) := by rw [h, zero_add]
    · exact ⟨fun _ => 0, fun {x _} _ => absurd ⟨x⟩ hX⟩

/-- Positive-ledger reachability runs both ways: a path `x → y` of ledger `r` and a loop at
`y` of ledger `N` give a path `y → x` of ledger `N - r`, which is positive once `N > r`. -/
theorem reverse_path_ledger (comp : ∀ {x y z : X}, P x y → P y z → P x z)
    (rev : ∀ {x y : X}, P x y → P y x) (ℓ : ∀ {x y : X}, P x y → A)
    (hcomp : ∀ {x y z : X} (p : P x y) (q : P y z), ℓ (comp p q) = ℓ p + ℓ q)
    (hrev : ∀ {x y : X} (p : P x y), ℓ (rev p) = -ℓ p)
    {x y : X} (γ : P x y) (c : P y y) :
    ℓ (comp c (rev γ)) = ℓ c - ℓ γ := by
  rw [hcomp, hrev, sub_eq_add_neg]

/-- With integer ledgers: if `ℓ(γ) = r > 0` and a loop at the endpoint has `N > r`, the
reverse path also has positive ledger, so positive reachability is not antisymmetric. -/
theorem positive_both_ways {P : X → X → Type*} (comp : ∀ {x y z : X}, P x y → P y z → P x z)
    (rev : ∀ {x y : X}, P x y → P y x) (ℓ : ∀ {x y : X}, P x y → ℤ)
    (hcomp : ∀ {x y z : X} (p : P x y) (q : P y z), ℓ (comp p q) = ℓ p + ℓ q)
    (hrev : ∀ {x y : X} (p : P x y), ℓ (rev p) = -ℓ p)
    {x y : X} (γ : P x y) (c : P y y) (hγ : 0 < ℓ γ) (hc : ℓ γ < ℓ c) :
    0 < ℓ γ ∧ 0 < ℓ (comp c (rev γ)) := by
  refine ⟨hγ, ?_⟩
  rw [hcomp, hrev]
  omega

end DiracTime.PathLedger
