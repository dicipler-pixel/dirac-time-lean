/-
Affine phase readout and torus-knot silence (§9.2 and Theorem 13.1, parts 3–4, of
"The Dirac Time of the Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978631).

For an affine readout `x = A + B s`, `y = C + D s` the angular numerator
`x y' − y x' = A D − B C` does not depend on `s`: the phase lift is strictly monotone when it
is nonzero and the readout is silent when it vanishes.

On the arc `(a, b)` of the torus knot `T(p, q)`, the boundary sector `(m, n)` with offsets
`(ε_μ, ε_λ)` reads `x = m + ε_μ + α`, `y = n + ε_λ + a/2 − pq α`. Its numerator is
`A D − B C = −(pq (m + ε_μ) + n + ε_λ + a/2)`, so a silent sector exists exactly when
`pq ε_μ + ε_λ + a/2` is an integer.

At an end of the arc the index `k = u a q ± v b p`, with `u q ≡ 1 (mod p)` and
`v p ≡ 1 (mod q)`, satisfies `k ≡ a (mod p)` and `k ≡ ±b (mod q)`.
-/
import Mathlib

namespace DiracTime.PhaseSilence

/-- §9.2: the angular numerator of an affine readout is constant. -/
theorem affine_numerator (A B C D s : ℝ) :
    (A + B * s) * D - (C + D * s) * B = A * D - B * C := by
  ring

/-- Theorem 13.1(4): the phase numerator of the boundary sector `(m, n)`. -/
theorem sector_numerator (p q a m n : ℤ) (εμ ελ : ℝ) :
    (m + εμ) * (-(p * q : ℝ)) - 1 * (n + ελ + a / 2) =
      -((p * q : ℝ) * (m + εμ) + n + ελ + a / 2) := by
  ring

/-- **Theorem 13.1(4), silence criterion.** Some boundary sector is silent exactly when
`pq ε_μ + ε_λ + a/2` is an integer. -/
theorem silent_sector_iff (p q a : ℤ) (εμ ελ : ℝ) :
    (∃ m n : ℤ, (m + εμ) * (-(p * q : ℝ)) - 1 * (n + ελ + a / 2) = 0) ↔
      ∃ k : ℤ, (p * q : ℝ) * εμ + ελ + a / 2 = k := by
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨-(p * q * m) - n, ?_⟩
    push_cast
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨0, -k, ?_⟩
    push_cast
    linarith

/-- Theorem 13.1(3): the end index is `a` modulo `p`. -/
theorem end_index_mod_p (p q u v a b : ℤ) (hu : u * q ≡ 1 [ZMOD p]) :
    u * a * q + v * b * p ≡ a [ZMOD p] := by
  have h0 : v * b * p ≡ 0 [ZMOD p] := Int.modEq_zero_iff_dvd.mpr ⟨v * b, by ring⟩
  calc u * a * q + v * b * p ≡ u * a * q + 0 [ZMOD p] := Int.ModEq.add_left _ h0
    _ = a * (u * q) := by ring
    _ ≡ a * 1 [ZMOD p] := Int.ModEq.mul_left _ hu
    _ = a := mul_one a

/-- Theorem 13.1(3): the end index is `±b` modulo `q`. -/
theorem end_index_mod_q (p q u v a b : ℤ) (hv : v * p ≡ 1 [ZMOD q]) :
    u * a * q + v * b * p ≡ b [ZMOD q] ∧ u * a * q - v * b * p ≡ -b [ZMOD q] := by
  have h0 : u * a * q ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr ⟨u * a, by ring⟩
  have hb : v * b * p ≡ b [ZMOD q] := by
    calc v * b * p = b * (v * p) := by ring
      _ ≡ b * 1 [ZMOD q] := Int.ModEq.mul_left _ hv
      _ = b := mul_one b
  constructor
  · calc u * a * q + v * b * p ≡ 0 + b [ZMOD q] := Int.ModEq.add h0 hb
      _ = b := zero_add b
  · calc u * a * q - v * b * p ≡ 0 - b [ZMOD q] := Int.ModEq.sub h0 hb
      _ = -b := zero_sub b

end DiracTime.PhaseSilence
