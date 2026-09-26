import ElementalFoundations

/- Deliberately false controls. The CI job succeeds only when Lean rejects this
file with unsolved goals after all valid imports elaborate. -/

example : ElementalFoundations.transmission 1 (1/10) =
    ElementalFoundations.transmission (-1) (1/10) := by
  norm_num [ElementalFoundations.transmission, ElementalFoundations.denominator,
    ElementalFoundations.characteristic]

example : (1/10 : ℝ) + 1/14 ≤ 2/12 := by
  norm_num
