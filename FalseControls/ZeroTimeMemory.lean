import UPGFeedback

/- Deliberately false: a nonzero one-channel coupling cannot have zero
zero-time memory Gram. CI succeeds only when Lean rejects this file. -/

example : UPGFeedback.memoryAtZero (!![(1 : ℝ)]) = 0 := by
  norm_num [UPGFeedback.memoryAtZero]
