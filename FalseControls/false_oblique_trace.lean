import LightBridges.Examples
example : (LightBridges.obliqueP0 * LightBridges.obliqueP1).trace ≤ 1 := by rw [LightBridges.oblique_trace_two]; norm_num
