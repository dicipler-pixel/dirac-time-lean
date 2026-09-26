import OpticalMetric
example : LightConstitutive.transitionMetric 1 1 + LightConstitutive.transitionMetric 2 2 = 0 := by norm_num [LightConstitutive.transitionMetric]
