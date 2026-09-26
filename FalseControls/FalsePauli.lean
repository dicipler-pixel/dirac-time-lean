import PauliMemory
-- Deliberately false: coincidence cannot have positive same-spin pair density.
example : 0 < PauliMemory.pairDensity 1 0 0 0 1 0 0 0 := by
  norm_num [PauliMemory.pairDensity, PauliMemory.density,
    PauliMemory.coherenceReal, PauliMemory.coherenceImag]
