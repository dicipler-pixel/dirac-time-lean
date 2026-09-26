import PauliMemory
-- Deliberately false: equal instantaneous readouts do not ensure equal futures.
example : PauliMemory.delayedReadout 0 1 0 1 1 =
    PauliMemory.delayedReadout 0 1 0 (-1) 1 := by
  norm_num [PauliMemory.delayedReadout, PauliMemory.delayedCoordinate,
    PauliMemory.affineReadout]
