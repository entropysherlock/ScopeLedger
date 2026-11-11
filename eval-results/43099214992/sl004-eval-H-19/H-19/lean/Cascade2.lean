import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos1021.SL003.targetProp := by
  unfold SL003FC.Erdos1021.SL003.targetProp
  simpa [cliqueSubdivision] using @Erdos1021.erdos_1021
