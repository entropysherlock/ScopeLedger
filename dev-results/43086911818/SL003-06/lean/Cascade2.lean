import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos441.SL003.targetProp := by
  unfold SL003FC.Erdos441.SL003.targetProp
  simpa [erdosConstruction, g] using @Erdos441.not_erdos_441
