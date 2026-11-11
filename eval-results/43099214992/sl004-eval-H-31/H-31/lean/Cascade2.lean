import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos136.SL003.targetProp := by
  unfold SL003FC.Erdos136.SL003.targetProp
  simpa [Colorable, Is45Coloring, f] using @Erdos136.erdos_136
