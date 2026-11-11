import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos737.SL003.targetProp := by
  unfold SL003FC.Erdos737.SL003.targetProp
  simpa [ChromaticNumberAlephOne, CycleThroughEdgeOfLength] using @Erdos737.eventually_cycles_through_fixed_edge
