import SL003Target

theorem SL003.direct : SL003FC.Erdos737.SL003.targetProp := by
  unfold SL003FC.Erdos737.SL003.targetProp
  exact @Erdos737.eventually_cycles_through_fixed_edge
