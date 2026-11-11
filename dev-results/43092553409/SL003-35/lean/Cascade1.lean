import SL003Target

theorem SL003.cascade1 : SL003FC.Erdos737.SL003.targetProp := by
  unfold SL003FC.Erdos737.SL003.targetProp
  exact_mod_cast @Erdos737.eventually_cycles_through_fixed_edge
