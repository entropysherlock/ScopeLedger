import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E1_twin_exact : SL003FC.Erdos441.SL003.targetProp := by
  unfold SL003FC.Erdos441.SL003.targetProp
  with_unfolding_all exact @Erdos441.not_erdos_441
