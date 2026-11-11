import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B1_exact : SL003FC.Erdos1180.SL003.targetProp := by
  unfold SL003FC.Erdos1180.SL003.targetProp
  exact @Erdos1180.Palomar.erdos_1180_variants_shparlinski
