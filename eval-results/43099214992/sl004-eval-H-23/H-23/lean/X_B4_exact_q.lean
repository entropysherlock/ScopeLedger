import SL003Target

set_option maxHeartbeats 2000000 in
theorem SL004.bridge_B4_exact_q : SL003FC.Erdos1180.SL003.targetProp := by
  unfold SL003FC.Erdos1180.SL003.targetProp
  have h := @Erdos1180.Palomar.erdos_1180_variants_shparlinski
  exact?
