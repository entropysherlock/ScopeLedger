import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Erdos1180.SL003.targetProp := by
  unfold SL003FC.Erdos1180.SL003.targetProp
  first | exact (@Erdos1180.Palomar.erdos_1180_variants_shparlinski).mp trivial | with_unfolding_all exact (@Erdos1180.Palomar.erdos_1180_variants_shparlinski).mp trivial
