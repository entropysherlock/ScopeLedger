import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Erdos780.SL003.targetProp := by
  unfold SL003FC.Erdos780.SL003.targetProp
  first | exact (@Erdos780.erdos_780).mp trivial | with_unfolding_all exact (@Erdos780.erdos_780).mp trivial
