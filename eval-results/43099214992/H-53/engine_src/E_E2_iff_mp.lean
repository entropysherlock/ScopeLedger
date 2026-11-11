import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Erdos109.SL003.targetProp := by
  unfold SL003FC.Erdos109.SL003.targetProp
  first | exact (@Erdos109.erdos_109).mp trivial | with_unfolding_all exact (@Erdos109.erdos_109).mp trivial
