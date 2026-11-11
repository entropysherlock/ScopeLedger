import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Erdos522.SL003.targetProp := by
  unfold SL003FC.Erdos522.SL003.targetProp
  first | exact (@E522.erdos_522_zero_one_solved).mp trivial | with_unfolding_all exact (@E522.erdos_522_zero_one_solved).mp trivial
