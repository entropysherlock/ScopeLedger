import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.OeisA361033.SL003.targetProp := by
  unfold SL003FC.OeisA361033.SL003.targetProp
  first | exact (@A361033.a_odd_iff).mp trivial | with_unfolding_all exact (@A361033.a_odd_iff).mp trivial
