import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.BorweinSineSeries.SL003.targetProp := by
  unfold SL003FC.BorweinSineSeries.SL003.targetProp
  first | exact (@borwein_sine_series).mp trivial | with_unfolding_all exact (@borwein_sine_series).mp trivial
