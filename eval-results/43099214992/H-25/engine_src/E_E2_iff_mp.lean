import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.SpectralSetProduct.SL003.targetProp := by
  unfold SL003FC.SpectralSetProduct.SL003.targetProp
  first | exact (@ProductInterval.fc_three_dimensional).mp trivial | with_unfolding_all exact (@ProductInterval.fc_three_dimensional).mp trivial
