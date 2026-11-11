import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E1_twin_exact : SL003FC.SpectralSetProduct.SL003.targetProp := by
  unfold SL003FC.SpectralSetProduct.SL003.targetProp
  with_unfolding_all exact @ProductInterval.fc_three_dimensional
