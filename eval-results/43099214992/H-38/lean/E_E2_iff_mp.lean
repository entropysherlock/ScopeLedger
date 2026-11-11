import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Erdos1050.SL003.targetProp := by
  unfold SL003FC.Erdos1050.SL003.targetProp
  first | exact (@LeanGallery.NumberTheory.Erdos1050.erdos_1050).mp trivial | with_unfolding_all exact (@LeanGallery.NumberTheory.Erdos1050.erdos_1050).mp trivial
