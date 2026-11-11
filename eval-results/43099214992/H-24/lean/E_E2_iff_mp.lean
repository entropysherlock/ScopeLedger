import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E2_iff_mp : SL003FC.Erdos889.SL003.targetProp := by
  unfold SL003FC.Erdos889.SL003.targetProp
  first | exact (@Erdos889Proof.erdos_889_V1_eq_1_finite_solved).mp trivial | with_unfolding_all exact (@Erdos889Proof.erdos_889_V1_eq_1_finite_solved).mp trivial
