import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B3_aesop : SL003FC.Erdos889.SL003.targetProp := by
  unfold SL003FC.Erdos889.SL003.targetProp
  have h := @Erdos889Proof.erdos_889_V1_eq_1_finite_solved
  aesop
