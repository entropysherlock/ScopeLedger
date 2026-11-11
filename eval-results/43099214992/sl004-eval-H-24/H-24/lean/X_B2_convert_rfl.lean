import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B2_convert_rfl : SL003FC.Erdos889.SL003.targetProp := by
  unfold SL003FC.Erdos889.SL003.targetProp
  have h := @Erdos889Proof.erdos_889_V1_eq_1_finite_solved
  convert h using 3 <;> rfl
