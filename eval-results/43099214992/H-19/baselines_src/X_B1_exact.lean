import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_B1_exact : SL003FC.Erdos1021.SL003.targetProp := by
  unfold SL003FC.Erdos1021.SL003.targetProp
  exact @Erdos1021.erdos_1021
