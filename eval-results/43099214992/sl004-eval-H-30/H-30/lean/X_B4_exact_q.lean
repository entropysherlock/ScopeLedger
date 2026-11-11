import SL003Target

set_option maxHeartbeats 2000000 in
theorem SL004.bridge_B4_exact_q : SL003FC.Erdos674.SL003.targetProp := by
  unfold SL003FC.Erdos674.SL003.targetProp
  have h := @Erdos674.erdos_674
  exact?
