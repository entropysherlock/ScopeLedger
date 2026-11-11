import SL003Target

set_option maxHeartbeats 2000000 in
theorem SL004.bridge_B4_exact_q : SL003FC.Erdos261.SL003.targetProp := by
  unfold SL003FC.Erdos261.SL003.targetProp
  have h := @Erdos261.Palomar.borwein_loring
  exact?
