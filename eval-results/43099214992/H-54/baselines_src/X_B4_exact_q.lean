import SL003Target

set_option maxHeartbeats 2000000 in
theorem SL004.bridge_B4_exact_q : SL003FC.Kourovka.«21.149».SL003.targetProp := by
  unfold SL003FC.Kourovka.«21.149».SL003.targetProp
  have h := @KourovkaNotebook.Solution21_149.kourovka_21_149
  exact?
