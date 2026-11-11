import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p3_k3 : SL003FC.Erdos1096.SL003.targetProp := by
  unfold SL003FC.Erdos1096.SL003.targetProp
  have h := (@Erdos1096.erdos_1096).2.1
  convert h using 3 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp) | (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩) | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)) | (apply funext; intro; first | with_unfolding_all rfl | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩))))
