import SL003Target

set_option maxHeartbeats 400000 in
theorem SL004.bridge_E3_convert_p0_k3 : SL003FC.Erdos889.SL003.targetProp := by
  unfold SL003FC.Erdos889.SL003.targetProp
  have h := @Erdos889Proof.erdos_889_V1_eq_1_finite_solved
  convert h using 3 <;> (first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp) | (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩) | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)) | (apply funext; intro; first | with_unfolding_all rfl | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩))))
