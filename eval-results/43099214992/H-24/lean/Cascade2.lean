import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos889.SL003.targetProp := by
  unfold SL003FC.Erdos889.SL003.targetProp
  simpa [V, V_l, v, v_l, v₀] using @Erdos889Proof.erdos_889_V1_eq_1_finite_solved
