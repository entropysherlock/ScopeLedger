import SL003Target

/-! SL-004 Layer B round 1 (Claude), H-31 (Erdős 136). Class C1: FC's `f n = sInf {k | Colorable n k}`;
the project's `erdos136Fun n = Nat.find _` with `erdos136Fun_spec` and `erdos136Fun_min`; the two
`Colorable` are twins, so `IsLeast.csInf_eq` gives the correspondence. -/

theorem SL004.corrH31 (n : ℕ) : SL003FC.Erdos136.f n = Erdos136.erdos136Fun n := by
  unfold SL003FC.Erdos136.f
  apply IsLeast.csInf_eq
  refine ⟨?_, fun k hk => Erdos136.erdos136Fun_min ?_⟩
  · have := Erdos136.erdos136Fun_spec n
    with_unfolding_all exact this
  · with_unfolding_all exact hk

theorem SL004.bridgeH31 : SL003FC.Erdos136.SL003.targetProp := by
  unfold SL003FC.Erdos136.SL003.targetProp
  simp only [SL004.corrH31]
  exact Erdos136.erdos_136
