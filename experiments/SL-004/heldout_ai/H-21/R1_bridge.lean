import SL003Target

/-! SL-004 Layer B round 1 (Claude), H-21 (Erdős 841, many small values). Classes C1 + L: FC's `t`
(an `sInf`) equals the project's `t = Nat.find _` (`IsLeast.csInf_eq` with `t_spec`,
`t_le_of_admissible`); the cited limit is FC's with `K = 20`, and `manySmallUpTo x` is FC's filtered
interval. -/

theorem SL004.corrH21_t (n : ℕ) : SL003FC.Erdos841.t n = Erdos841.t n := by
  unfold SL003FC.Erdos841.t
  apply IsLeast.csInf_eq
  exact ⟨Erdos841.t_spec n, fun T hT => Erdos841.t_le_of_admissible hT⟩

theorem SL004.bridgeH21 : SL003FC.Erdos841.SL003.targetProp := by
  unfold SL003FC.Erdos841.SL003.targetProp
  refine ⟨20, ?_⟩
  have h := (Erdos841.erdos841_many_small_values_global).1
  simp only [SL004.corrH21_t]
  first
    | exact h
    | with_unfolding_all exact h
