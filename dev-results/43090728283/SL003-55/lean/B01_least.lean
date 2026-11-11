import SL003Target

/-! SL-004 dev, SL003-55 (Erdős 841, lower bound). Correspondence by characterisation: the project's
`t n = Nat.find (exists_admissible n)` is the least admissible `T` (`t_spec`, `t_le_of_admissible`),
and `Admissible n` is FC's set predicate, so FC's `sInf` equals it (`IsLeast.csInf_eq`). The bridge
supplies the cited explicit constant and its positivity, and rewrites `-1/5 = -(1/5)`. -/

theorem SL004.corr55_t (n : ℕ) : SL003FC.Erdos841.t n = Erdos841.t n := by
  unfold SL003FC.Erdos841.t
  apply IsLeast.csInf_eq
  exact ⟨Erdos841.t_spec n, fun T hT => Erdos841.t_le_of_admissible hT⟩

theorem SL004.bridge55 : SL003FC.Erdos841.SL003.targetProp := by
  unfold SL003FC.Erdos841.SL003.targetProp
  refine ⟨Erdos841.pellLowerBoundConstant, Erdos841.pellLowerBoundConstant_pos, ?_⟩
  filter_upwards [Erdos841.erdos841_lower_bound_explicit] with n hn hsq
  rw [SL004.corr55_t n, show (-1 / 5 : ℝ) = -(1 / 5) by ring]
  exact hn hsq
