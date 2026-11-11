import SL003Target

/-! Bridge for H-21 (Erdős 841, many small values): from
`Erdos841.erdos841_many_small_values_global`, with `K = 20`. -/

namespace SL004.H21

/-- The transported `t` (an `sInf`) agrees with the cited `t` (a `Nat.find`). -/
theorem t_eq (n : ℕ) : SL003FC.Erdos841.t n = Erdos841.t n := by
  unfold SL003FC.Erdos841.t
  apply le_antisymm
  · exact Nat.sInf_le (Erdos841.t_spec n)
  · exact Erdos841.t_le_of_admissible (n := n)
      (Nat.sInf_mem (s := {T : ℕ | ∃ J ⊆ Finset.Icc 1 T, IsSquare (n * ∏ j ∈ J, (n + j))})
        ⟨Erdos841.t n, Erdos841.t_spec n⟩)

end SL004.H21

theorem SL004.bridge_main : SL003FC.Erdos841.SL003.targetProp := by
  unfold SL003FC.Erdos841.SL003.targetProp
  refine ⟨20, (Erdos841.erdos841_many_small_values_global.1).congr (fun x => ?_)⟩
  refine congrArg (fun s : Finset ℕ => Real.log (s.card : ℝ) / Real.log (x : ℝ)) ?_
  ext n
  rw [Erdos841.erdos841_many_small_values_global.2 x n, Finset.mem_filter, Finset.mem_Icc,
    SL004.H21.t_eq]
  tauto
