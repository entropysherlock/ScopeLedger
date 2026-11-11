import SL003Target

open Filter Real Topology

theorem SL004.t_eq (n : ℕ) : SL003FC.Erdos841.t n = Erdos841.t n := by
  unfold SL003FC.Erdos841.t
  apply le_antisymm
  · exact Nat.sInf_le (Erdos841.t_spec n)
  · have hne : {T | ∃ J ⊆ Finset.Icc 1 T, IsSquare (n * ∏ j ∈ J, (n + j))}.Nonempty :=
      ⟨Erdos841.t n, Erdos841.t_spec n⟩
    have hmem : sInf {T | ∃ J ⊆ Finset.Icc 1 T, IsSquare (n * ∏ j ∈ J, (n + j))} ∈
        {T | ∃ J ⊆ Finset.Icc 1 T, IsSquare (n * ∏ j ∈ J, (n + j))} := Nat.sInf_mem hne
    exact Erdos841.t_le_of_admissible hmem

theorem SL004.filt_eq (x : ℕ) :
    Erdos841.manySmallUpTo x =
      (Finset.Icc 1 x).filter fun n : ℕ ↦
        ((SL003FC.Erdos841.t n : ℕ) : ℝ) ≤
          exp (20 * Real.sqrt (log n * log (log n))) := by
  ext n
  simp only [Erdos841.manySmallUpTo, Finset.mem_filter, SL004.t_eq]

theorem SL004.bridge_main : SL003FC.Erdos841.SL003.targetProp := by
  refine ⟨20, ?_⟩
  have h := Erdos841.erdos841_many_small_values_global.1
  simp only [SL004.filt_eq] at h
  first
    | exact h
    | (convert h using 4)
