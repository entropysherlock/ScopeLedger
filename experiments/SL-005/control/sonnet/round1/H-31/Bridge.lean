import SL003Target

theorem SL004.is45_iff {n k : ℕ} (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) :
    SL003FC.Erdos136.Is45Coloring C ↔ Erdos136.Is45Coloring C := by
  unfold SL003FC.Erdos136.Is45Coloring Erdos136.Is45Coloring
  apply forall_congr'
  intro v
  first
    | exact Iff.rfl
    | (convert Iff.rfl)

theorem SL004.col_iff (n k : ℕ) :
    SL003FC.Erdos136.Colorable n k ↔ Erdos136.Colorable n k := by
  unfold SL003FC.Erdos136.Colorable Erdos136.Colorable
  exact exists_congr fun C => SL004.is45_iff C

theorem SL004.f_eq (n : ℕ) : SL003FC.Erdos136.f n = Erdos136.erdos136Fun n := by
  unfold SL003FC.Erdos136.f
  apply le_antisymm
  · exact Nat.sInf_le ((SL004.col_iff _ _).mpr (Erdos136.erdos136Fun_spec n))
  · have hne : {k | SL003FC.Erdos136.Colorable n k}.Nonempty :=
      ⟨Erdos136.erdos136Fun n, (SL004.col_iff _ _).mpr (Erdos136.erdos136Fun_spec n)⟩
    exact Erdos136.erdos136Fun_min ((SL004.col_iff _ _).mp (Nat.sInf_mem hne))

theorem SL004.bridge_main : SL003FC.Erdos136.SL003.targetProp := by
  unfold SL003FC.Erdos136.SL003.targetProp
  refine Filter.Tendsto.congr (fun n => ?_) Erdos136.erdos_136
  rw [SL004.f_eq n]
