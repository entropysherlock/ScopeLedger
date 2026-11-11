import SL003Target

/-! Bridge for H-41 (monochromatic quantum graphs, `N = 8`, `D = 3`, over `ℤ`): from
`QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_int`.

The transported definitions are a verbatim copy, in namespace `SL003FC`, of the Formal Conjectures
definitions used by the cited theorem.  The only type that differs is the edge structure `EdgeN`,
so a transported weight function is turned into a cited one by repackaging edges, and the
perfect-matching sums and the `allEqual` predicate are shown to agree. -/

namespace SL004.H41

/-- Repackage a transported weight function as a cited weight function. -/
def conv {N D : ℕ} (W : SL003FC.MonochromaticQuantumGraph.WeightsN N D ℤ) :
    MonochromaticQuantumGraph.WeightsN N D ℤ :=
  fun e => W (SL003FC.MonochromaticQuantumGraph.EdgeN.mk e.u e.v e.i e.j)

theorem vertices_eq : ∀ N : ℕ,
    MonochromaticQuantumGraph.vertices N = SL003FC.MonochromaticQuantumGraph.vertices N
  | 0 => rfl
  | N + 1 => by
      show (0 : Fin (N + 1)) :: (MonochromaticQuantumGraph.vertices N).map Fin.succ =
        (0 : Fin (N + 1)) :: (SL003FC.MonochromaticQuantumGraph.vertices N).map Fin.succ
      rw [vertices_eq N]

theorem pmSumListAux_eq {N D : ℕ} (W : SL003FC.MonochromaticQuantumGraph.WeightsN N D ℤ)
    (ι : Fin N → Fin D) : ∀ (n : ℕ) (L : List (Fin N)),
      MonochromaticQuantumGraph.pmSumListAux (conv W) ι n L =
        SL003FC.MonochromaticQuantumGraph.pmSumListAux W ι n L
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, [] => rfl
  | _ + 2, [_] => rfl
  | n + 2, v :: w :: vs => by
      have hA : MonochromaticQuantumGraph.pmSumListAux (conv W) ι (n + 2) (v :: w :: vs) =
          ((w :: vs).map (fun u =>
            conv W (MonochromaticQuantumGraph.mkEdge v u (ι v) (ι u)) *
              MonochromaticQuantumGraph.pmSumListAux (conv W) ι n ((w :: vs).erase u))).sum :=
        rfl
      have hB : SL003FC.MonochromaticQuantumGraph.pmSumListAux W ι (n + 2) (v :: w :: vs) =
          ((w :: vs).map (fun u =>
            W (SL003FC.MonochromaticQuantumGraph.mkEdge v u (ι v) (ι u)) *
              SL003FC.MonochromaticQuantumGraph.pmSumListAux W ι n ((w :: vs).erase u))).sum :=
        rfl
      rw [hA, hB]
      exact congrArg List.sum (List.map_congr_left (fun u _ =>
        congrArg (fun t => conv W (MonochromaticQuantumGraph.mkEdge v u (ι v) (ι u)) * t)
          (pmSumListAux_eq W ι n ((w :: vs).erase u))))

theorem pmSumN_eq {N D : ℕ} (W : SL003FC.MonochromaticQuantumGraph.WeightsN N D ℤ)
    (ι : Fin N → Fin D) :
    MonochromaticQuantumGraph.pmSumN N D (conv W) ι =
      SL003FC.MonochromaticQuantumGraph.pmSumN N D W ι := by
  show MonochromaticQuantumGraph.pmSumListAux (conv W) ι
      (MonochromaticQuantumGraph.vertices N).length (MonochromaticQuantumGraph.vertices N) =
    SL003FC.MonochromaticQuantumGraph.pmSumListAux W ι
      (SL003FC.MonochromaticQuantumGraph.vertices N).length
      (SL003FC.MonochromaticQuantumGraph.vertices N)
  rw [vertices_eq N]
  exact pmSumListAux_eq W ι _ _

theorem allEqual_iff {N D : ℕ} (ι : Fin N → Fin D) :
    MonochromaticQuantumGraph.allEqual ι ↔ SL003FC.MonochromaticQuantumGraph.allEqual ι := by
  unfold MonochromaticQuantumGraph.allEqual MonochromaticQuantumGraph.allEqualList
    SL003FC.MonochromaticQuantumGraph.allEqual SL003FC.MonochromaticQuantumGraph.allEqualList
  rw [vertices_eq N]

end SL004.H41

theorem SL004.bridge_main : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  rintro ⟨W, hW⟩
  apply QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_int.1 trivial
  refine ⟨SL004.H41.conv W, ?_⟩
  intro ι
  rw [SL004.H41.pmSumN_eq W ι, hW ι]
  by_cases h : SL003FC.MonochromaticQuantumGraph.allEqual ι
  · rw [if_pos h, if_pos ((SL004.H41.allEqual_iff ι).2 h)]
  · rw [if_neg h, if_neg (fun h' => h ((SL004.H41.allEqual_iff ι).1 h'))]
