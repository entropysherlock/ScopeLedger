import SL003Target

theorem SL004.vertices_eq (N : ℕ) :
    MonochromaticQuantumGraph.vertices N = SL003FC.MonochromaticQuantumGraph.vertices N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [MonochromaticQuantumGraph.vertices, SL003FC.MonochromaticQuantumGraph.vertices, ih]

theorem SL004.allEqual_iff {N D : ℕ} (ι : Fin N → Fin D) :
    MonochromaticQuantumGraph.allEqual ι ↔ SL003FC.MonochromaticQuantumGraph.allEqual ι := by
  unfold MonochromaticQuantumGraph.allEqual SL003FC.MonochromaticQuantumGraph.allEqual
    MonochromaticQuantumGraph.allEqualList SL003FC.MonochromaticQuantumGraph.allEqualList
  rw [SL004.vertices_eq]

theorem SL004.pm_aux {α : Type} [Semiring α] {N D : ℕ}
    (W' : MonochromaticQuantumGraph.WeightsN N D α)
    (W : SL003FC.MonochromaticQuantumGraph.WeightsN N D α)
    (hW : ∀ e : SL003FC.MonochromaticQuantumGraph.EdgeN N D, W' ⟨e.u, e.v, e.i, e.j⟩ = W e)
    (ι : Fin N → Fin D) (n : ℕ) :
    (∀ L, MonochromaticQuantumGraph.pmSumListAux W' ι n L =
        SL003FC.MonochromaticQuantumGraph.pmSumListAux W ι n L) ∧
    (∀ L, MonochromaticQuantumGraph.pmSumListAux W' ι (n + 1) L =
        SL003FC.MonochromaticQuantumGraph.pmSumListAux W ι (n + 1) L) := by
  induction n with
  | zero =>
    refine ⟨fun L => ?_, fun L => ?_⟩
    · first
        | rfl
        | simp [MonochromaticQuantumGraph.pmSumListAux,
            SL003FC.MonochromaticQuantumGraph.pmSumListAux]
    · first
        | rfl
        | simp [MonochromaticQuantumGraph.pmSumListAux,
            SL003FC.MonochromaticQuantumGraph.pmSumListAux]
  | succ n ih =>
    refine ⟨ih.2, fun L => ?_⟩
    cases L with
    | nil =>
      first
        | rfl
        | simp [MonochromaticQuantumGraph.pmSumListAux,
            SL003FC.MonochromaticQuantumGraph.pmSumListAux]
    | cons v vs =>
      simp only [MonochromaticQuantumGraph.pmSumListAux,
        SL003FC.MonochromaticQuantumGraph.pmSumListAux]
      congr 1
      apply List.map_congr_left
      intro u _
      rw [ih.1 (vs.erase u)]
      congr 1
      exact hW (SL003FC.MonochromaticQuantumGraph.mkEdge v u (ι v) (ι u))

theorem SL004.pm_conv {N D : ℕ} (W : SL003FC.MonochromaticQuantumGraph.WeightsN N D ℤ)
    (ι : Fin N → Fin D) (n : ℕ) (L : List (Fin N)) :
    MonochromaticQuantumGraph.pmSumListAux
        (fun e : MonochromaticQuantumGraph.EdgeN N D => W ⟨e.u, e.v, e.i, e.j⟩) ι n L =
      SL003FC.MonochromaticQuantumGraph.pmSumListAux W ι n L :=
  (SL004.pm_aux (fun e : MonochromaticQuantumGraph.EdgeN N D => W ⟨e.u, e.v, e.i, e.j⟩) W
    (fun e => rfl) ι n).1 L

theorem SL004.bridge_main : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  have h := (QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_int).mp trivial
  rintro ⟨W, hW⟩
  apply h
  refine ⟨fun e => W ⟨e.u, e.v, e.i, e.j⟩, ?_⟩
  intro ι
  have h1 := hW ι
  have e1 : MonochromaticQuantumGraph.pmSumN 8 3
      (fun e : MonochromaticQuantumGraph.EdgeN 8 3 => W ⟨e.u, e.v, e.i, e.j⟩) ι =
      SL003FC.MonochromaticQuantumGraph.pmSumN 8 3 W ι := by
    unfold MonochromaticQuantumGraph.pmSumN MonochromaticQuantumGraph.pmSumList
      SL003FC.MonochromaticQuantumGraph.pmSumN SL003FC.MonochromaticQuantumGraph.pmSumList
    rw [SL004.vertices_eq]
    exact SL004.pm_conv W ι _ _
  have e2 := SL004.allEqual_iff ι
  rw [e1, h1]
  exact if_congr e2.symm rfl rfl
