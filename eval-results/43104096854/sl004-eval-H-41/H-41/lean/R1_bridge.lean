import SL003Target

/-! SL-004 Layer B round 1 (Claude), H-41 (monochromatic quantum graphs, N = 8). Class T2: the
project re-declares `structure EdgeN`; FC's weights pull back along the field-copying map and the
equation systems are twins (pattern certified on dev cases SL003-14/43). -/

def SL004.psiH41 {N D : ℕ} (e : MonochromaticQuantumGraph.EdgeN N D) :
    SL003FC.MonochromaticQuantumGraph.EdgeN N D :=
  ⟨e.u, e.v, e.i, e.j⟩

theorem SL004.corrH41 (W : SL003FC.MonochromaticQuantumGraph.WeightsN 8 3 ℤ) :
    SL003FC.MonochromaticQuantumGraph.EqSystemN 8 3 W →
      MonochromaticQuantumGraph.EqSystemN 8 3 (fun e => W (SL004.psiH41 e)) := by
  intro h ι
  have := h ι
  with_unfolding_all exact this

theorem SL004.bridgeH41 : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  rintro ⟨W, hE⟩
  apply (QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_int).mp trivial
  exact ⟨fun e => W (SL004.psiH41 e), SL004.corrH41 W hE⟩
