import SL003Target

/-! SL-004 dev, SL003-43: the twin-structure principle. The project re-declares FC's `structure EdgeN`
field for field. A weight function on FC's edges is pulled back along the field-copying map
`ψ : EdgeN → SL003FC…EdgeN`; the remaining definitions are twins, so FC's equation system for `W`
is definitionally the project's for `W ∘ ψ`. -/

def SL004.psi43 {N D : ℕ} (e : MonochromaticQuantumGraph.EdgeN N D) : SL003FC.MonochromaticQuantumGraph.EdgeN N D :=
  ⟨e.u, e.v, e.i, e.j⟩

theorem SL004.corr43_eqSystem (W : SL003FC.MonochromaticQuantumGraph.WeightsN 8 3 ℤ) :
    SL003FC.MonochromaticQuantumGraph.EqSystemN 8 3 W →
      MonochromaticQuantumGraph.EqSystemN 8 3 (fun e => W (SL004.psi43 e)) := by
  intro h ι
  have := h ι
  with_unfolding_all exact this

theorem SL004.bridge43 : SL003FC.MonochromaticQuantumGraph.SL003.targetProp := by
  unfold SL003FC.MonochromaticQuantumGraph.SL003.targetProp
  rintro ⟨W, hW, hE⟩
  apply (QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_trinary_int).mp trivial
  exact ⟨fun e => W (SL004.psi43 e), fun e => hW _, SL004.corr43_eqSystem W hE⟩
