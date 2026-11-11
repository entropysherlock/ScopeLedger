import SL003Target

/-! SL-004 dev, SL003-45 (Erdős 1195). Correspondence: FC's `HasSet` and the project's
`HasErdos1195Witness` are twins (same body over twin `countingFunction`, `IntegerRatioFree`). Bridge: the
cited pointwise characterisation gives FC's set equality by extensionality. -/

theorem SL004.corr45_HasSet (F : ℝ → ℝ) : SL003FC.Erdos1195.HasSet F ↔ Erdos1195.HasErdos1195Witness F :=
  Iff.rfl

theorem SL004.bridge45 : SL003FC.Erdos1195.SL003.targetProp := by
  unfold SL003FC.Erdos1195.SL003.targetProp
  ext F
  simp only [Set.mem_setOf_eq, SL003FC.Erdos1195.erdos_1195.answer]
  constructor
  · rintro ⟨hG, hS⟩
    have hG' := hG
    obtain ⟨h1, h2, h3⟩ := hG'
    exact ⟨hG, (Erdos1195.erdos_1195 F h1 h2 h3).1 ((SL004.corr45_HasSet F).1 hS)⟩
  · rintro ⟨hG, hI⟩
    have hG' := hG
    obtain ⟨h1, h2, h3⟩ := hG'
    exact ⟨hG, (SL004.corr45_HasSet F).2 ((Erdos1195.erdos_1195 F h1 h2 h3).2 hI)⟩
