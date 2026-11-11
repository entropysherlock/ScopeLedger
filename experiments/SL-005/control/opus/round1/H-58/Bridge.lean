import SL003Target

/-! Bridge for H-58 (Erdős 274, abelian variant): from `Erdos274.erdos_274.variants.abelian`.

The transported `Group.ExactCovering` structure is a field-by-field copy of the cited one, so a
transported exact covering is repackaged with the same fields. -/

universe u v

theorem SL004.bridge_main : SL003FC.Erdos274.SL003.targetProp.{u, v} := by
  unfold SL003FC.Erdos274.SL003.targetProp
  intro G _ _ hG ι _ P hι
  exact Erdos274.erdos_274.variants.abelian hG
    (⟨P.parts, P.reps, P.nonempty, P.disjoint, P.covers⟩ : Group.ExactCovering G ι) hι
