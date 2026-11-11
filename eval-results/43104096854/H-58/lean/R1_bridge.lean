import SL003Target

/-! SL-004 Layer B round 1 (Claude), H-58 (Erdős 274, abelian case). Class T2: the project
re-declares `Group.ExactCovering` field for field; an FC covering is rebuilt as the project's by
copying its fields, and the conclusion concerns the same subgroups. -/

theorem SL004.bridgeH58 : SL003FC.Erdos274.SL003.targetProp := by
  unfold SL003FC.Erdos274.SL003.targetProp
  intro G _ _ hG ι _ P hι
  exact Erdos274.erdos_274.variants.abelian hG ⟨P.parts, P.reps, P.nonempty, P.disjoint, P.covers⟩ hι
