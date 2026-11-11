import SL003Target

universe u v

theorem SL004.bridge_main : SL003FC.Erdos274.SL003.targetProp.{u, v} := by
  intro G _ _ hG ι _ P hι
  exact Erdos274.erdos_274.variants.abelian hG
    ({ parts := P.parts, reps := P.reps, nonempty := P.nonempty,
       disjoint := P.disjoint, covers := P.covers } : Group.ExactCovering G ι) hι
