import SL003Target

/-! SL-004 dev, SL003-35 (Erdős 737). Correspondence: the project's `IsUncountablyChromatic G` is
`IsEmpty (G.Coloring ℕ)`; the cited theorem gives an adjacent pair `a r` and cycles through `s(a, r)`
of every large length; FC asks for an edge `e ∈ G.edgeSet` with `CycleThroughEdgeOfLength`. -/

theorem SL004.bridge35 : SL003FC.Erdos737.SL003.targetProp := by
  unfold SL003FC.Erdos737.SL003.targetProp
  intro V G hG
  obtain ⟨a, r, hadj, N, hN⟩ := Erdos737.eventually_cycles_through_fixed_edge (G := G) hG
  refine ⟨s(a, r), by simpa using hadj, N, fun n hn => ?_⟩
  obtain ⟨c, hc, hlen, he⟩ := hN n hn
  unfold SL003FC.Erdos737.CycleThroughEdgeOfLength
  exact ⟨_, c, hc, hlen, he⟩
