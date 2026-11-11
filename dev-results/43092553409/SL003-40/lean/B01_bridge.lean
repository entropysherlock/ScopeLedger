import B00_corr

/-! SL-004 dev, SL003-40 (Erdős 690, 1 ≤ k ≤ 3): FC quantifies over every density function `d`;
the cited theorem fixes one (`primeFactorDensity`) and proves it unimodal for 1 ≤ k ≤ 3. A density
is unique (limits in ℝ are unique), so `d p` equals the cited density at every prime, and
unimodality transfers through the ℚ → ℝ cast. -/

theorem SL004.bridge40 : SL003FC.Erdos690.SL003.targetProp := by
  unfold SL003FC.Erdos690.SL003.targetProp
  intro k hk1 hk3 d hd
  obtain ⟨hden, huni, -⟩ := Erdos690.erdos_690
  have hdeq : ∀ p, Nat.Prime p → d p = (Erdos690.primeFactorDensity k p : ℝ) := by
    intro p hp
    have h1 := hd p hp
    have h2 := hden k p (by omega) hp
    rw [SL004.corr690_kth k p hk1] at h1
    exact tendsto_nhds_unique h1 h2
  obtain ⟨m, hm, hinc, hdec⟩ := huni k hk1 hk3
  unfold SL003FC.Erdos690.IsUnimodalOnPrimes
  refine ⟨m, hm, fun p q hp hq hpq hqm => ?_, fun p q hp hq hmp hpq => ?_⟩
  · rw [hdeq p hp, hdeq q hq]
    exact_mod_cast hinc p q hp hq hpq hqm
  · rw [hdeq p hp, hdeq q hq]
    exact_mod_cast hdec p q hp hq hmp hpq
