import B00_corr

/-! SL-004 dev, SL003-16 (Erdős 690): FC refutes "for every k ≥ 1, every density function of the
k-th-smallest-prime-factor sets is unimodal". The cited theorem gives the densities (as rationals)
and non-unimodality for 4 ≤ k ≤ 20. The bridge takes k = 4, casts the densities to ℝ, and moves
unimodality back to ℚ (`Rat.cast_le`). -/

theorem SL004.bridge16 : SL003FC.Erdos690.SL003.targetProp := by
  unfold SL003FC.Erdos690.SL003.targetProp
  intro H
  obtain ⟨hden, -, hnot⟩ := Erdos690.erdos_690
  have hU := H 4 (by norm_num) (fun p => (Erdos690.primeFactorDensity 4 p : ℝ)) (fun p hp => by
    rw [SL004.corr690_kth 4 p (by norm_num)]
    exact hden 4 p (by norm_num) hp)
  apply hnot 4 (by norm_num) (by norm_num)
  unfold SL003FC.Erdos690.IsUnimodalOnPrimes at hU
  obtain ⟨m, hm, hinc, hdec⟩ := hU
  unfold Erdos690.DensityUnimodal Erdos690.UnimodalOnPrimes
  exact ⟨m, hm, fun p q hp hq h1 h2 => by exact_mod_cast hinc p q hp hq h1 h2,
    fun p q hp hq h1 h2 => by exact_mod_cast hdec p q hp hq h1 h2⟩
