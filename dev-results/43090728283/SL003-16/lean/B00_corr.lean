import SL003Target

/-! SL-004 dev, Erdős 690: FC's `kthPrimeFactorSet` requires `0 < n`, the project's requires `0 < k`.
For `k ≥ 1` they are the same set, because `p ∈ n.primeFactors` forces `0 < n`. -/

theorem SL004.corr690_kth (k p : ℕ) (hk : 1 ≤ k) :
    SL003FC.Erdos690.kthPrimeFactorSet k p = Erdos690.kthPrimeFactorSet k p := by
  ext n
  simp only [SL003FC.Erdos690.kthPrimeFactorSet, Erdos690.kthPrimeFactorSet,
    Erdos690.IsKthSmallestPrimeFactor, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hp, hc⟩
    exact ⟨by omega, hp, hc⟩
  · rintro ⟨-, hp, hc⟩
    exact ⟨Nat.pos_of_mem_primeFactors hp, hp, hc⟩
