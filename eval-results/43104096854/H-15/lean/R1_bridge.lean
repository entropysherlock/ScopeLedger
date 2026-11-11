import SL003Target

/-! SL-004 Layer B round 1 (Claude), H-15 (Erdős 673). Class C4 enumeration change: FC indexes the
divisors with `Nat.nth (· ∣ n)`, the project with `n.divisors.orderEmbOfFin`; Mathlib's
`Nat.nth_eq_orderEmbOfFin` relates them once the finite set `{d | d ∣ n}` is identified with
`n.divisors` (n ≠ 0). Then the two `G` agree on `[1, X]` and the cited asymptotic transfers. -/

theorem SL004.auxH15 {s t : Finset ℕ} (hst : s = t) (j : ℕ) (h1 : j < s.card) (h2 : j < t.card) :
    s.orderEmbOfFin rfl ⟨j, h1⟩ = t.orderEmbOfFin rfl ⟨j, h2⟩ := by
  subst hst
  rfl

theorem SL004.corrH15_nth (n : ℕ) (hn : n ≠ 0) (j : ℕ) (hj : j < n.divisors.card) :
    Nat.nth (· ∣ n) j = Erdos673.divisorSequence n ⟨j, hj⟩ := by
  have hf : (setOf (· ∣ n)).Finite := by
    apply (n.divisors.finite_toSet).subset
    intro d hd
    simp only [Set.mem_setOf_eq] at hd
    simpa [Nat.mem_divisors, hn] using hd
  have heq : hf.toFinset = n.divisors := by
    ext d
    simp [Nat.mem_divisors, hn]
  have hj' : j < hf.toFinset.card := by
    rw [heq]
    exact hj
  rw [Nat.nth_eq_orderEmbOfFin hf hj']
  unfold Erdos673.divisorSequence
  exact SL004.auxH15 heq j hj' hj

theorem SL004.corrH15_G (n : ℕ) (hn : n ≠ 0) : SL003FC.Erdos673.G n = Erdos673.G n := by
  unfold SL003FC.Erdos673.G Erdos673.G
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  rw [SL004.corrH15_nth n hn i (by omega), SL004.corrH15_nth n hn (i + 1) (by omega)]

theorem SL004.bridgeH15 : SL003FC.Erdos673.SL003.targetProp := by
  unfold SL003FC.Erdos673.SL003.targetProp
  have h := Erdos673.erdos_673.2.1
  have hfun : (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X, SL003FC.Erdos673.G n) = fun X => Erdos673.GSum X := by
    funext X
    unfold Erdos673.GSum
    refine Finset.sum_congr rfl fun n hn => ?_
    exact SL004.corrH15_G n (by simp at hn; omega)
  rw [hfun]
  exact h
