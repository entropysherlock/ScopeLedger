import SL003Target

/-! Bridge for H-15 (Erdős 673, part ii): from `Erdos673.erdos_673` to the transported target. -/

namespace SL004.H15

theorem orderEmbOfFin_congr (s t : Finset ℕ) (h : s = t) (j : ℕ) (h1 : j < s.card)
    (h2 : j < t.card) :
    s.orderEmbOfFin rfl ⟨j, h1⟩ = t.orderEmbOfFin rfl ⟨j, h2⟩ := by
  subst h
  rfl

theorem nth_eq (n : ℕ) (hn : 0 < n) (j : ℕ) (hj : j < n.divisors.card) :
    Nat.nth (· ∣ n) j = (Erdos673.divisorSequence n ⟨j, hj⟩ : ℕ) := by
  have hf : {d : ℕ | d ∣ n}.Finite :=
    n.divisors.finite_toSet.subset (fun d hd => Nat.mem_divisors.2 ⟨hd, hn.ne'⟩)
  have hs : hf.toFinset = n.divisors := by
    ext d
    simp [Nat.mem_divisors, hn.ne']
  have hj' : j < hf.toFinset.card := by
    rw [hs]
    exact hj
  rw [Nat.nth_eq_orderEmbOfFin hf hj']
  exact orderEmbOfFin_congr _ _ hs j hj' hj

theorem G_eq (n : ℕ) (hn : 0 < n) : SL003FC.Erdos673.G n = Erdos673.G n := by
  unfold SL003FC.Erdos673.G Erdos673.G
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hi := i.isLt
  rw [nth_eq n hn i (by omega), nth_eq n hn (i + 1) (by omega)]

end SL004.H15

theorem SL004.bridge_main : SL003FC.Erdos673.SL003.targetProp := by
  unfold SL003FC.Erdos673.SL003.targetProp
  have hfun : (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X, SL003FC.Erdos673.G n) =
      fun X : ℕ => Erdos673.GSum X := by
    funext X
    unfold Erdos673.GSum
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have h1 := (Finset.mem_Icc.1 hn).1
    exact SL004.H15.G_eq n (by omega)
  rw [hfun]
  exact Erdos673.erdos_673.2.1
