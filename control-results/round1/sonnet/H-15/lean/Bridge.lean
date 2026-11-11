import SL003Target

theorem SL004.oe_congr {s t : Finset ℕ} (h : s = t) {k : ℕ} (hk : k < s.card) (hk' : k < t.card) :
    (s.orderEmbOfFin rfl ⟨k, hk⟩ : ℕ) = t.orderEmbOfFin rfl ⟨k, hk'⟩ := by
  subst h
  rfl

theorem SL004.nth_div (n k : ℕ) (hn : n ≠ 0) (hk : k < n.divisors.card) :
    Nat.nth (fun d => d ∣ n) k = (Erdos673.divisorSequence n ⟨k, hk⟩ : ℕ) := by
  have hf : (setOf (fun d => d ∣ n)).Finite := by
    apply (Nat.divisors n).finite_toSet.subset
    intro d hd
    exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨hd, hn⟩)
  have hs : hf.toFinset = n.divisors := by
    ext d
    simp [Set.Finite.mem_toFinset, Nat.mem_divisors, hn]
  have hk' : k < hf.toFinset.card := by rw [hs]; exact hk
  rw [Nat.nth_eq_orderEmbOfFin hf hk']
  exact SL004.oe_congr hs hk' hk

theorem SL004.G_eq (n : ℕ) : SL003FC.Erdos673.G n = Erdos673.G n := by
  unfold SL003FC.Erdos673.G Erdos673.G
  apply Finset.sum_congr rfl
  intro i _
  have hi0 := i.2
  have hi : (i : ℕ) + 1 < n.divisors.card := by omega
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hi
  have h1 := SL004.nth_div n i hn (by omega)
  have h2 := SL004.nth_div n ((i : ℕ) + 1) hn hi
  first
    | (rw [h1, h2])
    | (simp only [h1, h2])
    | (simp [Fin.val_add, h1, h2])

theorem SL004.GSum_eq (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, SL003FC.Erdos673.G n) = Erdos673.GSum X := by
  unfold Erdos673.GSum
  exact Finset.sum_congr rfl (fun n _ => SL004.G_eq n)

theorem SL004.bridge_main : SL003FC.Erdos673.SL003.targetProp := by
  unfold SL003FC.Erdos673.SL003.targetProp
  have h := Erdos673.erdos_673.2.1
  exact h.congr_left (Filter.Eventually.of_forall (fun X => (SL004.GSum_eq X).symm))
