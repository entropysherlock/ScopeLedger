import SL003Target

/-! SL-003 AI attempt 1 (Claude). The cited theorem quantifies over the structure
`Erdos440.IncreasingSequence` and counts edges in `(Finset.range x).filter`; the target quantifies over
`a : ℕ → ℕ` with `StrictMono a` and positivity and counts with `Set.ncard`. The bridge packages `a` as
the structure and shows the two counts agree (an edge with lcm ≤ x has index < x, because
i + 1 ≤ a i ≤ lcm). No human edits. -/

theorem SL003.ai1 : SL003FC.Erdos440.SL003.targetProp := by
  unfold SL003FC.Erdos440.SL003.targetProp
  intro a ha hpos
  let A : Erdos440.IncreasingSequence := ⟨a, hpos, ha⟩
  have key : ∀ x : ℕ, SL003FC.Erdos440.count a x = A.count x := by
    intro x
    show {i | Nat.lcm (a i) (a (i + 1)) ≤ x}.ncard =
      ((Finset.range x).filter fun i => Nat.lcm (a i) (a (i + 1)) ≤ x).card
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_sep_iff, Finset.coe_filter, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · intro h
      refine ⟨?_, h⟩
      have h1 : i + 1 ≤ a i := A.index_succ_le i
      have h2 : a i ≤ Nat.lcm (a i) (a (i + 1)) := A.value_le_edgeLcm_left i
      omega
    · intro h
      exact h.2
  have hfun : (fun x : ℕ ↦ (SL003FC.Erdos440.count a x : ℝ)) = fun x : ℕ ↦ (A.count x : ℝ) := by
    funext x
    rw [key x]
  rw [hfun]
  exact Erdos440.erdos_440.1 A
