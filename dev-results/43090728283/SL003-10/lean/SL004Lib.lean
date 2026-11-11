import Mathlib

/-!
# SL-004 correspondence library

Representation-change lemmas for extremal quantities. Formal Conjectures usually states an extremal
function as `sSup`/`sInf` of a set; independent proofs usually compute it (`Finset.sup` over a finite
family, `Nat.findGreatest`, `Nat.find`, `Finset.card` of a filter). Each lemma turns one
representation into the other under the side conditions that make them agree. They depend on Mathlib
only, and are compiled inside each cited project's own environment.
-/

namespace SL004Lib

/-- A supremum over the values of `f` on a finite nonempty family is that family's `Finset.sup`. -/
theorem sSup_eq_finset_sup {β : Type*} (s : Finset β) (P : β → Prop) (f : β → ℕ)
    (hP : ∀ b, P b ↔ b ∈ s) (hne : s.Nonempty) :
    sSup {k | ∃ b, P b ∧ f b = k} = s.sup f := by
  have hbdd : BddAbove {k | ∃ b, P b ∧ f b = k} := by
    refine ⟨s.sup f, ?_⟩
    rintro k ⟨b, hb, rfl⟩
    exact Finset.le_sup ((hP b).1 hb)
  obtain ⟨b₀, hb₀⟩ := hne
  apply le_antisymm
  · apply csSup_le ⟨f b₀, b₀, (hP b₀).2 hb₀, rfl⟩
    rintro k ⟨b, hb, rfl⟩
    exact Finset.le_sup ((hP b).1 hb)
  · obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_sup s ⟨b₀, hb₀⟩ f
    rw [hbeq]
    exact le_csSup hbdd ⟨b, (hP b).2 hb, rfl⟩

/-- A supremum of a predicate bounded by `n` is `Nat.findGreatest`. -/
theorem sSup_eq_findGreatest (P : ℕ → Prop) [DecidablePred P] (n : ℕ) (hb : ∀ k, P k → k ≤ n) :
    sSup {k | P k} = Nat.findGreatest P n := by
  by_cases hex : ∃ k, P k
  · obtain ⟨k, hk⟩ := hex
    have hbdd : BddAbove {k | P k} := ⟨n, fun m hm => hb m hm⟩
    apply le_antisymm
    · apply csSup_le ⟨k, hk⟩
      intro m hm
      exact Nat.le_findGreatest (hb m hm) hm
    · exact le_csSup hbdd (Nat.findGreatest_spec (m := k) (hb k hk) hk)
  · have hempty : {k | P k} = (∅ : Set ℕ) := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hm => hex ⟨m, hm⟩
    rw [hempty, Nat.sSup_empty, eq_comm, Nat.findGreatest_eq_zero_iff]
    intro m _ _ hm
    exact hex ⟨m, hm⟩

/-- An infimum of a satisfiable predicate on `ℕ` is `Nat.find`. -/
theorem sInf_eq_find (P : ℕ → Prop) [DecidablePred P] (h : ∃ n, P n) :
    sInf {n | P n} = Nat.find h :=
  Nat.sInf_def h

/-- Counting by `Set.ncard` equals counting the filtered range, when the predicate forces `i < n`. -/
theorem ncard_eq_card_filter (P : ℕ → Prop) [DecidablePred P] (n : ℕ) (h : ∀ i, P i → i < n) :
    {i | P i}.ncard = ((Finset.range n).filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_sep_iff, Finset.coe_filter, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨fun hi => ⟨h i hi, hi⟩, fun hi => hi.2⟩

end SL004Lib
