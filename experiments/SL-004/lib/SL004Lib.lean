import Mathlib

/-!
# SL-004 correspondence library

Characterisation lemmas for extremal quantities. Formal Conjectures usually states an extremal
function as `sSup`/`sInf` of a set; independent proofs usually compute it (`Nat.find`,
`Nat.findGreatest`, `Finset.sup`). The transport principle used throughout SL-004 is:

  if the project's value is the least (greatest) element of FC's set, then FC's `sInf` (`sSup`)
  equals it (`IsLeast.csInf_eq`, `IsGreatest.csSup_eq`),

which needs no knowledge of how either side is computed. The lemmas below give the characterisation
for the common computable representations. Mathlib only, written to compile across the Mathlib
versions pinned by the audited projects.
-/

namespace SL004Lib

/-- `Nat.find h` is the least element of `{n | P n}`. -/
theorem isLeast_find (P : ℕ → Prop) [DecidablePred P] (h : ∃ n, P n) :
    IsLeast {n | P n} (Nat.find h) :=
  ⟨Nat.find_spec h, fun _ hm => Nat.find_min' h hm⟩

/-- `Nat.findGreatest P n` is the greatest element of `{k | P k}` when `P` is bounded by `n` and
satisfied somewhere. -/
theorem isGreatest_findGreatest (P : ℕ → Prop) [DecidablePred P] (n : ℕ)
    (hb : ∀ k, P k → k ≤ n) (hex : ∃ k, P k) :
    IsGreatest {k | P k} (Nat.findGreatest P n) := by
  obtain ⟨k, hk⟩ := hex
  exact ⟨Nat.findGreatest_spec (hb k hk) hk, fun m hm => Nat.le_findGreatest (hb m hm) hm⟩

/-- `s.sup f` is the greatest value of `f` on a nonempty finite family, as a set of naturals. -/
theorem isGreatest_finset_sup {β : Type*} (s : Finset β) (P : β → Prop) (f : β → ℕ)
    (hP : ∀ b, P b ↔ b ∈ s) (hne : s.Nonempty) :
    IsGreatest {k | ∃ b, P b ∧ f b = k} (s.sup f) := by
  obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_sup s hne f
  refine ⟨⟨b, (hP b).2 hb, hbeq.symm⟩, ?_⟩
  rintro k ⟨c, hc, rfl⟩
  exact Finset.le_sup ((hP c).1 hc)

end SL004Lib
