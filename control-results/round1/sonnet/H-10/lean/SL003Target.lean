import Mathlib
import ErdosProblems.Erdos534

namespace SL003FC

section
namespace Erdos534
/-- A set `A ⊆ {1, …, N}` is *admissible* if it contains `N` and any two distinct elements
of `A` have a common factor. -/
def IsAdmissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ N ∈ A ∧ (A : Set ℕ).Pairwise fun a b ↦ 1 < Nat.gcd a b
/-- The largest size of an admissible subset of `{1, …, N}`. -/
noncomputable def maxCard (N : ℕ) : ℕ :=
  sSup {n | ∃ A : Finset ℕ, IsAdmissible N A ∧ A.card = n}
/-- The prime factors `q₁ < ⋯ < qⱼ` of `N` which are at most `q`. -/
def primePrefix (N q : ℕ) : Finset ℕ := N.primeFactors.filter (· ≤ q)
/-- The Ahlswede–Khachatrian set associated to a prime factor `q` of `N`: those integers in
`[1, N]` which are a multiple of at least one of `2 q₁, …, 2 qⱼ, q₁ ⋯ qⱼ`, where
`q₁ < ⋯ < qⱼ = q` are the prime factors of `N` which are at most `q`. -/
def ahlswedeKhachatrian (N q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m ↦
    (∏ p ∈ primePrefix N q, p) ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m
end Erdos534

namespace Erdos534

/-- SL-003 transported target: FormalConjectures/ErdosProblems/534.lean `erdos_534`. -/
def SL003.targetProp : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N), ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card

end Erdos534
end
end SL003FC
