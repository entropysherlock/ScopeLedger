import Mathlib
import ErdosProblems.Erdos441

namespace SL003FC

section
open Filter Asymptotics
namespace Erdos441
/--
`g N` is the size of the largest `A ⊆ {1, …, N}` such that `lcm(a, b) ≤ N` for all `a, b ∈ A`.
-/
noncomputable def g (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k}
/--
Erdős' construction: all integers in $[1,(N/2)^{1/2}]$ together with all even integers in
$[(N/2)^{1/2},(2N)^{1/2}]$.
-/
def erdosConstruction (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a ↦ 2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)
end Erdos441

namespace Erdos441

/-- SL-003 transported target: FormalConjectures/ErdosProblems/441.lean `erdos_441`. -/
def SL003.targetProp : Prop :=
  ¬ ∀ N : ℕ, 1 ≤ N → g N = (erdosConstruction N).card

end Erdos441
end
end SL003FC
