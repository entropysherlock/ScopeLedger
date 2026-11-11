import Mathlib
import ErdosProblems.Erdos763

namespace SL003FC

section
open Filter Asymptotics AdditiveCombinatorics
namespace Erdos763
end Erdos763

namespace Erdos763

/-- SL-003 transported target: FormalConjectures/ErdosProblems/763.lean `erdos_763`. -/
def SL003.targetProp : Prop :=
  ¬ ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧
    (fun N : ℕ ↦ (∑ n ∈ Finset.range (N + 1), sumRep A n : ℝ) - c * N) =O[atTop]
      fun _ ↦ (1 : ℝ)

end Erdos763
end
end SL003FC
