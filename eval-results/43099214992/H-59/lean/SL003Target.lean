import Mathlib
import ErdosProblems.Erdos499

namespace SL003FC

section
open Nat
namespace Erdos499
end Erdos499

/-- SL-003 transported target: FormalConjectures/ErdosProblems/499.lean `erdos_499`. -/
def SL003.targetProp : Prop :=
  (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      n ^ (- n : ℤ) ≤ ∏ i, M i (σ i))

end
end SL003FC
