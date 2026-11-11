import Mathlib
import ErdosProblems.Erdos1096

namespace SL003FC

section
open Filter
open scoped Topology
namespace Erdos1096
end Erdos1096

namespace Erdos1096

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1096.lean `erdos_1096`. -/
def SL003.targetProp : Prop :=
  ∃ ε > 0, ∀ q, 1 < q → q < 1 + ε →
    ∀ x : ℕ → ℝ, StrictMono x → Set.range x = { ∑ i ∈ S, q ^ i | S : Finset ℕ } →
    Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0)

end Erdos1096
end
end SL003FC
