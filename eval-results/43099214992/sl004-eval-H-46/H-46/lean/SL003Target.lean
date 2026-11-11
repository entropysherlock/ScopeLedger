import Mathlib
import Erdos548

namespace SL003FC

section
open SimpleGraph
namespace Erdos548
end Erdos548

namespace Erdos548

/-- SL-003 transported target: FormalConjectures/ErdosProblems/548.lean `erdos_548`. -/
def SL003.targetProp : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n))
    (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

end Erdos548
end
end SL003FC
