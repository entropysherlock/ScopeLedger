import Mathlib
import ErdosProblems.Erdos780

namespace SL003FC

section
namespace Erdos780
end Erdos780

namespace Erdos780

/-- SL-003 transported target: FormalConjectures/ErdosProblems/780.lean `erdos_780`. -/
def SL003.targetProp : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

end Erdos780
end
end SL003FC
