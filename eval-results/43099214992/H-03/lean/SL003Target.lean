import Mathlib
import Proofs.T_Erdos316_erdos_316_variants_generalized

namespace SL003FC

section
namespace Erdos316
end Erdos316

namespace Erdos316

/-- SL-003 transported target: FormalConjectures/ErdosProblems/316.lean `erdos_316.variants.generalized`. -/
def SL003.targetProp : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ A : Finset ℕ,
    A.Nonempty ∧ 0 ∉ A ∧ 1 ∉ A ∧ ∑ k ∈ A, (1 / k : ℚ) < n ∧ ∀ P : Finpartition A,
    P.parts.card ≤ n → ∃ p ∈ P.parts, 1 ≤ ∑ n ∈ p, (1 / n : ℚ)

end Erdos316
end
end SL003FC
