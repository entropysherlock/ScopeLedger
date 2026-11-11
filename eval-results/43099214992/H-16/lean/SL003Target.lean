import Mathlib
import ErdosProblems.Erdos877

namespace SL003FC

section
open Filter Asymptotics Real
namespace Erdos877
/-- `A` is a maximal sum-free subset of `{1, …, n}`. -/
def IsMaximalSumFree (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ IsSumFree (A : Set ℕ) ∧
    ∀ B ⊆ Finset.Icc 1 n, IsSumFree (B : Set ℕ) → A ⊆ B → A = B
open scoped Classical in
/-- `fm n` counts the number of maximal sum-free subsets $A\subseteq\{1,\ldots,n\}$. -/
noncomputable def fm (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsMaximalSumFree n A).card
end Erdos877

namespace Erdos877

/-- SL-003 transported target: FormalConjectures/ErdosProblems/877.lean `erdos_877.variants.luczak_schoen`. -/
def SL003.targetProp : Prop :=
  ∃ c : ℝ, c < 1 / 2 ∧ ∀ᶠ n : ℕ in atTop, (fm n : ℝ) ≤ 2 ^ (c * n)

end Erdos877
end
end SL003FC
