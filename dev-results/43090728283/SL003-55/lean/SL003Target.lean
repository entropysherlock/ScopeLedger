import Mathlib
import ErdosProblems.Erdos841.LowerBound

namespace SL003FC

section
open Filter Real Topology
namespace Erdos841
/-- `t n` is the least `T` such that `{n + 1, …, n + T}` contains a subset whose product with `n`
is a square; `t n = 0` if and only if `n` is itself a square. -/
noncomputable def t (n : ℕ) : ℕ :=
  sInf {T | ∃ J ⊆ Finset.Icc 1 T, IsSquare (n * ∏ j ∈ J, (n + j))}
end Erdos841

namespace Erdos841

/-- SL-003 transported target: FormalConjectures/ErdosProblems/841.lean `erdos_841.variants.lower_bound`. -/
def SL003.targetProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, ¬ IsSquare n →
      C * (log (log n) ^ ((6 : ℝ) / 5) * log (log (log n)) ^ (-(1 : ℝ) / 5)) ≤ t n

end Erdos841
end
end SL003FC
