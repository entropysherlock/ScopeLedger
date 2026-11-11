import Mathlib
import ErdosProblems.Erdos841.Core

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

/-- SL-003 transported target: FormalConjectures/ErdosProblems/841.lean `erdos_841.variants.many_small_values`. -/
def SL003.targetProp : Prop :=
  ∃ K : ℝ,
    Tendsto (fun x : ℕ ↦
      log (((Finset.Icc 1 x).filter fun n ↦
        (t n : ℝ) ≤ exp (K * √(log n * log (log n)))).card : ℝ) / log x) atTop (𝓝 1)

end Erdos841
end
end SL003FC
