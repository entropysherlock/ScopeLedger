import Mathlib
import FormalConjectures.ErdosProblems.«987»

namespace SL003FC

section
open Filter Finset Asymptotics
open scoped ExponentialSum
namespace Erdos987
/--
For an infinite sequence $x_1, x_2, \ldots \in (0, 1)$, define
$$A_k = \limsup_{n \to \infty} \left\lvert \sum_{j \le n} e(k x_j) \right\rvert,$$
where $e(x) = e^{2\pi i x}$.
-/
noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)
end Erdos987

namespace Erdos987

/-- SL-003 transported target: FormalConjectures/ErdosProblems/987.lean `erdos_987.variants.sup_limsup_infty`. -/
def SL003.targetProp : Prop :=
  ∀ (x : ℕ → ℝ) (hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1), atTop.limsup (fun k : ℕ =>
      ⨆ n : ℕ, ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)) = ⊤

end Erdos987
end
end SL003FC
