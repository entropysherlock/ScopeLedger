import Mathlib
import ErdosProblems.Erdos673

namespace SL003FC

section
open Filter Asymptotics Real
namespace Erdos673
/-- If $1=d_1<\cdots <d_{\tau(n)}=n$ are the divisors of $n$ (here `Nat.nth (· ∣ n) i` is
$d_{i+1}$), then
$$G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.$$ -/
noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)
end Erdos673

namespace Erdos673

/-- SL-003 transported target: FormalConjectures/ErdosProblems/673.lean `erdos_673.parts.ii`. -/
def SL003.targetProp : Prop :=
  (fun X : ℕ ↦ ∑ n ∈ Finset.Icc 1 X, G n) ~[atTop] fun X : ℕ ↦ (X : ℝ) * log X

end Erdos673
end
end SL003FC
