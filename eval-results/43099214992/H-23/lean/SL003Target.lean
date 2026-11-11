import Mathlib
import Solution

namespace SL003FC

section
open Filter
namespace Erdos1180
/--
`Represents ε p a s` says that the multiset `s` of denominators `n` with `1 ≤ n ≤ p^ε` and
`n` coprime to `p` has `∑ n⁻¹ = a` in `ZMod p`.
-/
def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (s : Multiset ℕ) : Prop :=
  (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
    (s.map fun n : ℕ ↦ (n : ZMod p)⁻¹).sum = a
/--
`C ε` is the least `C` such that, for all primes `p`, every residue modulo `p` is the sum of at
most `C` elements of `{n⁻¹ : 1 ≤ n ≤ p^ε}` (or `0` if no such `C` exists).
-/
noncomputable def C (ε : ℝ) : ℕ :=
  sInf {C | ∀ p : ℕ, p.Prime → ∀ a : ZMod p, ∃ s : Multiset ℕ, s.card ≤ C ∧ Represents ε p a s}
end Erdos1180

namespace Erdos1180

/-- SL-003 transported target: FormalConjectures/ErdosProblems/1180.lean `erdos_1180.variants.shparlinski`. -/
def SL003.targetProp : Prop :=
  ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → ∀ a : ZMod p,
      ∃ s : Multiset ℕ, (s.card : ℝ) ≤ K * ε⁻¹ ^ 3 ∧ Represents ε p a s

end Erdos1180
end
end SL003FC
