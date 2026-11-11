import Mathlib
import ErdosProblems.Erdos49

namespace SL003FC

section
open Filter Asymptotics
namespace Erdos49
/-- The largest size of a set $A\subseteq\{1,\ldots,N\}$ on which Euler's totient function is
strictly increasing. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ StrictMonoOn Nat.totient (A : Set ℕ) ∧
    A.card = k}
/-- The largest size of a set $A\subseteq\{1,\ldots,N\}$ on which Euler's totient function is
non-decreasing. -/
noncomputable def g (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ MonotoneOn Nat.totient (A : Set ℕ) ∧
    A.card = k}
end Erdos49

namespace Erdos49

/-- SL-003 transported target: FormalConjectures/ErdosProblems/49.lean `erdos_49.variants.tao`. -/
def SL003.targetProp : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 10 ≤ N →
    (g N : ℝ) ≤ (1 + C * (Real.log (Real.log N) ^ 5 / Real.log N)) *
      Nat.primeCounting N

end Erdos49
end
end SL003FC
