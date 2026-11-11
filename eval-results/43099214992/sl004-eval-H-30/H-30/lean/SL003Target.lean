import Mathlib
import ErdosProblems.Erdos674

namespace SL003FC

section
namespace Erdos674
/-- The set of integer solutions to $x^x y^y = z^z$ with $x, y, z > 1$. -/
def solutionSet : Set (ℕ × ℕ × ℕ) :=
  {(x, y, z) | 1 < x ∧ 1 < y ∧ 1 < z ∧ x ^ x * y ^ y = z ^ z}
end Erdos674

namespace Erdos674

/-- SL-003 transported target: FormalConjectures/ErdosProblems/674.lean `erdos_674`. -/
def SL003.targetProp : Prop :=
  solutionSet.Nonempty

end Erdos674
end
end SL003FC
