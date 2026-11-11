import Mathlib
import LeanOeisProofs.NewFormalization.A361033

namespace SL003FC

section
namespace OeisA361033
/-- The factorial ratio $3(4n)!/(n!((n+1)!)^3)$. -/
def a (n : ℕ) : ℕ :=
  3 * (4 * n).factorial / (n.factorial * (n + 1).factorial ^ 3)
end OeisA361033

namespace OeisA361033

/-- SL-003 transported target: FormalConjectures/OEIS/361033.lean `conjecture_1`. -/
def SL003.targetProp : Prop :=
  ∀ (n : ℕ), Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1

end OeisA361033
end
end SL003FC
