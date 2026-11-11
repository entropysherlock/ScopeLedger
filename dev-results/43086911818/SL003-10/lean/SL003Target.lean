import Mathlib
import ErdosProblems.Erdos525

namespace SL003FC

section
open Filter Real Finset
namespace Erdos525
/-- The degree-`n` polynomial $f(z)=\sum_{j\leq n}\epsilon_j z^j$ with coefficients
`ε : Fin (n + 1) → ℤˣ`, i.e. $\epsilon_j\in\{-1,1\}$, evaluated at `z`. -/
def eval {n : ℕ} (ε : Fin (n + 1) → ℤˣ) (z : ℂ) : ℂ :=
  ∑ j, ((ε j : ℤ) : ℂ) * z ^ (j : ℕ)
/-- The degree-`n` polynomials with $\pm 1$ coefficients such that $|f(z)|\geq 1$ for all
$|z|=1$. -/
def exceptional (n : ℕ) : Set (Fin (n + 1) → ℤˣ) :=
  {ε | ∀ z : ℂ, ‖z‖ = 1 → 1 ≤ ‖eval ε z‖}
/-- $m(f)=\min_{|z|=1}|f(z)|$. -/
noncomputable def m {n : ℕ} (ε : Fin (n + 1) → ℤˣ) : ℝ :=
  sInf ((fun z ↦ ‖eval ε z‖) '' Metric.sphere (0 : ℂ) 1)
open scoped Classical in
/-- The probability that a uniformly random degree-`n` polynomial with $\pm 1$ coefficients
satisfies `P`. -/
noncomputable def prob (n : ℕ) (P : (Fin (n + 1) → ℤˣ) → Prop) : ℝ :=
  ((univ.filter P).card : ℝ) / 2 ^ (n + 1)
end Erdos525

namespace Erdos525

/-- SL-003 transported target: FormalConjectures/ErdosProblems/525.lean `erdos_525.parts.i`. -/
def SL003.targetProp : Prop :=
  (fun n : ℕ ↦ ((exceptional n).ncard : ℝ)) =o[atTop] fun n : ℕ ↦ (2 : ℝ) ^ n

end Erdos525
end
end SL003FC
