import Mathlib
import LeanGallery.NumberTheory.Erdos482.Statement

namespace SL003FC

section
namespace Erdos482
/-- The sequence of the problem: $a_1 = 1$ and $a_{n+1} = \lfloor \sqrt{2}(a_n + 1/2) \rfloor$ for
$n \geq 1$. The value $a_0$ is not used. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊√2 * ((a (n + 1) : ℝ) + 1 / 2)⌋₊
/-- Stoll's general Graham–Pollak-type recurrence in base $g$, with real parameters $a$, $b$, and
$\varepsilon$. Its even-index differences are used to read base-$g$ digits. -/
noncomputable def generalRecurrence (g : ℕ) (a b ε : ℝ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      if Even n then ⌊a * ((generalRecurrence g a b ε n : ℝ) + ε)⌋
      else ⌊b * ((generalRecurrence g a b ε n : ℝ) + 1 / ((g : ℝ) - 1))⌋
/-- The odd-step coefficient of the Rabinowitz–Gilbert/Stoll binary recurrence. -/
noncomputable def alpha (t : ℝ) : ℝ := 2 * (t + 1) / (t + 2)
/-- The even-step coefficient of the Rabinowitz–Gilbert/Stoll binary recurrence. -/
noncomputable def beta (t : ℝ) : ℝ := (t + 2) / (t + 1)
/-- Zero-based form of the Rabinowitz–Gilbert/Stoll binary recurrence: `stollBinary t k` is the
paper's $u_{k+1}$.  At $t = \sqrt{2}$ both coefficients equal $\sqrt{2}$, and this is the sequence
`a` shifted by one. -/
noncomputable def stollBinary (t : ℝ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ⌊(if Even n then alpha t else beta t) * ((stollBinary t n : ℝ) + 1 / 2)⌋₊
/-- The binary digits of a normalized real $t \in [1, 2)$, indexed from one and including the
leading digit.  The value at index zero is padding. -/
noncomputable def binaryDigit (t : ℝ) : ℕ → Fin 2
  | 0 => 0
  | 1 => 1
  | k + 2 => Real.digits (t - 1) 2 k
end Erdos482

namespace Erdos482

/-- SL-003 transported target: FormalConjectures/ErdosProblems/482.lean `erdos_482`. -/
def SL003.targetProp : Prop :=
  (∀ n : ℕ, 1 ≤ n →
      (a (2 * n + 1) : ℤ) - 2 * a (2 * n - 1) = (Real.digits (√2 / 2) 2 (n - 1) : ℕ)) ∧
      Real.ofDigits (Real.digits (√2 / 2) 2) = √2 / 2

end Erdos482
end
end SL003FC
