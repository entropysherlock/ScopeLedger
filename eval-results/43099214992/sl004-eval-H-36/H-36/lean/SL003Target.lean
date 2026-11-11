import Mathlib
import OeisA6697.solution

namespace SL003FC

section
namespace OeisA6697
open PowerSeries WithPiTopology List
/-- The morphism σ on {a, b} defined by a ↦ aab, b ↦ b, represented on Bool where
`false` = a and `true` = b. -/
def morphism : Bool → List Bool
  | false => [false, false, true]  -- a ↦ aab
  | true => [true]                -- b ↦ b
/-- The n-th iterate of the morphism applied to [a]. -/
def finiteWord : ℕ → List Bool
  | 0 => [false]
  | n + 1 => (finiteWord n).flatMap morphism
/-- The infinite word w is the fixed point of the morphism starting from 'a'.
We define it as the limit: w(i) is the i-th symbol, which stabilizes after
sufficiently many iterations. -/
noncomputable def infiniteWord (i : ℕ) : Bool :=
  (finiteWord (i + 1))[i]'(by grw [length_finiteWord, ← Nat.lt_two_pow_self] <;> lia)
/-- A subword (factor) of length n starting at position i. -/
noncomputable def subwordAt (i n : ℕ) : List Bool :=
  (List.range n).map fun j => infiniteWord (i + j)
/-- The set of all distinct subwords of length n in the infinite word. -/
def subwordsOfLength (n : ℕ) : Set (List Bool) :=
  {w | ∃ i, w = subwordAt i n}
/-- The subword complexity function: a(n) is the number of distinct subwords of length n. -/
noncomputable def a (n : ℕ) : ℕ := (subwordsOfLength n).ncard
end OeisA6697

namespace OeisA6697

/-- SL-003 transported target: FormalConjectures/OEIS/6697.lean `conjecture`. -/
def SL003.targetProp : Prop :=
  ∀ (n : ℕ), a n = coeff (R := ℚ) n
      ((1 - X)⁻¹ + X * (1 - X)⁻¹ ^ 2 * ((1 - X)⁻¹ - ∑' k, X ^ (2 ^ (k + 1) + k)))

end OeisA6697
end
end SL003FC
