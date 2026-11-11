import Mathlib
import LeanOeisProofs.NewFormalization.A397588

namespace SL003FC

section
namespace OeisA397588
/-- Manyama's coefficient recurrence, extended by $a(0)=0$. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (n + 3) * ∑ k ∈ (Finset.Icc 1 (n + 1)).attach, a k.1 * a (n + 2 - k.1)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Finset.mem_Icc.mp k.2).2
  · exact Nat.sub_lt (Nat.succ_pos _) (Finset.mem_Icc.mp k.2).1
end OeisA397588

namespace OeisA397588

/-- SL-003 transported target: FormalConjectures/OEIS/397588.lean `three_dvd_a`. -/
def SL003.targetProp : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), 3 ∣ a n

end OeisA397588
end
end SL003FC
