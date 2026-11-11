import SL003Target
import SL004Lib

/-! SL-004 dev, SL003-55 via the library: `Nat.find` is the least element (`SL004Lib.isLeast_find`). -/

open Classical in
theorem SL004.corr55_lib (n : ℕ) : SL003FC.Erdos841.t n = Erdos841.t n := by
  unfold SL003FC.Erdos841.t Erdos841.t
  exact IsLeast.csInf_eq (SL004Lib.isLeast_find _ (Erdos841.exists_admissible n))
