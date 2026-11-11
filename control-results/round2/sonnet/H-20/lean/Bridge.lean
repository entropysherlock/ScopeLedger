import SL003Target

universe u

theorem SL004.bridge_main : SL003FC.Erdos522.SL003.targetProp.{u} := by
  intro Ω i1 i2 n hn f
  have h := E522.erdos_522_zero_one_solved.mp trivial (Ω := Ω) (n := n)
  let g : Erdos522.KacCoefficients ({0, 1} : Set ℂ) Ω := ⟨f.toFun, f.h_indep, f.h_unif⟩
  have hcount : ∀ (m : ℕ) (ω : Ω), g.numRootsInUnitDisk m ω = f.numRootsInUnitDisk m ω :=
    fun m ω => rfl
  have key := h hn g
  first
    | exact key
    | (simp only [hcount] at key
       exact key)
