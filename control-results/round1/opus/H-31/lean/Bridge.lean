import SL003Target

/-! Bridge for H-31 (Erdős 136): from `Erdos136.erdos_136`.

The transported and cited `(4,5)`-colouring predicates differ only in the `DecidableEq`
instance used by `Finset.image`, so the minimal palette sizes agree. -/

namespace SL004.H31

theorem is45_iff {n k : ℕ} (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) :
    SL003FC.Erdos136.Is45Coloring C ↔ Erdos136.Is45Coloring C := by
  unfold SL003FC.Erdos136.Is45Coloring Erdos136.Is45Coloring
  constructor
  · intro h v
    convert h v
  · intro h v
    convert h v

theorem colorable_iff (n k : ℕ) :
    SL003FC.Erdos136.Colorable n k ↔ Erdos136.Colorable n k := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (is45_iff C).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (is45_iff C).2 hC⟩

theorem f_eq (n : ℕ) : SL003FC.Erdos136.f n = Erdos136.erdos136Fun n := by
  have hspec : SL003FC.Erdos136.Colorable n (Erdos136.erdos136Fun n) :=
    (colorable_iff n _).2 (Erdos136.erdos136Fun_spec n)
  unfold SL003FC.Erdos136.f
  apply le_antisymm
  · exact Nat.sInf_le hspec
  · apply Erdos136.erdos136Fun_min
    apply (colorable_iff n _).1
    exact Nat.sInf_mem (s := {k : ℕ | SL003FC.Erdos136.Colorable n k})
      ⟨Erdos136.erdos136Fun n, hspec⟩

end SL004.H31

theorem SL004.bridge_main : SL003FC.Erdos136.SL003.targetProp := by
  unfold SL003FC.Erdos136.SL003.targetProp
  refine Erdos136.erdos_136.congr (fun n => ?_)
  show (Erdos136.erdos136Fun n : ℝ) / (n : ℝ) = (SL003FC.Erdos136.f n : ℝ) / (n : ℝ)
  rw [SL004.H31.f_eq]
