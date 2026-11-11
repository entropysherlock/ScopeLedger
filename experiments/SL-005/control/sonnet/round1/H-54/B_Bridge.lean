import SL003Target
import A_Infra

theorem SL004.bridge_main : SL003FC.Kourovka.«21.149».SL003.targetProp := by
  obtain ⟨H, o, hdlab, φ, hφ⟩ := kourovka_21_149
  letI : LinearOrder (DlabGroup H) := o
  have hle : ∀ a b : DlabGroup H, φ a ≤ φ b ↔ a ≤ b := by
    intro a b
    first
      | exact map_le_map_iff φ
      | exact φ.map_le_map_iff'
      | exact φ.toOrderIso.le_iff_le
  have hlt : ∀ a b : DlabGroup H, φ a < φ b ↔ a < b := by
    intro a b
    rw [← not_le, ← not_le, hle b a]
  let e : DlabGroup H ≃* SL004.H54.Gr H := SL004.H54.eqv H
  let α : SL004.H54.Gr H ≃* SL004.H54.Gr H := e.symm.trans (φ.toMulEquiv.trans e)
  have hα : ∀ a, α (e a) = e (φ a) := by
    intro a
    show e (φ.toMulEquiv (e.symm (e a))) = e (φ a)
    rw [MulEquiv.symm_apply_apply]
    try rfl
  refine ⟨H, SL004.H54.Gr H, SL004.H54.isDlabGroup H, α, ?_, ?_⟩
  · intro f g
    obtain ⟨a, rfl⟩ := e.surjective f
    obtain ⟨b, rfl⟩ := e.surjective g
    rw [hα, hα]
    exact (SL004.H54.dlabLt_eqv H (φ a) (φ b)).trans
      (((hdlab.lt_iff_firstDisagreement (φ a) (φ b)).symm.trans
        ((hlt a b).trans (hdlab.lt_iff_firstDisagreement a b))).trans
        (SL004.H54.dlabLt_eqv H a b).symm)
  · rintro ⟨u, hu⟩
    apply hφ
    unfold MulAut.innerSubgroup
    rw [MonoidHom.mem_range]
    refine ⟨(e.symm u)⁻¹, ?_⟩
    ext a
    have h1 := hu (e a)
    rw [hα] at h1
    have h2 : φ a = e.symm (u⁻¹ * e a * u) := by
      rw [← h1]
      simp
    have h3 : φ.toMulEquiv a = φ a := rfl
    rw [MulAut.conj_apply, h3, h2]
    simp
