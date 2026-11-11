import SL003Target

open scoped unitInterval Topology
open Filter

namespace SL004.H54

/-- Extension of an interval automorphism to the real line by the identity. -/
noncomputable def extFun (f : Dlab.IntervalAut) (x : ℝ) : ℝ :=
  if h : x ∈ Set.Icc (0 : ℝ) 1 then ((f ⟨x, h⟩ : unitInterval) : ℝ) else x

theorem extFun_of_mem (f : Dlab.IntervalAut) {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) :
    extFun f x = ((f ⟨x, h⟩ : unitInterval) : ℝ) := by
  unfold extFun
  rw [dif_pos h]

theorem extFun_of_not_mem (f : Dlab.IntervalAut) {x : ℝ} (h : x ∉ Set.Icc (0 : ℝ) 1) :
    extFun f x = x := by
  unfold extFun
  rw [dif_neg h]

theorem notIcc_of_neg {x : ℝ} (h : x < 0) : x ∉ Set.Icc (0 : ℝ) 1 :=
  fun hh => absurd hh.1 (not_le.mpr h)

theorem notIcc_of_gt {x : ℝ} (h : 1 < x) : x ∉ Set.Icc (0 : ℝ) 1 :=
  fun hh => absurd hh.2 (not_le.mpr h)

theorem extFun_mem_iff (f : Dlab.IntervalAut) (x : ℝ) :
    extFun f x ∈ Set.Icc (0 : ℝ) 1 ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : x ∈ Set.Icc (0 : ℝ) 1
  · rw [extFun_of_mem f h]
    exact ⟨fun _ => h, fun _ => (f ⟨x, h⟩).2⟩
  · rw [extFun_of_not_mem f h]

theorem extFun_mul (f g : Dlab.IntervalAut) (x : ℝ) :
    extFun (f * g) x = extFun f (extFun g x) := by
  by_cases h : x ∈ Set.Icc (0 : ℝ) 1
  · have hg : extFun g x ∈ Set.Icc (0 : ℝ) 1 := (extFun_mem_iff g x).mpr h
    have e : (g ⟨x, h⟩ : unitInterval) = ⟨extFun g x, hg⟩ :=
      Subtype.ext (extFun_of_mem g h).symm
    rw [extFun_of_mem (f * g) h, extFun_of_mem f hg, ← e]
    try rfl
  · have hg : extFun g x ∉ Set.Icc (0 : ℝ) 1 := fun hh => h ((extFun_mem_iff g x).mp hh)
    rw [extFun_of_not_mem _ h, extFun_of_not_mem g h, extFun_of_not_mem f h]

theorem extFun_one (x : ℝ) : extFun (1 : Dlab.IntervalAut) x = x := by
  by_cases h : x ∈ Set.Icc (0 : ℝ) 1
  · rw [extFun_of_mem _ h]
    rfl
  · exact extFun_of_not_mem _ h

theorem extFun_zero (a : Dlab.IntervalAut) : extFun a 0 = 0 := by
  have h : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [extFun_of_mem a h]
  exact congrArg Subtype.val (IntervalAut.map_zero a)

theorem extFun_one' (a : Dlab.IntervalAut) : extFun a 1 = 1 := by
  have h : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [extFun_of_mem a h]
  exact congrArg Subtype.val (IntervalAut.map_one a)

theorem extFun_ge_one (a : Dlab.IntervalAut) {p : ℝ} (hp : 1 ≤ p) : extFun a p = p := by
  by_cases hp1 : p = 1
  · subst hp1
    exact extFun_one' a
  · exact extFun_of_not_mem a (notIcc_of_gt (lt_of_le_of_ne hp (Ne.symm hp1)))

theorem extFun_strictMono (f : Dlab.IntervalAut) : StrictMono (extFun f) := by
  intro x y hxy
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · rw [extFun_of_mem f hx, extFun_of_mem f hy]
    exact f.strictMono (show (⟨x, hx⟩ : unitInterval) < ⟨y, hy⟩ from hxy)
  · rw [extFun_of_mem f hx, extFun_of_not_mem f hy]
    have h1 : 1 < y := by
      by_contra hh
      push_neg at hh
      exact hy ⟨by linarith [hx.1], hh⟩
    exact lt_of_le_of_lt (f ⟨x, hx⟩).2.2 h1
  · rw [extFun_of_not_mem f hx, extFun_of_mem f hy]
    have h1 : x < 0 := by
      by_contra hh
      push_neg at hh
      exact hx ⟨hh, by linarith [hy.2]⟩
    exact lt_of_lt_of_le h1 (f ⟨y, hy⟩).2.1
  · rw [extFun_of_not_mem f hx, extFun_of_not_mem f hy]
    exact hxy

/-- The extension as an order automorphism of the real line. -/
noncomputable def extOrd (f : Dlab.IntervalAut) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (extFun f) (extFun_strictMono f) (by
    intro y
    refine ⟨extFun f⁻¹ y, ?_⟩
    have h : extFun (f * f⁻¹) y = y := by
      rw [mul_inv_cancel]
      exact extFun_one y
    rwa [extFun_mul] at h)

theorem extOrd_apply (f : Dlab.IntervalAut) (x : ℝ) : extOrd f x = extFun f x := rfl

noncomputable def extHom : Dlab.IntervalAut →* (ℝ ≃o ℝ) where
  toFun := extOrd
  map_one' := by
    ext x
    exact extFun_one x
  map_mul' f g := by
    ext x
    exact extFun_mul f g x

theorem extHom_apply (f : Dlab.IntervalAut) : extHom f = extOrd f := rfl

theorem extHom_injective : Function.Injective extHom := by
  intro f g h
  ext a
  have h1 : extFun f a = extFun g a := congrArg (fun k : ℝ ≃o ℝ => k (a : ℝ)) h
  rw [extFun_of_mem f a.2, extFun_of_mem g a.2] at h1
  exact h1

/-- The Dlab group realised inside the order automorphisms of the real line. -/
noncomputable def Gr (K : Subgroup NNRealˣ) : Subgroup (ℝ ≃o ℝ) :=
  (Dlab.subgroup K).map extHom

noncomputable def eqv (K : Subgroup NNRealˣ) : DlabGroup K ≃* Gr K :=
  Subgroup.equivMapOfInjective (Dlab.subgroup K) extHom extHom_injective

theorem eqv_apply (K : Subgroup NNRealˣ) (a : DlabGroup K) :
    ((eqv K a : Gr K) : ℝ ≃o ℝ) = extOrd a.1 := by
  first
    | rfl
    | exact Subgroup.coe_equivMapOfInjective_apply _ _ _ _

theorem eventually_ext_id (a : Dlab.IntervalAut) (p : unitInterval)
    (h : ∀ᶠ t in 𝓝 p, a t = t) : ∀ᶠ y in 𝓝 (p : ℝ), extFun a y = y := by
  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp h
  refine Metric.eventually_nhds_iff.mpr ⟨ε, hε, ?_⟩
  intro y hy
  by_cases hyI : y ∈ Set.Icc (0 : ℝ) 1
  · rw [extFun_of_mem a hyI]
    have hd : dist (⟨y, hyI⟩ : unitInterval) p < ε := by
      rw [Subtype.dist_eq]
      exact hy
    exact congrArg Subtype.val (hh hd)
  · exact extFun_of_not_mem a hyI

theorem ext_props (K : Subgroup NNRealˣ) (a : Dlab.IntervalAut) (ha : Dlab.IsElement K a) :
    SL003FC.Kourovka.«21.149».IsLocallyRightLinear K (extOrd a) ∧
    (∀ x ∉ Set.Ioo (0 : ℝ) 1, extOrd a x = x) ∧
    (∀ᶠ x in 𝓝 (0 : ℝ), extOrd a x = x) ∧ (∀ᶠ x in 𝓝 (1 : ℝ), extOrd a x = x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    by_cases hp0 : p < 0
    · refine ⟨-p, by linarith, 1, K.one_mem, ?_⟩
      intro x hx1 hx2
      have hx0 : x < 0 := by linarith
      rw [extOrd_apply, extOrd_apply, extFun_of_not_mem a (notIcc_of_neg hp0),
        extFun_of_not_mem a (notIcc_of_neg hx0)]
      simp
    · by_cases hp1 : 1 ≤ p
      · refine ⟨1, one_pos, 1, K.one_mem, ?_⟩
        intro x hx1 hx2
        have hx : 1 < x := by linarith
        rw [extOrd_apply, extOrd_apply, extFun_ge_one a hp1, extFun_of_not_mem a (notIcc_of_gt hx)]
        simp
      · push_neg at hp0 hp1
        have hpI : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp0, hp1.le⟩
        have hlt : (⟨p, hpI⟩ : unitInterval) < 1 := by
          first
            | exact hp1
            | (show p < 1
               exact hp1)
        obtain ⟨ε, hε, h, hl⟩ := ha.1 ⟨p, hpI⟩ hlt
        refine ⟨min ε (1 - p), lt_min hε (by linarith), h.1, h.2, ?_⟩
        intro x hx1 hx2
        have hxε : x < p + ε := lt_of_lt_of_le hx2 (by linarith [min_le_left ε (1 - p)])
        have hx1' : x < 1 := by linarith [min_le_right ε (1 - p)]
        have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, hx1'.le⟩
        have hres := @hl ⟨x, hxI⟩ hx1 hxε
        rw [extOrd_apply, extOrd_apply, extFun_of_mem a hxI, extFun_of_mem a hpI]
        exact hres
  · intro x hx
    rw [extOrd_apply]
    by_cases hxI : x ∈ Set.Icc (0 : ℝ) 1
    · have h01 : x = 0 ∨ x = 1 := by
        by_contra hh
        push_neg at hh
        exact hx ⟨lt_of_le_of_ne hxI.1 (Ne.symm hh.1), lt_of_le_of_ne hxI.2 hh.2⟩
      rcases h01 with rfl | rfl
      · exact extFun_zero a
      · exact extFun_one' a
    · exact extFun_of_not_mem a hxI
  · exact eventually_ext_id a 0 ha.2.1
  · exact eventually_ext_id a 1 ha.2.2

theorem restr_exists (f : ℝ ≃o ℝ) (h : ∀ x, x ∉ Set.Ioo (0 : ℝ) 1 → f x = x) :
    ∃ a : Dlab.IntervalAut, extOrd a = f := by
  have h0 : f 0 = 0 := h 0 (by simp)
  have h1 : f 1 = 1 := h 1 (by simp)
  have hm : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    constructor
    · have := f.monotone hx.1
      rwa [h0] at this
    · have := f.monotone hx.2
      rwa [h1] at this
  have hs0 : f.symm 0 = 0 := by
    rw [OrderIso.symm_apply_eq]
    exact h0.symm
  have hs1 : f.symm 1 = 1 := by
    rw [OrderIso.symm_apply_eq]
    exact h1.symm
  have hm' : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → f.symm y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    constructor
    · have := f.symm.monotone hy.1
      rwa [hs0] at this
    · have := f.symm.monotone hy.2
      rwa [hs1] at this
  let a : Dlab.IntervalAut :=
    { toEquiv :=
        { toFun := fun x => ⟨f x, hm x x.2⟩
          invFun := fun y => ⟨f.symm y, hm' y y.2⟩
          left_inv := fun x => Subtype.ext (f.symm_apply_apply x)
          right_inv := fun y => Subtype.ext (f.apply_symm_apply y) }
      map_rel_iff' := by
        intro x y
        exact f.le_iff_le }
  refine ⟨a, ?_⟩
  ext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · rw [extOrd_apply, extFun_of_mem a hx]
    try rfl
  · rw [extOrd_apply, extFun_of_not_mem a hx]
    exact (h x (fun hh => hx ⟨hh.1.le, hh.2.le⟩)).symm

theorem isDlabGroup (K : Subgroup NNRealˣ) :
    SL003FC.Kourovka.«21.149».IsDlabGroup K (Gr K) := by
  left
  intro f
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ext_props K a ha
  · rintro ⟨hlin, hout, h0, h1⟩
    obtain ⟨a, rfl⟩ := restr_exists f hout
    have h0' : ∀ᶠ t in 𝓝 (0 : unitInterval), a t = t := by
      have key := (continuous_subtype_val.tendsto (0 : unitInterval)).eventually
        (show ∀ᶠ y in 𝓝 (((0 : unitInterval)) : ℝ), extOrd a y = y from h0)
      refine key.mono (fun t ht => Subtype.ext ?_)
      rw [extOrd_apply, extFun_of_mem a t.2] at ht
      exact ht
    have h1' : ∀ᶠ t in 𝓝 (1 : unitInterval), a t = t := by
      have key := (continuous_subtype_val.tendsto (1 : unitInterval)).eventually
        (show ∀ᶠ y in 𝓝 (((1 : unitInterval)) : ℝ), extOrd a y = y from h1)
      refine key.mono (fun t ht => Subtype.ext ?_)
      rw [extOrd_apply, extFun_of_mem a t.2] at ht
      exact ht
    have hlin' : Dlab.IsLocallyRightHLinear K a := by
      intro p hp
      obtain ⟨ε, hε, h, hhK, hl⟩ := hlin (p : ℝ)
      refine ⟨ε, hε, ⟨h, hhK⟩, ?_⟩
      intro x hx1 hx2
      have hres := hl (x : ℝ) hx1 hx2
      rw [extOrd_apply, extOrd_apply, extFun_of_mem a x.2, extFun_of_mem a p.2] at hres
      exact hres
    have hmem : a ∈ Dlab.subgroup K := Dlab.mem_subgroup.mpr ⟨hlin', h0', h1'⟩
    exact Subgroup.mem_map.mpr ⟨a, hmem, rfl⟩

theorem dlabLt_eqv (K : Subgroup NNRealˣ) (a b : DlabGroup K) :
    SL003FC.Kourovka.«21.149».DlabLt (eqv K a) (eqv K b) ↔
      KourovkaNotebook.Solution21_149.FirstDisagreementLt K a b := by
  unfold SL003FC.Kourovka.«21.149».DlabLt KourovkaNotebook.Solution21_149.FirstDisagreementLt
  simp only [eqv_apply, extOrd_apply]
  constructor
  · rintro ⟨x, hx, hy⟩
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := by
      by_contra hn
      rw [extFun_of_not_mem _ hn, extFun_of_not_mem _ hn] at hx
      exact lt_irrefl _ hx
    refine ⟨⟨x, hxI⟩, ?_, ?_⟩
    · rw [extFun_of_mem _ hxI, extFun_of_mem _ hxI] at hx
      exact hx
    · intro y hyl
      apply hy y
      rw [extFun_of_mem _ y.2, extFun_of_mem _ y.2]
      exact hyl
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, ?_, ?_⟩
    · rw [extFun_of_mem _ x.2, extFun_of_mem _ x.2]
      exact hx
    · intro y hyl
      by_cases hyI : y ∈ Set.Icc (0 : ℝ) 1
      · rw [extFun_of_mem _ hyI, extFun_of_mem _ hyI] at hyl
        exact hy ⟨y, hyI⟩ hyl
      · rw [extFun_of_not_mem _ hyI, extFun_of_not_mem _ hyI] at hyl
        exact absurd hyl (lt_irrefl _)

end SL004.H54


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
