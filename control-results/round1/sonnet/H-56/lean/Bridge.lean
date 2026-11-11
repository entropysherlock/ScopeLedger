import SL003Target

noncomputable def SL004.poly (N : ℕ) (ε : Fin N → ℝ) : Polynomial ℂ :=
  ∑ k : Fin N, Polynomial.C (ε k : ℂ) * Polynomial.X ^ (k : ℕ)

theorem SL004.coeff_poly (N : ℕ) (ε : Fin N → ℝ) (i : ℕ) :
    (SL004.poly N ε).coeff i = if h : i < N then (ε ⟨i, h⟩ : ℂ) else 0 := by
  unfold SL004.poly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases h : i < N
  · rw [dif_pos h, Finset.sum_eq_single (⟨i, h⟩ : Fin N)]
    · simp
    · intro b _ hb
      have : i ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
      simp [this]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro b _
    have hb := b.2
    have : i ≠ (b : ℕ) := by omega
    simp [this]

theorem SL004.natDegree_poly (n : ℕ) (ε : Fin (n + 1) → ℝ) (hε : ∀ k, ε k = -1 ∨ ε k = 1) :
    (SL004.poly (n + 1) ε).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [SL004.coeff_poly, dif_neg (by omega)]
  · rw [SL004.coeff_poly, dif_pos (by omega)]
    rcases hε ⟨n, by omega⟩ with h | h <;> simp [h]

theorem SL004.sign_poly (n : ℕ) (ε : Fin (n + 1) → ℝ) (hε : ∀ k, ε k = -1 ∨ ε k = 1) :
    ∀ i ≤ (SL004.poly (n + 1) ε).natDegree,
      (SL004.poly (n + 1) ε).coeff i = -1 ∨ (SL004.poly (n + 1) ε).coeff i = 1 := by
  intro i hi
  rw [SL004.natDegree_poly n ε hε] at hi
  rw [SL004.coeff_poly, dif_pos (by omega)]
  rcases hε ⟨i, by omega⟩ with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem SL004.eval_poly (N : ℕ) (ε : Fin N → ℝ) (z : ℂ) :
    (SL004.poly N ε).eval z = OAI.AsymptoticallyMinimalLittlewood.littlewoodValue ε z := by
  unfold SL004.poly OAI.AsymptoticallyMinimalLittlewood.littlewoodValue
  rw [Polynomial.eval_finset_sum]
  simp

theorem SL004.bridge_main : SL003FC.Erdos1150.SL003.targetProp := by
  rintro ⟨c, hc, hev⟩
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨N₀, -, hmain⟩ := OAI.AsymptoticallyMinimalLittlewood.main (c / 2) (half_pos hc)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (1 + c) ^ 2 - (1 + c / 2) ^ 2 := ⟨_, rfl⟩
  have hDpos : 0 < D := by
    rw [hD]
    nlinarith [sq_nonneg c]
  obtain ⟨m, hm⟩ := exists_nat_ge ((1 + c / 2) ^ 2 / D)
  obtain ⟨n, hnn⟩ : ∃ n : ℕ, n = max (max n₁ N₀) m := ⟨_, rfl⟩
  have hn1 : n₁ ≤ n := by rw [hnn]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hn2 : N₀ ≤ n + 1 := by
    have : N₀ ≤ n := by rw [hnn]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  have hn3 : m ≤ n := by rw [hnn]; exact le_max_right _ _
  obtain ⟨ε, hε, hbd⟩ := hmain (n + 1) hn2
  have hε' : ∀ k, ε k = -1 ∨ ε k = 1 := hε
  haveI : Nonempty (Metric.sphere (0 : ℂ) 1) := ⟨⟨1, by simp⟩⟩
  have hsupb : (⨆ z : Metric.sphere (0 : ℂ) 1, ‖(SL004.poly (n + 1) ε).eval (z : ℂ)‖) ≤
      (1 + c / 2) * Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
    apply ciSup_le
    intro z
    rw [SL004.eval_poly]
    exact hbd z (mem_sphere_zero_iff_norm.mp z.2)
  have hP := hn₁ n hn1 (SL004.poly (n + 1) ε) (SL004.sign_poly n ε hε')
    (SL004.natDegree_poly n ε hε')
  have hnR : (m : ℝ) ≤ n := by exact_mod_cast hn3
  have hnD : (1 + c / 2) ^ 2 ≤ n * ((1 + c) ^ 2 - (1 + c / 2) ^ 2) := by
    have h1 : (1 + c / 2) ^ 2 / D ≤ n := le_trans hm hnR
    rw [div_le_iff₀ hDpos] at h1
    rw [← hD]
    exact h1
  have hkey : ((1 + c / 2) * Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 ≤
      ((1 + c) * Real.sqrt (n : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    push_cast
    nlinarith [hnD]
  have hx0 : 0 ≤ (1 + c / 2) * Real.sqrt (((n + 1 : ℕ) : ℝ)) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hy0 : 0 ≤ (1 + c) * Real.sqrt (n : ℝ) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hle : (1 + c / 2) * Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤ (1 + c) * Real.sqrt (n : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have h3 := mul_self_lt_mul_self hy0 hcon
    nlinarith [hkey, h3]
  linarith [hP, hsupb, hle]
