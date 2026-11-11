import SL003Target

/-! Bridge for H-56 (Erdős 1150): from `OAI.AsymptoticallyMinimalLittlewood.main`.

Given `c > 0`, apply the cited theorem with `η = c / 2` to get, for every large `n`, a real
signing `ε` of length `n + 1` whose Littlewood polynomial has sup-norm at most
`(1 + c/2) √(n+1)` on the unit circle.  Turned into a complex polynomial of degree `n` with
`±1` coefficients, this contradicts the assumed lower bound `(1 + c) √n` once `n` is large. -/

open Polynomial

namespace SL004.H56

/-- Coefficients of the polynomial attached to a signing of length `n + 1`. -/
noncomputable def coeffFn (n : ℕ) (ε : Fin (n + 1) → ℝ) (k : ℕ) : ℂ :=
  if h : k < n + 1 then ((ε ⟨k, h⟩ : ℝ) : ℂ) else 0

/-- The complex polynomial `∑_{k ≤ n} ε_k X^k`. -/
noncomputable def poly (n : ℕ) (ε : Fin (n + 1) → ℝ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (coeffFn n ε k) * X ^ k

theorem poly_coeff (n : ℕ) (ε : Fin (n + 1) → ℝ) (i : ℕ) (hi : i < n + 1) :
    (poly n ε).coeff i = coeffFn n ε i := by
  unfold poly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hi)]

theorem coeffFn_sign (n : ℕ) (ε : Fin (n + 1) → ℝ) (hε : ∀ k, ε k = -1 ∨ ε k = 1) (i : ℕ)
    (hi : i < n + 1) : coeffFn n ε i = -1 ∨ coeffFn n ε i = 1 := by
  unfold coeffFn
  rw [dif_pos hi]
  rcases hε ⟨i, hi⟩ with h | h <;> simp [h]

theorem poly_natDegree (n : ℕ) (ε : Fin (n + 1) → ℝ) (hε : ∀ k, ε k = -1 ∨ ε k = 1) :
    (poly n ε).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold poly
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hk' := Finset.mem_range.1 hk
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · rw [poly_coeff n ε n (Nat.lt_succ_self n)]
    rcases coeffFn_sign n ε hε n (Nat.lt_succ_self n) with h | h <;> rw [h] <;> norm_num

theorem poly_eval (n : ℕ) (ε : Fin (n + 1) → ℝ) (z : ℂ) :
    (poly n ε).eval z = OAI.AsymptoticallyMinimalLittlewood.littlewoodValue ε z := by
  unfold poly OAI.AsymptoticallyMinimalLittlewood.littlewoodValue
  rw [Polynomial.eval_finsetSum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [coeffFn, k.isLt]

end SL004.H56

theorem SL004.bridge_main : SL003FC.Erdos1150.SL003.targetProp := by
  unfold SL003FC.Erdos1150.SL003.targetProp
  rintro ⟨c, hc, hev⟩
  have hc' : (0 : ℝ) < c := hc
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨N₀, -, hN₀⟩ := OAI.AsymptoticallyMinimalLittlewood.main (c / 2) (by linarith)
  have hD : (0 : ℝ) < c / 2 * (2 + 3 * c / 2) := by
    apply mul_pos <;> linarith
  obtain ⟨K, hK⟩ := exists_nat_gt ((1 + c / 2) ^ 2 / (c / 2 * (2 + 3 * c / 2)))
  have h1 : (1 + c / 2) ^ 2 < (K : ℝ) * (c / 2 * (2 + 3 * c / 2)) := (div_lt_iff₀ hD).1 hK
  obtain ⟨n, hnM, hnN, hnK⟩ : ∃ n : ℕ, M ≤ n ∧ N₀ ≤ n + 1 ∧ K ≤ n :=
    ⟨M + N₀ + K, by omega, by omega, by omega⟩
  obtain ⟨ε, hε, hbound⟩ := hN₀ (n + 1) hnN
  have hε' : ∀ k, ε k = -1 ∨ ε k = 1 := hε
  have hdeg := SL004.H56.poly_natDegree n ε hε'
  have hP := hM n hnM (SL004.H56.poly n ε)
    (fun i hi => by
      rw [hdeg] at hi
      rw [SL004.H56.poly_coeff n ε i (by omega)]
      exact SL004.H56.coeffFn_sign n ε hε' i (by omega))
    hdeg
  have hsup : (⨆ z : Metric.sphere (0 : ℂ) 1, ‖(SL004.H56.poly n ε).eval (z : ℂ)‖) ≤
      (1 + c / 2) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    haveI : Nonempty (Metric.sphere (0 : ℂ) 1) := ⟨⟨1, by simp⟩⟩
    apply ciSup_le
    intro z
    show ‖(SL004.H56.poly n ε).eval (z : ℂ)‖ ≤ _
    rw [SL004.H56.poly_eval]
    exact hbound z (by simpa using z.2)
  have hKn : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnK
  have hcmp : (1 + c / 2) * Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (1 + c) * Real.sqrt (n : ℝ) := by
    have hx : 0 ≤ (1 + c / 2) * Real.sqrt ((n + 1 : ℕ) : ℝ) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hy : 0 ≤ (1 + c) * Real.sqrt (n : ℝ) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hsq : ((1 + c / 2) * Real.sqrt ((n + 1 : ℕ) : ℝ)) ^ 2 ≤
        ((1 + c) * Real.sqrt (n : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hKn hD.le, h1]
    nlinarith [hsq, hx, hy]
  linarith [hP, hsup, hcmp]
