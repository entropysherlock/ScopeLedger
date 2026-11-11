import SL003Target

/-! SL-003 AI attempt 1 (Claude). The target refutes "for every k ≥ 2 and every A, some z has no
unique representation in A + {x^k}" (with x^k written as the evaluation of the polynomial X^k). The
cited theorem gives, for k = 6, a set A with a unique representation of every integer. No human
edits. -/

theorem SL003.ai1 : SL003FC.Erdos477.SL003.targetProp := by
  unfold SL003FC.Erdos477.SL003.targetProp
  intro H
  obtain ⟨A, hA⟩ := Erdos477.erdos477_sixth_power
  obtain ⟨z, hz⟩ := H 6 (by norm_num) A
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at hz
  apply hz
  obtain ⟨p, hp, huniq⟩ := hA z
  refine ⟨p, ⟨Set.mem_prod.mpr ⟨hp.1, hp.2.1⟩, hp.2.2.symm⟩, ?_⟩
  rintro q ⟨hq, hqz⟩
  exact huniq q ⟨(Set.mem_prod.mp hq).1, (Set.mem_prod.mp hq).2, hqz.symm⟩
