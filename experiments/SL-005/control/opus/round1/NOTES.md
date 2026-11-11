# Round 1 notes

Each submitted case has one file, `Bridge.lean`, whose final theorem is `SL004.bridge_main`.

## Cases with no submission

### H-05 (Erdős 482, `erdos_482.variants.stoll_general`): no file
The cited theorem `LeanGallery.NumberTheory.Erdos482.Statement.statement_cor33_unconditional` is one
concrete instance. It fixes base 2, the single real `759250125 * √2`, and the specific recurrence
parameter `1 - π^2 / e^3`, and it holds only for indices `m + 31`.
The target is Stoll's general theorem: for **every** base `g ≥ 2` and **every** `w > 0` there exist
`a, b, ε` with `a * b = g` such that the recurrence produces the base-`g` digits of `w` for all
`n ≥ 1`. A single instance cannot imply a statement quantified over all `g` and all `w`. Proving the
general statement independently would not use the cited theorem, which the task forbids. I judge
this case impossible.

### H-54 (Kourovka 21.149, `variants.not_inner`): no file
1. The cited constant `KourovkaNotebook.Solution21_149.kourovka_21_149` does not exist in the
   pinned environment. `exact_attempt_error.log` reports "Unknown identifier", and `explore.log`
   shows the same. At the pinned commit, the source declares the theorem as
   `theorem _root_.kourovka_21_149` (Kourovka/Problem_21_149.lean, line 768), so its real name is
   the root-level `kourovka_21_149`. A bridge therefore cannot refer to the cited theorem under its
   recorded name.
2. Even using `_root_.kourovka_21_149`, the bridge would be a large formalization:
   - The cited Dlab group is a subgroup of `unitInterval ≃o unitInterval`. The target needs a
     subgroup of `ℝ ≃o ℝ` that satisfies one of the six membership characterizations in
     `IsDlabGroup`.
   - That requires building the extension-by-identity embedding `IntervalAut →* (ℝ ≃o ℝ)` and
     proving it is a strict-mono bijection and a group hom.
   - It requires proving the exact image characterization, which compares neighbourhood filters
     in `unitInterval` and in `ℝ` and right-linearity at every real point.
   - It requires relating `FirstDisagreementLt` and the order `o` to the transported `DlabLt`.
   - It requires transporting non-innerness across the isomorphism.

   I did not attempt this without a compiler.

## Assumptions per submitted case
- H-10: `Erdos534.candidate` and `SL003FC...ahlswedeKhachatrian` agree elementwise, and `Admissible`
  is definitionally `IsAdmissible`. `maxCard` (an `sSup`) is attained by the candidate.
- H-15: assumes `Nat.nth (· ∣ n) (i + 1)` in the transported `G` uses natural-number addition
  `↑i + 1` (the default elaboration with expected type `ℕ`). For `n ≥ 1`, `Nat.nth (· ∣ n)` agrees
  with `n.divisors.orderEmbOfFin` via `Nat.nth_eq_orderEmbOfFin`.
- H-18: proves sequence completeness from strong completeness of `range \ {0}`, using an empty
  exceptional set and choosing one index per value.
- H-20, H-58: the transported structures are field-for-field copies, so the proof repackages them.
- H-21: `K = 20`. Transported `t` (`sInf`) equals cited `t` (`Nat.find`).
- H-27: `C' = C/8 + 1`.
- H-31: the `Is45Coloring` predicates may differ only in their `DecidableEq` instance (`convert`).
- H-41: the cited side is the root namespace `MonochromaticQuantumGraph` from Formal Conjectures
  (pinned dependency `f7349f3`), whose definitions match the transported copy verbatim. The proof
  does structural recursion on the fuel, with `rfl` for the unfolding equations.
- H-45: `g N` is attained (`Nat.sSup_mem`). `MonotoneOn` is definitionally `TotientMonotoneOn`.
- H-56: `η = c/2`, and `n` is chosen large via `exists_nat_gt`. Uses the Mathlib names
  `Polynomial.finsetSum_coeff` and `Polynomial.eval_finsetSum`. If these are missing in the pinned
  Mathlib, the fallback is the older `finset_sum_coeff` / `eval_finset_sum`.
