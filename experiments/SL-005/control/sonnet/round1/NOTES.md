# Round 1 notes

Nothing could be compiled here, so every file below is untested. Most proofs are definitional-unfolding
bridges, and the places most likely to need a round-2 fix are called out per case.

## H-05 (Erdos 482): NO submission
The cited theorem `statement_cor33_unconditional` is only Stoll's Cor 3.3 instance. It says that one specific
sequence (`vv` with `epsilon = 1 - pi^2/e^3`) reads off the binary digits of `759250125 * sqrt 2`.
The transported target quantifies over every base `g >= 2` and every real `w > 0`, and asks for coefficients
`a, b, epsilon`. A single numerical instance cannot imply that, so the cited theorem does not imply the target.
The same module has a sibling theorem, `LeanGallery.NumberTheory.Erdos482.General.erdos482_resolution`
(re-exported as `Statement.statement_erdos482_resolution`). Its statement has the shape of the target, with
`gu` in place of `generalRecurrence`. I did not submit a bridge from it, because it is not the cited theorem
and I did not want to add a vacuous dependency on the cited one just to pass the "must use the cited theorem" check.

## H-10 (Erdos 534)
Straight transport. The helper `ak_eq` shows `ahlswedeKhachatrian = candidate`, using `rfl` with an `ext`/`simp`
fallback. `IsAdmissible` and `Admissible` are `Iff.rfl`. `maxCard` is shown to equal the cardinality via `IsGreatest.csSup_eq`.

## H-15 (Erdos 673 ii)
The cited theorem gives the `IsEquivalent` for `GSum`. The two `G`s differ: the transported one uses
`Nat.nth (. | n) i`, the cited one uses `divisors.orderEmbOfFin`. I bridge them with
`Nat.nth_eq_orderEmbOfFin`. This assumes the target's `Nat.nth _ (i + 1)` elaborated as `↑i + 1` in `ℕ`, and
there is a `first` fallback for the `Fin`-addition reading.

## H-18 (Erdos 354 i)
From `IsAddStronglyComplete (range w \ {0})` I take `B = ∅` to get `IsAddComplete`, then show
`subsetSums (range w \ {0}) ⊆ subseqSums' w` by choosing one index per value. The transported `interleave`
is replaced by the cited one via `interleave_eq` (`rfl`).

## H-20 (Erdos 522 zero_one)
The transported `KacCoefficients` is rebuilt as the cited one by copying the three fields, and the cited
`True ↔ ...` is used with `.mp trivial`. This relies on `numRootsInUnitDisk` being definitionally equal
across the two copies, and a fallback `simp only [hcount]` is included.

## H-21 (Erdos 841 many_small_values)
`K = 20`. The transported `t` (defined with `sInf`) is shown equal to the cited `t` (defined with `Nat.find`).
The `manySmallUpTo` finset is rewritten to the transported filter.

## H-27 (Erdos 865)
Take `C' = C/8 + 1`. Then `|A| >= 5N/8 + C'` gives `8|A| > 5N + C`, which contradicts the cited
bound unless `A` has a triple. `HasTriple` is definitionally the target's triple condition.

## H-31 (Erdos 136)
`Is45Coloring` differs only in the `DecidableEq (Fin k)` instance used in `Finset.image`. A `convert` handles
it, with `Iff.rfl` tried first. `f = sInf` is shown equal to `erdos136Fun = Nat.find`.

## H-41 (Monochromatic quantum graph, N=8, D=3)
The transported `EdgeN`, `WeightsN`, `pmSumListAux` and the rest are copies of the cited ones in a different
namespace, so I transport weights `W ↦ W ∘ (cited edge → transported edge)`. I prove equality of the
`pmSumListAux` recursions by induction on the fuel, and equality of `vertices` and `allEqual`. This assumes
the cited (Formal Conjectures) definitions are textually the same as the transported copies, which I could not
check because that file is a dependency that is not in the cloned repository.

## H-45 (Erdos 49 Tao)
`g N` is a `sSup` of a bounded nonempty set of naturals, so `Nat.sSup_mem` gives a witness `A`.
`MonotoneOn totient ↑A` is converted to `TotientMonotoneOn A`, and the cited `QuantitativeResolution` applies.

## H-54 (Kourovka 21.149), 2 files
`case.json` names the cited theorem `KourovkaNotebook.Solution21_149.kourovka_21_149`, but in the source it is
declared `_root_.kourovka_21_149`. I use the root name. The cited model is a Dlab group of order automorphisms of
`[0,1]`. The target uses subgroups of `ℝ ≃o ℝ`. `A_Infra.lean` extends interval automorphisms by the identity
to `ℝ` (`extFun`, `extOrd`, `extHom`) and proves:
- `Gr K` (the image) satisfies the first disjunct of `IsDlabGroup`, in both directions of the iff.
- `DlabLt` on the image is equivalent to the cited `FirstDisagreementLt`.
`B_Bridge.lean` transports the cited order automorphism and the non-innerness. This is the longest and riskiest
proof here; the Mathlib API names it uses (`Subgroup.equivMapOfInjective`, `map_le_map_iff`, ...) are unchecked.

## H-56 (Erdos 1150 / Littlewood)
The target is read as `(⨆ z, ‖P z‖) > (1+c) * sqrt n`, which is how `⨆`'s binder precedence parses.
A cited polynomial with `n+1` signed coefficients is built, of degree `n`, with `η = c/2`. Then
`(1+c/2) sqrt(n+1) <= (1+c) sqrt n` for large `n` contradicts the "eventually" in the negated target.

## H-58 (Erdos 274 abelian)
The transported `Group.ExactCovering` is rebuilt as the cited one field by field. Both universe parameters are kept.
