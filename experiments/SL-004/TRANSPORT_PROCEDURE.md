# SL-004 transport procedure (frozen with the engine)

The engine has two layers. Every result from either layer is accepted only by the same checks:
- the type guard (it proves exactly the transported FC statement);
- standard axioms only;
- `leanchecker` replay, where the toolchain ships it;
- the proof term uses the cited theorem.

## Layer A: automatic (no model, no human)

`engine.py`, a fixed portfolio of 37 candidates per case. Lean decides which, if any, succeed.
1. **Twin exact:** `with_unfolding_all exact cited`.
2. **`True ↔ P` unwrapping.**
3. **Anti-unify, then close:** for each projection of the cited statement (none, `.1`, `.2`, … depth 4)
   and each depth k = 1..4, `convert cited using k`. Every residual goal is then closed by the fixed
   closer:
   - `rfl`, then `with_unfolding_all rfl` (twin definitions, including well-founded recursion);
   - `simp`;
   - the least-element characterisation `sInf {n | P n} = Nat.find h`.
4. **Logical normalisation** of both statements (`True ↔`, eventual bounds, `≥`/`>`, bounded
   quantifiers), then exact / twin exact / convert.

## Layer B: AI-assisted (Claude), fixed budget

**Inputs**, the same for every case:
- the transported target;
- the cited statement;
- the automatic exploration log (`Z_explore.log`: every identifier on both sides, printed in the cited
  environment);
- the Layer A and baseline errors;
- the cited repository's source at the pinned commit.

**Method.** Classify each mismatch into one correspondence class, then write the correspondence lemmas
(`SL004.corr*`) and the bridge (`SL004.bridge*`) from that class's pattern:

| Class | Pattern |
|---|---|
| T1 twin definition | `with_unfolding_all rfl` |
| T2 twin structure | pull back along the field-copying map, then T1 for everything defined over it |
| C1 extremal characterisation | `IsLeast.csInf_eq` / `IsGreatest.csSup_eq` with the project's own spec lemmas or `SL004Lib` |
| C2 uniqueness | a quantity FC quantifies over is pinned by uniqueness (limits, densities) to the cited one |
| L logical repackaging | projections, existential witnesses, `∀ᶠ` ↔ `∃ N ∀ n ≥ N`, set extensionality from a pointwise characterisation, casts |
| D directional only | the cited theorem has an extra hypothesis H; certify `H → target` as `SL004.relation*`, never as a bridge |

A class is a hypothesis about the mismatch, not a claim. Only Lean decides.

**Budget per case.** At most two submission rounds after the automatic run, and at most three candidate
files per round. No human-written Lean. A case still open after two rounds is `undecided`.

**Reporting.** Layer A and Layer B coverage are reported separately. Layer B is never described as
automatic.
