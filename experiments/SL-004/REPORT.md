# SL-004 report: theorem transport across independently built definitions

Author: Caleb J. Westfall. Engineering, AI layer and analysis: Claude (Anthropic). 2026-11-11.
Protocol: [PROTOCOL.md](PROTOCOL.md). Engine frozen at commit `ea1712a8a206bc311e1bf74b3b91cf8ec94fdce2`
([ENGINE_FROZEN](ENGINE_FROZEN)). That SHA is the seed of the held-out sample.

## 1. Result in one paragraph

On a preregistered held-out sample of 60 external Lean proof links cited by Formal Conjectures (drawn
after the engine was frozen; 30 repositories), 32 links reach a buildable, transported target.
- Standard Lean automation certifies 19 of the 32: `exact`, `convert`, `aesop`, `exact?`.
- The frozen **automatic** transport engine certifies the same 19 and **nothing more**.
- An **AI layer** working under a fixed procedure certifies 9 more. It is Claude, writing correspondence
  lemmas by class, with at most 2 rounds per case and no human-written Lean. 8 of the 9 are new; 1 reuses
  an SL-002 proof.

That gives **28 of 32 certified (87.5%; 95% CI 71–97%)**, against 19/32 for the baselines (59%; 41–76%).
- Every certificate proves exactly the transported statement, uses only the standard axioms, and depends
  on the cited theorem.
- Every certificate is replayed by `leanchecker` where the project's toolchain ships it (2 do not).
- No false certification was observed.

In development, the same AI layer certified 8 of the 13 SL-003 cases that `exact` and the cascade could
not decide. SL003-40 was confirmed independently on Google Colab.

## 2. What was established

**Correspondence classes** (each a fixed proof pattern; Lean decides every instance):

| Class | Pattern | Certified instances |
|---|---|---|
| T1 twin definition | definitions compiled from the same source agree by `with_unfolding_all rfl`, including well-founded recursion | SL003-45, SL003-59 (regression), H-10 (part) |
| T2 twin structure | a re-declared `structure` is rebuilt field by field; dependent definitions then agree definitionally | SL003-14, SL003-43, H-20, H-41, H-58 |
| C1 extremal characterisation | FC's `sSup`/`sInf` equals the project's `Finset.sup`/`Nat.findGreatest`/`Nat.find` value once that value is shown greatest/least (`IsGreatest.csSup_eq`, `IsLeast.csInf_eq`, `SL004Lib`) | SL003-03, SL003-06, SL003-55, H-10, H-21, H-31 |
| C2 uniqueness | a quantity FC quantifies over is pinned to the cited one (uniqueness of limits/densities) | SL003-40 |
| C3 bounded supremum | FC's `sSup` is attained (`Nat.sSup_mem`), so the cited uniform bound applies | H-45 |
| L logical repackaging | projections, witnesses, contraposition with constant adjustment, `∀ᶠ` ↔ `∃ N ∀ n ≥ N`, set extensionality from a pointwise characterisation, casts | SL003-35, SL003-45, H-21, H-27 |
| D directional only | the cited theorem carries an extra hypothesis H; only `H → target` is certified, as a relation | SL003-15 (`PiIrrBound → target`) |

**Certificates.** Development: 8 bridges (SL003-03, 06, 14, 35, 40, 43, 45, 55) plus the SL003-59
regression ([results/dev_round5/DEV_STATUS.md](results/dev_round5/DEV_STATUS.md),
[results/colab_SL003-16_40](results/colab_SL003-16_40)). Held-out: 9 bridges (H-10, 20, 21, 27, 31, 41,
45, 58, and H-56, which reuses SL-002) in `heldout_ai/`. Logs for every attempt are on branch `sl004-ci`.

## 3. Held-out evaluation (frozen engine, no tuning)

| | n | Note |
|---|---|---|
| Sampled | 60 | 30 repositories; seed = freeze SHA; CI regenerated the sample byte for byte |
| Reached Stage B | 46 | 6 locate, 4 environment, 4 retrieval blocked in Stage A |
| Evaluated | 46 | H-47 (Gerver sofa project): build exceeded the frozen 60-minute budget, `infrastructure_blocked: build` |
| Transported target elaborates (T) | 32 | 10 `target_failed` (mostly FC utility definitions absent from the cited environment), 2 transport, 2 build |
| `exact` | 17 / 32 | |
| Any baseline (`exact`, `convert … <;> rfl`, `aesop`, `exact?`) | 19 / 32 | |
| Frozen automatic engine (37 strategies) | 19 / 32 | **+0 over the baselines** |
| AI layer (Layer B), round 1 + round 2 | +9 (8 new) | 7 in round 1, 2 in round 2 |
| **Total certified** | **28 / 32** | open: H-15 (two rounds failed); declined: H-05 (cited theorem is a special instance), H-18 (needs new mathematics), H-54 (harness name defect) |

Independent repositories with AI-layer certificates: plby/lean-proofs, KitaKen1/erdos-522-strong-law,
KitaKen1/monochromatic-quantum-graphs-lean, mrricky22/erdos-865-lean, Jostamon/erdos274-hs-abelian,
openai/math (reuse).

## 4. Baselines and resources

| Method | Certified on T (32) |
|---|---|
| `exact` | 17 |
| `convert … using 3 <;> rfl` | ⊆ 19 |
| `aesop` (cited theorem in context) | ⊆ 19 |
| `exact?` | ⊆ 19 |
| Automatic engine (twins, anti-unification, normalisation) | 19 |
| Engine + AI layer | 28 |

**Not run:** SemantEq, BEq+, Comparator (an identical-statement check, so by construction at most the
`exact` cases), and **an AI agent without the procedure**. The last one is the decisive missing control.
Runtime per case was 5–9 minutes on a GitHub runner, almost all of it Mathlib cache and project build.
AI bridges compiled in seconds. Human-written Lean: none.

## 5. Novelty audit (hostile)

- **The mathematics is standard.** `IsGreatest.csSup_eq`, `Nat.sInf_def`, definitional unfolding and
  field-copying maps are textbook Lean. No new theorem is claimed.
- **Transfer frameworks exist.** Trocq (Coq), Isabelle's Lifting/Transfer, and Mathlib's `Equiv`
  transfer and `equiv_rw` all transport along correspondences *declared and proved by the user*.
  Gauthier and Kaliszyk align concepts across libraries without proofs.
- **What is new here is empirical.** First, independently formalised "solved" claims mostly fail exact
  matching because the definitions were rebuilt under the same names. Second, those gaps fall into a few
  classes whose correspondences can be *proved*. Third, on a held-out preregistered sample, an AI agent
  following that procedure certifies 8 links that standard automation does not, with no false
  certification.
- **The automatic engine is not a contribution.** It adds nothing over existing tactics on held-out
  data.

## 6. Threats to validity

- The AI layer is the same agent that designed the procedure, and its budget allowed exploration logs
  and reading the cited sources. Its success measures *agent + procedure*, not the procedure alone.
- n = 32 transported cases. plby/lean-proofs contributes many of them.
- Two toolchains lack `leanchecker`, so those certificates rest on the elaborator plus the axiom check.
- 13 held-out links did not reach a transported target. Coverage claims are about T, not about all 60.

## 7. Verdict

**LEVEL 3 CANDIDATE.**
- **Met:** machine-checked certificates (17 nontrivial transports across development and held-out
  data), generalisation to held-out cases from independent repositories, an advantage over standard
  automation (28 vs 19 of 32), reproducible CI with every log, and no false certifications.
- **Not met:** a new general *method*. The automatic layer failed, and the AI layer's advantage has not
  been measured against an AI agent working without the procedure.

**Next steps for Level 3:**
1. Run the AI-without-procedure baseline on the same 13 non-baseline cases, with the same budget.
2. Have a second model or person apply the frozen procedure.
3. Replay every certificate in a clean, independent environment.
