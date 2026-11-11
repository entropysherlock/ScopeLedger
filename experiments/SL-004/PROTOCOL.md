# SL-004 protocol: theorem transport across independently built definitions

Author: Caleb J. Westfall. Engineering: Claude (Anthropic). Version 1.0, committed before any
development result exists.

## 1. Question

SL-003 found that most cited Lean proofs cannot be checked against the Formal Conjectures (FC)
statement with `exact`. The main reason is that the cited project re-implements FC's definitions,
which then differ from FC's in construction while agreeing in meaning.

Question: can one fixed, reusable procedure turn such links into kernel-checked bridges? The procedure
must:
1. align the definitions;
2. prove correspondence lemmas between them;
3. rebuild the theorem-level bridge from those lemmas;

and it must reject any correspondence it cannot prove.

## 2. Phases

**Development (D).** The 13 SL-003 `undecided` cases, with SL003-59 as a regression test (it is already
certified in SL-003). Development is unrestricted, but every attempt and log is kept, on the `sl004-ci`
branch under `dev-results/<run>/`. A success counts only if it passes the SL-003 acceptance checks:
- type guard (proves exactly the transported target);
- standard axioms only;
- `leanchecker` replay;
- the proof term uses the cited theorem.

Scoped results (`SL004.relation*`, `SL004.corr*`) are reported with their exact statements. They never
count as proving a target.

**Freeze.** The engine (code, tactic and strategy library, AI budget) is frozen by a commit that adds
`experiments/SL-004/ENGINE_FROZEN`. Nothing in the engine changes afterwards. A defect found later is
reported, not fixed, for this evaluation.

**Held-out evaluation (H).**
- Population: the 997 SL-003 links minus the 60 SL-003 sampled links.
- Sample: `random.Random(SEED).sample(...)` without replacement, n = 60, with SEED = the full SHA of the
  freeze commit. This guarantees the sample did not exist while the engine was developed.
- Processing: Stage A of SL-003, then Stage B, then the engine, all frozen.
- Target: at least 30 of the 60 links reach a buildable, transported target. If fewer do, every one is
  still reported, and the evaluation is described as smaller than planned.

## 3. Baselines on H (identical cases and environments)

1. `exact` (SL-003 Direct).
2. The SL-003 pipeline (Direct + fixed cascade).
3. Mathlib general automation, under the same per-case time budget:
   - `convert <cited> using 3` followed by `all_goals rfl`;
   - `aesop` with the cited theorem added;
   - `exact?` (5-minute limit).
4. Engine, automatic: no AI.
5. Engine + AI fallback, budget fixed at freeze. AI-written text is labelled as such. Human-written
   Lean is never counted as automatic.

SemantEq, BEq+ and Comparator are reported as not run unless they are run on the same cases.

## 4. Measures

Over H:
- certified coverage, with Clopper–Pearson and repository-cluster bootstrap intervals;
- human intervention (expected: none);
- false certifications, i.e. any accepted bridge that fails an acceptance check on independent replay
  (expected: none, by construction);
- runtime per case;
- failures, by stage and cause.

## 5. Level 3 claim conditions (from the mission)

A precise new method, Lean-checked certificates, nontrivial successes on held-out cases from
independent repositories, an advantage over the baselines, reproducible CI, and a novelty audit. If
these conditions are not met, the report says so and names the strongest defensible alternative.
