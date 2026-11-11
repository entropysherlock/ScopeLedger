# SL-005 report: does ScopeLedger's structured transport procedure beat ordinary AI proof development?

Author: Caleb J. Westfall. Orchestration and analysis: Claude (Anthropic). 2026-11-11.
Protocol: [PROTOCOL.md](PROTOCOL.md). Blind control package: [control_package/](control_package/).
Audit: [AUDIT.md](AUDIT.md). Numbers: [results/summary.json](results/summary.json). Every compile log is
on branch `sl005-ci` (`control-results/round<k>/<agent>/<case>/`).

## Answer

**No measurable advantage.** On the same 13 held-out cases that standard Lean automation could not
certify, two fresh AI agents with no procedure each certified **10**. The structured treatment
(SL-004 Layer B) certified **9**, one of them by reusing an SL-002 proof. All three arms used the same
harness, the same pinned environments, the same acceptance checks and the same budget (2 rounds × ≤3 files).

## Paired results

| Case (repository) | Treatment | Opus control | Sonnet control |
|---|---|---|---|
| H-05 Erdős 482 (gotrevor/lean-gallery) | declined | declined | declined |
| H-10 Erdős 534 (plby) | ✓ round 2 | ✗ | ✓ |
| H-15 Erdős 673 (plby) | ✗ | **✓** | **✓** round 2 |
| H-18 Erdős 354 (Andrewyzzz/erdos354) | declined as "new mathematics" | **✓** | **✓** round 2 |
| H-20 Erdős 522 (KitaKen1) | ✓ | ✓ round 2 | ✓ round 2 |
| H-21 Erdős 841 (plby) | ✓ | ✓ | ✓ |
| H-27 Erdős 865 (mrricky22) | ✓ | ✓ | ✓ |
| H-31 Erdős 136 (plby) | ✓ | ✓ | ✓ |
| H-41 quantum graphs (KitaKen1) | ✓ | ✓ | ✗ |
| H-45 Erdős 49 (plby) | ✓ round 2 | ✓ | ✓ |
| H-54 Kourovka 21.149 (pitmonticone) | declined | declined | ✗ (see below) |
| H-56 Erdős 1150 (openai/math) | ✓ reuse of SL-002 | ✓ from scratch | ✓ from scratch |
| H-58 Erdős 274 (Jostamon) | ✓ | ✓ | ✓ |
| **Certified of 13** | **9** (8 new; CP 95% 39–91%) | **10** (46–95%) | **10** (46–95%) |

Discordant pairs:

| Comparison | Treatment only | Control only | Exact McNemar p |
|---|---|---|---|
| Treatment vs opus | H-10 | H-15, H-18 | 1.0 |
| Treatment vs sonnet | H-41 | H-15, H-18 | 1.0 |

At least one control certified **11 of 13**, every case except H-05 and H-54. H-05 is impossible from the
cited theorem, and all three arms said so independently.

**H-54.** Sonnet's bridge compiles, proves exactly the transported target with standard axioms, and
passes `leanchecker`. It fails only the dependency check, because the frozen harness records the cited
name as `KourovkaNotebook.Solution21_149.kourovka_21_149`, while the declaration is the root-level
`kourovka_21_149`. Sonnet found and used the real name. The same defect made the treatment decline the
case. It is not counted for anyone.

## Cost and intervention

| | Treatment | Opus control | Sonnet control |
|---|---|---|---|
| Inference | not metered (in-session) | ~288k tokens, 70 tool calls, 18 min (round 1); round 2 54 s | ~304k tokens, 48 tool calls, 19 min (round 1); round 2 62 s |
| Compiler | 2 CI rounds | 2 CI rounds | 2 CI rounds |
| Human-written Lean | none | none | none |

## What this means

- The SL-004 gain over standard automation (19 → 28 of 32 held-out links) is real, but it is the gain of
  **an AI agent writing Lean with compiler feedback**, not of ScopeLedger's correspondence classes or
  transport procedure.
- Unstructured agents matched the treatment on 8 shared successes. They also solved H-15, which the
  treatment failed twice, and H-18, which the treatment had declined. The procedure may have narrowed
  the treatment agent's view of what was provable.
- The correspondence taxonomy is still a useful *description* of the gaps, and the controls' proofs fall
  into the same classes. But the evidence does not show that it *helps produce* proofs.
- The combined empirical result is: in this held-out sample, AI agents with Lean compiler feedback
  certify about 30 of 32 transportable "solved" links (19 by automation plus 11 by agents). That is a
  statement about current AI proof development, not a new method.

## Limitations

- Retrospective, not randomized. The treatment results were known before the controls ran, and n = 13.
  No difference here is causal in either direction.
- Contamination (see [AUDIT.md](AUDIT.md)):
  - no control touched anything outside its package, and no solution content appears in either
    transcript;
  - both saw a one-line description of the ScopeLedger project in their system context;
  - the opus control is likely the same model family as the treatment agent;
  - shared training data cannot be audited.
- The treatment agent was the orchestrator's own session, with its broader context. The controls were
  fresh sessions with a narrower context. Context differences cut both ways.
- Compiler feedback was relayed by the orchestrator as raw files written by a script, unedited.

## Level 3 decision

**C. LEVEL 2.**
- **Why:** the advantage of ScopeLedger's structured transport over standard automation is fully
  explained by ordinary AI-assisted Lean proof development. Independent unstructured agents did at least
  as well on identical cases, environments, checks and budgets.
- **What survives:** ScopeLedger's verified infrastructure, a pinned and replayable acceptance harness
  with a dependency check and the controlled comparison itself. Also the empirical measurements from
  SL-003 to SL-005, and the finding that most solved-claim gaps in Formal Conjectures are closable, with
  kernel-checked proofs, by current AI agents.
- **What does not survive:** the claim that the correspondence-class procedure is a new method that
  improves proof production.
