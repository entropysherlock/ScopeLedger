# SL-005: controlled comparison of structured and unstructured AI theorem transport

Author: Caleb J. Westfall. Orchestration: Claude (Anthropic). Date: 2026-11-11.

## Question
SL-004's AI layer (Layer B) used ScopeLedger's frozen procedure: correspondence classes, the `SL004Lib`
library, 2 rounds of at most 3 files. It certified 9 of the 13 held-out cases that standard automation
did not. Does that advantage survive comparison with AI agents that write Lean bridges *without* the
procedure?

## Design (retrospective, not randomized)
- **Cases:** the 13 SL-004 held-out cases not certified by any baseline: H-05, 10, 15, 18, 20, 21, 27, 31,
  41, 45, 54, 56, 58. Stage A records are CI's, copied unchanged into `stage_a/`.
- **Treatment B** = SL-004 Layer B (frozen procedure at `ea1712a`), results as recorded in SL-004, not
  modified.
- **Control A** = fresh AI agents with no access to the ScopeLedger conversation, given only the blind
  package `control_package/`. Per case: the transported target file, `case.json` (cited theorem and
  statement, repository, pin, toolchain), the automatic `#print` exploration log, and the `exact`
  compiler error. The task text is `control_package/TASK.md`, verbatim.
  - **Excluded:** correspondence classes, the transport procedure, `SL004Lib`, all SL-003/SL-004 bridges
    and attempts, and all reports.
  - **Allowed:** cloning the cited repository at its pin (as Layer B was), and Lean/Mathlib documentation.
- **Two independent control agents**, reported separately: a general-purpose agent with model `opus`, and
  one with model `sonnet`. Each has its own package copy.
- **Same harness:** the frozen SL-004 runner (`experiments/SL-004/dev_run.py`) in the pinned environments,
  with the same acceptance checks (type guard, standard axioms, `leanchecker` where shipped, transitive
  dependency on the cited theorem). The same budget: 2 rounds × at most 3 files per case. Between rounds
  the orchestrator relays only the raw compiler logs of the agent's own files.
- **No human-written Lean.** No case is retried beyond 2 rounds.

## Contamination (disclosed, not eliminated)
- The orchestrator (Claude) knows the SL-004 solutions. It relays only raw logs and does not edit control
  files.
- The control agents run on the same machine as the ScopeLedger clone and this session's transcript, so
  isolation is by instruction. An audit after the run checks every file path the agents touched.
- The repository is public on GitHub. A control agent could find the SL-004 bridges if it ignored its
  instructions; the audit checks for this.
- The control models may share training data with the treatment model. The opus control and the
  treatment agent are likely the same model family.
- This is a retrospective comparison: the treatment results were known before the control ran. Any
  difference is an association between conditions, not a causal effect of the procedure.

## Outcome
Per case and per agent: certified or not, by the same checks as SL-004. Reported paired with the
treatment, with exact (McNemar-type) and Clopper–Pearson summaries.
