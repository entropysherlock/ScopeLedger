# SL-005 contamination audit (round 1)

Method: each control agent's full transcript was scanned mechanically (pattern counts and tool-call
inputs only). The orchestrator did not read the agents' reasoning.

| | opus control | sonnet control |
|---|---|---|
| Tool calls | Bash 53, Write 13, Edit 2, Read 1 | Bash 45, Write 1, Read 1 |
| Paths outside its package in tool inputs | none (only its own clones of the cited repositories, Mathlib, and raw GitHub files) | none |
| SL-004 solution strings (`bridgeH`, `corrH`, `psiH41`, `with_unfolding_all`, `SL004Lib`, `TRANSPORT_PROCEDURE`, "correspondence class", "Layer B") | 0 | 0 |
| "ScopeLedger"/"entropysherlock" in tool traffic | only in its own TASK.md (the instruction not to look) | none |
| Tokens / tool uses / wall time | 288,005 / 70 / 18.2 min | 303,855 / 48 / 19.3 min |

Residual exposure:
- Both agents' system context contained the user-memory snapshot. Its file listing includes a one-line
  description of the ScopeLedger project ("open evidence-ledger project for AI-assisted mathematics"). It
  contains no solution content.
- Session metadata (the working-directory field) names the ScopeLedger clone.
- Shared model training data cannot be audited.
- The opus control is likely the same model family as the treatment agent.
