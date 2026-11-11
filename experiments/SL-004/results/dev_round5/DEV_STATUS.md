# SL-004 development status after round 5

Source: GitHub Actions run 43094411580 (Lean files of commit 04194d0, identical to the engine-freeze
commit ea1712a). Lean finished at 20:18–20:20 UTC. Artifact upload then hung and failed, and GitHub
finalised the jobs only at 21:01 UTC, after the freeze. The per-case summaries are the check-run
annotations in `annotations.tsv`, kept verbatim. The full Lean logs of this run were lost.

| Case | Correspondence class | Bridge | Proves target | Axioms | leanchecker | Uses cited |
|---|---|---|---|---|---|---|
| SL003-03 Erdős 581 | C1 greatest element (`IsGreatest.csSup_eq`) | `SL004.bridge03` | yes | standard | yes | yes |
| SL003-06 Erdős 441 | C1 greatest element (`sSup` vs `Finset.sup`) | `SL004.bridge06` | yes | standard | yes | yes |
| SL003-14 quantum graphs | T2 twin structure | `SL004.bridge14` | yes | standard | not shipped (v4.27) | yes |
| SL003-35 Erdős 737 | L logical repackaging | `SL004.bridge35` | yes | standard | yes | yes |
| SL003-40 Erdős 690 | C2 uniqueness of densities + set correspondence | `SL004.bridge40` | yes | standard | yes | yes |
| SL003-43 quantum graphs | T2 twin structure | `SL004.bridge43` | yes | standard | not shipped (v4.27) | yes |
| SL003-45 Erdős 1195 | T1 twin predicate + set extensionality | `SL004.bridge45` | yes | standard | yes | yes |
| SL003-55 Erdős 841 | C1 least element (`IsLeast.csInf_eq`) | `SL004.bridge55` | yes | standard | yes | yes |
| SL003-59 (regression) | T1 twin recursion (`with_unfolding_all rfl`) | `SL004.bridge59_twin` | yes | standard | yes | yes |
| SL003-15 | D directional | `SL004.relation15 : PiIrrBound → target` (relation, not a bridge) | n/a | standard | yes | yes |
| SL003-16 Erdős 690 | C2 + set correspondence | **unresolved**: `corr690_kth` certified; `B01_bridge.lean` failed to compile, error text lost with the logs | | | | |
| SL003-00, 10, 50 | not attempted (need new mathematics) | undecided | | | | |

Development total: **8 nontrivial certified transports** (03, 06, 14, 35, 40, 43, 45, 55), all written by
the AI layer (Claude). The automatic layer certified 1/14 (SL003-59, a verbatim twin). SL003-40 was
certified by a run whose results became visible only after the freeze. Its Lean files were already
fixed before the freeze, and the frozen engine does not depend on it.
