# SL-003 protocol (frozen)

**Title.** SL-003: a preregistered audit of 60 external Lean proof links cited by Formal Conjectures.

**Version 1.0.** Frozen in the commit that first contains this file. The sample does not exist at that
moment: its seed is the full SHA-1 of that commit (section 4), which cannot be known before the commit
is made. Amendments are appended at the end, dated, with whether outcomes had been seen.

## 1. Question

For a "solved" link in Formal Conjectures, does the cited Lean proof establish the repository's own
statement? Specifically, for each sampled link: (Q1) can the cited proof be retrieved and rebuilt from
pinned sources; (Q2) does the repository statement follow from the cited theorem directly, after a
mechanical bridge, after an AI-written bridge, or not at all on the evidence; (Q3) is there a certified
defect? Population-level: estimate the share of links in each outcome, with uncertainty.

## 2. Population (verified before freezing)

Formal Conjectures (google-deepmind/formal-conjectures, Apache-2.0) at
`da703a5f239f734a47ede2f4e99b9ccc9e644cb5` (2026-11-11T09:09:17Z). A **link** is one occurrence of
`formal_proof using lean4 at "<url>"` in any `.lean` file under `FormalConjectures/`, attached to the
next `theorem`/`lemma` declaration in the file (the **target**). Counts at the freeze commit: 1,173
`formal_proof` attributes; 997 of kind `lean4` (eligible); 174 `formal_conjectures` and 2
`other_system` (excluded: in-repository or non-Lean). The 997 eligible links attach to 975 distinct
targets. Hosts: github.com 961 (807 pinned to a 40-character commit), palomar-registry.org 19,
gist 10, erdosproblems.com 5, zenodo.org 1, other 1. `population.py enumerate` regenerates the list;
the count must be 997 or the run stops.

## 3. Unit and ordering

The unit is the link. Links are sorted by (file path, byte offset of the attribute) to fix an order
before sampling.

## 4. Sampling

Simple random sample without replacement of n = 60 from the 997 eligible links, drawn by Python's
`random.Random(SEED).sample(range(997), 60)` with `SEED` = the 40-character hex SHA-1 of the freeze
commit, as a string. No repository caps, no strata: every link has inclusion probability 60/997, so
estimates are unweighted. Links from the same target repository are not independent; uncertainty is
reported both as exact Clopper–Pearson 95% intervals (treating links as independent) and as a
cluster bootstrap over target repositories (2,000 resamples, seed fixed in `population.py`).
The sample is processed in drawn order.

## 5. Pinning

GitHub links with a commit in the URL use it. Links with a branch name are resolved to the last commit
on that branch at or before 2026-11-11T09:09:17Z. Gists are cloned as git repositories and pinned the
same way. Palomar links are resolved to the git source the entry names, if CI can read it. Other hosts
(erdosproblems.com forum, zenodo, personal sites) are `infrastructure_blocked: retrieval`.
A commit that no longer exists upstream is `infrastructure_blocked: retrieval`.

## 6. Locating the cited declaration

In order: the `theorem`/`lemma` whose header is at or immediately above the `#L` anchor line; else a
declaration in the file whose last name component equals the target's; else the only theorem in the
file. Otherwise `infrastructure_blocked: locate`.

## 7. Environment

The nearest directory at or above the cited file containing both `lean-toolchain` and
`lake-manifest.json` defines the environment: that Lean release (installed with elan) and that
project's dependencies, built with `lake` using the Mathlib cache. No environment is guessed. If none
exists, `infrastructure_blocked: environment`.

## 8. Transport of the target

The target statement is taken from Formal Conjectures at the freeze commit, together with the
definitions earlier in the same file. Permitted edits, all recorded per case:
(1) replace imports with `Mathlib` plus the cited module; (2) remove attributes and `module`/`public`
headers; (3) remove all other `theorem`/`lemma` blocks; (4) rewrite `answer(True) ↔ P` as `P`,
`answer(False) ↔ P` as `¬ P` (Formal Conjectures' own semantics); (5) if the cited project already
depends on Formal Conjectures, use its definitions instead of copies. Anything else makes the case
`infrastructure_blocked: transport`. A transported target that does not elaborate in the cited
environment is `infrastructure_blocked: transport` — never evidence about the mathematics.

## 9. Verification steps and the AI agent

For each case that builds: (a) axiom report of the cited declaration; (b) **direct**: `exact cited`
(definitional match); (c) **deterministic cascade**, fixed: `simpa using cited`, `exact_mod_cast cited`,
`simpa [<names of definitions in the transported block>] using cited`, `exact cited.1`, `exact cited.2`,
10 minutes total; (d) **AI bridge**: written by Claude (Anthropic), the assistant running this
experiment, given only the two statements, the definitions, and Lean error messages from CI. At most
2 compile attempts per case. No human writes or edits Lean. (e) every successful proof is replayed
with `leanchecker`; axioms must be within `propext`, `Classical.choice`, `Quot.sound`. If the cited
toolchain does not ship `leanchecker`, the outcome is recorded with replay marked unavailable (the
proof was still checked by the kernel during compilation) and such cases are counted separately.

## 10. Outcomes (exactly one per case)

| Outcome | Definition |
|---|---|
| `directly_verified` | step (b) succeeds |
| `auto_bridged_deterministic` | step (c) succeeds |
| `auto_bridged_ai` | step (d) succeeds |
| `human_assisted` | a human wrote or edited the bridge (expected: none; disclosed if any) |
| `certified_defect_link` | the build succeeds and the cited declaration's axioms include `sorryAx` or a non-standard axiom; or the anchor and name rules locate no declaration in a file that exists at the pin |
| `certified_defect_statement` | a kernel-checked proof of the negation of the transported target in the cited environment |
| `undecided` | builds and transports, but (b)–(d) fail within budget |
| `infrastructure_blocked` | with cause: retrieval, locate, environment, build, transport |

`certified_defect_link` means the link is wrong (the proof is incomplete or missing). It says nothing
about whether the conjecture is true. `certified_defect_statement` means the Formal Conjectures
statement is false as formalized. A build failure, a failed search or a textual difference is never a
defect.

A declaration whose statement differs from the target and cannot be bridged is `undecided`. For two
closed propositions "does not imply" cannot be certified unless the target is refuted, so no such
claim is made.

## 11. Baselines (same cases)

Reported per case: textual identity of statements after whitespace normalization (no prover);
`exact` (definitional equality); the deterministic cascade. Not run in v1.0 and reported as such:
SemantEq, BEq+ (their published code targets single-environment statement pairs; adapting them
is out of scope), Comparator, and an AI agent without the pipeline.

## 12. Budgets

Per case: build 60 minutes; cascade 10 minutes; AI 2 compile attempts. Total GitHub Actions budget:
public-repository free tier. Model cost: not metered separately (the agent is the session itself);
reported as compile attempts.

## 13. Decision rules

Let D = cases with a definite outcome (`directly_verified`, any `auto_bridged`, `human_assisted`,
either `certified_defect`). Let T = cases that build and transport.

* **STRONG SUCCESS:** ≥ 1 certified defect, and |D| ≥ 42 (70%).
* **SUCCESS (assurance):** no defect; ≥ 20% of T are not `directly_verified`; AI bridges ≥ 50% of
  those.
* **FAILURE (need):** ≥ 90% of T are `directly_verified`.
* **FAILURE (feasibility):** `infrastructure_blocked` > 30 (50%).
* **INCONCLUSIVE:** anything else; reported as such.

## 14. Threats to validity

The AI agent is also the experimenter, so it could in principle be unconsciously selective; the
2-attempt cap and processing in drawn order limit this, and every attempt is committed. Transport
across Mathlib versions can fail for reasons unrelated to the mathematics. Statements in Formal
Conjectures were revised after links were added; the frozen commit is used throughout. n = 60 gives
wide intervals. Links within a repository are correlated. Nothing here is reviewed by anyone outside
the project.

## 15. Disclosed pre-freeze inspection

Before freezing: the population counts above; the layout of `plby/lean-proofs` (largest target,
430 links; `src/<version>` projects with their own toolchain and manifest); the SL-002 cases (two
`openai/math` links, already bridged). No case was sampled and no bridge was attempted on any
population link other than the SL-002 pair before the freeze.

## Amendments

None.
