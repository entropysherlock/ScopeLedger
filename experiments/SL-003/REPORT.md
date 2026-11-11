# SL-003 report: a preregistered audit of 60 solved-claim links

Author: Caleb J. Westfall. Engineering and analysis: Claude (Anthropic). Date: 2026-11-11.
Protocol: [PROTOCOL.md](PROTOCOL.md), frozen at `e53ef139` before sampling, with four disclosed
amendments. Every number below is computed by [`analyze.py`](analyze.py) into
[`results/summary.json`](results/summary.json) from the committed per-case files.

## 1. Question and design

Formal Conjectures (commit `da703a5`) cites 997 external Lean proofs (`formal_proof using lean4 at
"<url>"`). For a simple random sample of 60 of them (seed = freeze commit SHA, no caps, unweighted, 21
repository clusters), we asked one question: does the cited Lean declaration establish the Formal
Conjectures (FC) statement it is attached to, as checked by Lean's kernel?

Pipeline per link:
1. **Stage A:** retrieve, pin and locate the declaration, and find its Lake environment (deterministic).
2. **Stage B:**
   - build the cited module and print the cited declaration's axioms;
   - transport the FC statement into that environment;
   - try `exact`, then a fixed tactic cascade;
   - then make at most two AI-written bridge attempts (Claude, no human edits).

A success must pass four checks:
- it proves exactly the transported target (type guard);
- it uses only standard axioms;
- it replays under `leanchecker`;
- a kernel dependency check shows the proof actually uses the cited theorem.

Runs (all on GitHub Actions; annotations kept under `results/`):

| Launch | Run | Status |
|---|---|---|
| 1 | 43063523513 | **invalid**: harness called `lean` outside the project (cancelled; amendment 2) |
| 2 | 43065022015 | frozen v1.0 transport: the **baseline** (`results/launch2_v1_transport/`) |
| 3 | 43071408322 | transport v1.1 (amendment 3), all 43 ready cases, AI attempt 1 for 4 cases |
| 4 | 43076587633 | AI attempt 1 for 5 cases, two of them re-run after a harness fix (amendment 4) |

## 2. Results (final, transport v1.1)

| Outcome | n / 60 | 95% Clopper–Pearson | 95% cluster bootstrap |
|---|---|---|---|
| Certified (any route) | **18** | 18.8–43.2% | 18.2–55.6% |
| … directly verified (`exact`) | 10 | 8.3–28.5% | 5.7–46.9% |
| … deterministic cascade | 1 | | |
| … AI bridge | 7 | | |
| Certified defect (link or statement) | **0** | 0–6.0% | |
| Undecided | 13 | | |
| Infrastructure blocked | 29 | 35.2–61.6% | 31.4–65.4% |
| … locate (file named, declaration not identified) | 12 | 10.8–32.3% | |
| … transport (FC statement does not elaborate in the cited environment) | 9 | | |
| … environment / build / retrieval | 3 / 3 / 2 | | |

Among the 31 links that build and transport (T):
- 18 are certified (58.1%, CP 39.1–75.5%).
- Only 10 are directly verified (32.3%, CP 16.7–51.4%).
- So **21 of 31 (68%) need a translation step beyond `exact`**: different packaging, extra or missing
  conjuncts, `True ↔ P`, implicit arguments, or re-implemented definitions.

Axioms: all 40 cited declarations that were built and checked use only `propext`, `Classical.choice`
and `Quot.sound`. None uses `sorryAx` (0/40; CP upper bound 8.8%).

AI bridges: 7 of 7 attempts succeeded on the first try (SL003-07, 09, 12, 24, 27, 32, 59). All are
kernel-replayed and all use the cited theorem. The agent declined 13 undecided cases whose bridges need
new mathematics (reasons in [`ai/DECLINED.md`](ai/DECLINED.md)).

**Decision rule (PROTOCOL section 13): INCONCLUSIVE.**
- There is no defect, so neither success rule's defect condition applies.
- The assurance rule needs AI to bridge at least 50% of the not-direct cases. It bridged 7 of 21
  (33%), because 13 were not attempted.
- Direct verification is 32% of T, far below the 90% that would show there is no need for the tool.
- Blocked cases (29) are just under the feasibility-failure line (more than 30).

Per-case outcomes are in section 6.

## 3. Findings

**F1. Exact-statement checking misses most real links.** Under the frozen v1.0 transport (launch 2)
no link was accepted as directly verified (0 of 44 Stage B cases). Two did compile directly but were
lost to the replay bug fixed in amendment 3 (SL003-11, 13). Under v1.1, `exact` closes 10 of 31.
Every text-identical link that built and transported was directly verified (8/8), and `exact` added
two more (SL003-13, 19). The remaining
21 need translation:
- 7 were closed by short AI bridges, which drop extra conclusions, unwrap `True ↔ P`, repackage a
  structure, or dispose of a degenerate case (SL003-32: a set containing 0).
- 13 need a real equivalence between two independently built definitions.

**F2. Same names do not mean the same definitions.** In 17 of the 31 transported cases, the cited
project declares definitions under FC's own names. Of the name-matched definitions, some are
definitionally equal to FC's and many are not. For example:
- SL003-06 `g`: `sSup {k | …}` in FC, `(candidates N).sup card` in the project;
- SL003-59 `a`: identical source text, but a separately compiled well-founded recursion, which is never
  `rfl`-equal.

A checker that matches names, or compares statement text, would treat these as the same object. The
kernel does not. *Limitation:* the `rfl` check compares `@FC.x` with `@_root_.x`, so a polymorphic
project copy (SL003-07's `IsErdosLovaszFamily`) shows as `not_rfl` even though its instance at `ℕ`
unfolds to FC's. The `not_rfl` counts are an upper bound on genuine divergence.

**F3. A conditional proof is attached to an unconditional statement (SL003-15).** For the Borwein sine
series:
- The cited theorem is `PiIrrBound → Summable …`. `PiIrrBound` is an irrationality-measure bound for π
  (μ(π) ≤ 7.10321, from Zeilberger–Zudilin, arXiv:1912.06345) that the repository assumes and does not
  prove.
- FC's `formal_proof` attribute attaches the link to the unconditional `Summable …`.
- FC's *docstring* discloses the condition ("conditional on such an irrationality measure of pi").

So the gap is documented in prose but not in the machine-readable claim. This is not a certified
defect under the protocol, and it is not evidence that the statement is false (the bound is a published
theorem). What is certified is the scoped relation "the cited theorem proves the target given
`PiIrrBound`". The case stays `undecided`.

**F4. One in five links does not identify a declaration.** For 12/60 links (20%, CP 10.8–32.3%), the
link names a file whose declaration the anchor, name and only-theorem rules cannot identify. Typically
it is a file-level URL to a file with several theorems. Under amendment 1 these are
`infrastructure_blocked: locate`, never defects: the link is imprecise, not wrong.

**F5. Some cited proofs do not build at their pinned commit in a clean environment.**
- SL003-46 and SL003-51 (one repository): `dsimp`/`rewrite` failures in an upstream module.
- SL003-28: a style linter configured as an error.

These are recorded as `infrastructure_blocked: build`. A build failure in our environment is not
evidence that the mathematics is wrong.

## 4. Baselines (same 60 cases)

| Method | Certified links | Note |
|---|---|---|
| Textual identity of statements | 12 counted "identical" | not a certificate; 4 of the 12 could not be checked (2 transport, 2 environment) |
| `exact` (direct) | 10 | |
| `exact` + deterministic cascade | 11 | |
| Full pipeline with AI bridges | **18** | +7 over the cascade, all kernel-replayed |

**Not run:** SemantEq, BEq+, Comparator, and an AI agent working without the pipeline. Comparator
checks that a submission proves an *identical* statement (FrontierMath Erdős uses it this way), so by
construction it would accept at most the direct cases. That is an inference, not a measurement.

Runtime: Stage B took a median of 243 s per case (maximum 930 s; 4.0 runner-hours in total, mostly
Mathlib cache downloads and builds). The AI bridges compiled in 7–14 s each. No model API spend is
recorded, because the bridges were written in-session.

## 5. Hostile review

- **The harness was amended after outcomes were seen** (amendments 2–4). Each fix is general, disclosed
  with its timing, and launch 2 is kept as the frozen-transport baseline. Still, v1.1 was developed on
  this sample. The certified rate is therefore an in-sample estimate, and it needs a confirmatory run on
  a fresh sample.
- **n = 60 with 21 clusters.** plby/lean-proofs supplies over half the sample, so the cluster-bootstrap
  intervals are wide.
- **The AI result is narrow.** 7/7 bridges is a perfect hit rate on cases the agent chose, and the
  agent declined the 13 hard ones. The economics claim ("cheap bridges for routine translations") holds.
  A claim that AI closes most gaps does not.
- **No defect was found.** That is a clean-audit result, not a failure: 0/40 built cited declarations
  use `sorry` or non-standard axioms.
- **No result here has been reviewed outside the project.**

## 6. Per-case outcomes

| Case | Repository | FC target | Outcome | Method / cause | Uses cited | Link |
|---|---|---|---|---|---|---|
| SL003-00 | plby/lean-proofs | `erdos_235` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos235.lean#L4266) |
| SL003-01 | plby/lean-proofs | `erdos_253` | infrastructure_blocked | transport |  | [link](https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos253.lean#L699) |
| SL003-02 | Marti2203/formal-conjectures | `erdos_987.variants.sqrt_lower_bound` | infrastructure_blocked | transport |  | [link](https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean) |
| SL003-03 | plby/lean-proofs | `erdos_581` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos581.lean#L31) |
| SL003-04 | epoch-research/LeanOpenProblems-results | `conjecture` | infrastructure_blocked | environment |  | [link](https://github.com/epoch-research/LeanOpenProblems-results/blob/f02efd9a8c5fc6a735d2a90c33e24f7278ce0ffc/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_64169_conjecture_0/Submission/Spec.lean#L514) |
| SL003-05 | linrock/math-proofs | `erdos_958` | infrastructure_blocked | transport |  | [link](https://github.com/linrock/math-proofs/blob/08152671ab394392fd941b18654daba734c26518/erdos-958/Solution.lean#L60) |
| SL003-06 | plby/lean-proofs | `erdos_441` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos441.lean#L453) |
| SL003-07 | plby/lean-proofs | `erdos_21` | auto_bridged_ai | Attempt1 | yes | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos21.lean#L13036) |
| SL003-08 | plby/lean-proofs | `erdos_775` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos775.lean) |
| SL003-09 | plby/lean-proofs | `erdos_477.variants.monomial` | auto_bridged_ai | Attempt1 | yes | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos477.lean#L42) |
| SL003-10 | plby/lean-proofs | `erdos_525.parts.i` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos525.lean#L118) |
| SL003-11 | gotrevor/lean-gallery | `erdos_1050.variants.two_pow_sub_one` | directly_verified | Direct | yes | [link](https://github.com/gotrevor/lean-gallery/blob/main/LeanGallery/NumberTheory/Erdos1050/Variants.lean) |
| SL003-12 | plby/lean-proofs | `erdos_83` | auto_bridged_ai | Attempt1 | yes | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos83.lean#L36) |
| SL003-13 | VictorLiwentao/lean-oeis-proofs | `conjecture_1` | directly_verified | Direct | yes | [link](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewProofs/A098275.lean#L166) |
| SL003-14 | KitaKen1/monochromatic-quantum-graphs-lean | `eqSystem6_no_solution_d3_trinary_int` | undecided |  |  | [link](https://github.com/KitaKen1/monochromatic-quantum-graphs-lean/blob/d3ed1892ef181f5f5f5d61d9b5817f05b53a6675/lean/QuantumLean/FormalConjecturesWrappers.lean#L88-L97) |
| SL003-15 | AxiomMath/gdm-formal-conjectures | `borwein_sine_series` | undecided |  |  | [link](https://github.com/AxiomMath/gdm-formal-conjectures/blob/main/BorweinSineSeries/solution.lean) |
| SL003-16 | plby/lean-proofs | `erdos_690` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2162) |
| SL003-17 | KitaKen1/erdos-979-k3 | `erdos_979.variants.k3` | directly_verified | Direct | yes | [link](https://github.com/KitaKen1/erdos-979-k3/blob/930fcc877fa4a2b4fc7c59614cbbab04a6d834ca/lean/K3Lean/Erdos979K3Final.lean#L46-L47) |
| SL003-18 | plby/lean-proofs | `erdos_519` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos519.lean) |
| SL003-19 | plby/lean-proofs | `erdos_438` | directly_verified | Direct | yes | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos438.lean#L46) |
| SL003-20 | gist:96516af9100a37a1da81908dc0b0410c | `erdos_692.parts.i` | infrastructure_blocked | locate |  | [link](https://gist.githubusercontent.com/pitmonticone/96516af9100a37a1da81908dc0b0410c/raw/a1d6ca7f3835c58b257e5e715c8fdf3a224e1bd0/Erdos692.lean) |
| SL003-21 | plby/lean-proofs | `erdos_95` | infrastructure_blocked | transport |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos95.lean#L1005) |
| SL003-22 | mnn31/erdos-lean | `finite_targets` | infrastructure_blocked | transport |  | [link](https://github.com/mnn31/erdos-lean/blob/5cb725981b3ad137103ef908eb6ecff9e7ed9bdf/ErdosLean/Erdos1167.lean#L990) |
| SL003-23 | plby/lean-proofs | `erdos_497` | infrastructure_blocked | transport |  | [link](https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos497.lean) |
| SL003-24 | plby/lean-proofs | `erdos_440.parts.i` | auto_bridged_ai | Attempt1 | yes | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos440.lean#L602) |
| SL003-25 | linrock/math-proofs | `erdos_306` | auto_bridged_deterministic | Cascade0 | yes | [link](https://github.com/linrock/math-proofs/blob/e1a5e2a3317007f0e31b98bf2e80383187b31238/erdos-306/Solution.lean#L34) |
| SL003-26 | anatoliiohorodnyk/lean-fc-proofs | `lovasz_plummer_conjecture` | directly_verified | Direct | yes | [link](https://github.com/anatoliiohorodnyk/lean-fc-proofs/blob/da6d56610c43a6eadd15945a3b80a62f223293f8/Proofs/T_LovaszPlummerConjecture_lovasz_plummer_conjecture.lean#L16602) |
| SL003-27 | plby/lean-proofs | `erdos_310` | auto_bridged_ai | Attempt1 | yes | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos310.lean#L240) |
| SL003-28 | KitaKen1/weak-tiling-bounded-density | `problem_4_1` | infrastructure_blocked | build |  | [link](https://github.com/KitaKen1/weak-tiling-bounded-density/blob/5d10499e1932cc017b7aaf8e931926dc969bd8f7/lean/WeakTilingProblem41FC.lean#L11484-L11487) |
| SL003-29 | linrock/math-proofs | `erdos_1180.variants.glibichuk` | directly_verified | Direct | yes | [link](https://github.com/linrock/math-proofs/blob/ba96303b34a95ac458958c1eb0bbdee54733484a/erdos-1180/Solution.lean#L83) |
| SL003-30 | glyaea/wow-ii-314 | `conjecture314` | infrastructure_blocked | environment |  | [link](https://github.com/glyaea/wow-ii-314/blob/7b35f1252e4aaae3c787faf8091f9c7cd4edc41f/solution.lean) |
| SL003-31 | plby/lean-proofs | `erdos_31` | infrastructure_blocked | transport |  | [link](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos31.lean) |
| SL003-32 | plby/lean-proofs | `erdos_537` | auto_bridged_ai | Attempt1 | yes | [link](https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos537.lean) |
| SL003-33 | KitaKen1/wowii-graph-conjecture-316-lean | `conjecture316` | infrastructure_blocked | environment |  | [link](https://github.com/KitaKen1/wowii-graph-conjecture-316-lean/blob/3335e07151bc43e86d5c104dd30fee3596f06410/GraphConjecture316.lean) |
| SL003-34 | math-inc/Sphere-Packing-Lean | `green_42.variants.dimension_eight` | infrastructure_blocked | locate |  | [link](https://github.com/math-inc/Sphere-Packing-Lean/blob/main/SpherePacking/Dim8/MainTheorem.lean) |
| SL003-35 | plby/lean-proofs | `erdos_737.variants.uncountable` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos737.lean#L1181) |
| SL003-36 | plby/lean-proofs | `erdos_898` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos898.lean) |
| SL003-37 | openai/math | `borsuk_conjecture` | infrastructure_blocked | transport |  | [link](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Main.lean#L117) |
| SL003-38 | wcook04/plectis-erdos-lean | `erdos_257.variants.summable_reciprocal_support` | directly_verified | Direct | yes | [link](https://github.com/wcook04/plectis-erdos-lean/blob/ec92e5ce12c6117a24e4b532ea565ba332a1df7b/verification/FC257ReciprocalSupport/verification/Solutions/FC257Subtype.lean#L10-L17) |
| SL003-39 | — | `erdos_654.parts.i` | infrastructure_blocked | retrieval |  | [link](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-02-000006) |
| SL003-40 | plby/lean-proofs | `erdos_690.variants.cambie_unimodal` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos690.lean#L2162) |
| SL003-41 | wcook04/plectis-erdos-lean | `erdos_1049.variants.geq_2_integer` | directly_verified | Direct | yes | [link](https://github.com/wcook04/plectis-erdos-lean/blob/c4eab2571b4692ee9c08d3ec138176f7fbfa09a9/verification/FCMergedIntegerAdapters/research/adapters/FormalConjecturesAdapter.lean#L96-L107) |
| SL003-42 | plby/lean-proofs | `erdos_314` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos314.lean) |
| SL003-43 | KitaKen1/monochromatic-quantum-graphs-lean | `eqSystem8_no_solution_d3_trinary_int` | undecided |  |  | [link](https://github.com/KitaKen1/monochromatic-quantum-graphs-lean/blob/d3ed1892ef181f5f5f5d61d9b5817f05b53a6675/lean/QuantumLean/FormalConjecturesWrappers.lean#L122-L131) |
| SL003-44 | plby/lean-proofs | `erdos_93` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos93.lean) |
| SL003-45 | plby/lean-proofs | `erdos_1195` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1195.lean#L1933) |
| SL003-46 | plby/lean-proofs | `erdos_981` | infrastructure_blocked | build |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos981.lean#L42) |
| SL003-47 | — | `erdos_654.variants.feng` | infrastructure_blocked | retrieval |  | [link](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-02-000006) |
| SL003-48 | plby/lean-proofs | `erdos_502` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos502.lean) |
| SL003-49 | plby/lean-proofs | `erdos_214` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos214.lean) |
| SL003-50 | gotrevor/lean-gallery | `erdos_482` | undecided |  |  | [link](https://github.com/gotrevor/lean-gallery/blob/a28a487968d989b24c9dde9b1958aa5b92c6fccb/LeanGallery/NumberTheory/Erdos482/Statement.lean#L46-L49) |
| SL003-51 | plby/lean-proofs | `erdos_237` | infrastructure_blocked | build |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos237b.lean#L55) |
| SL003-52 | anatoliiohorodnyk/lean-fc-proofs | `erdos_263.variants.super_doubly_exponential_eventual` | directly_verified | Direct | yes | [link](https://github.com/anatoliiohorodnyk/lean-fc-proofs/blob/5da9642575b26c2c816a49bcb56b33fed5456619/Proofs/T_Erdos263_erdos_263_variants_super_doubly_exponential_eventual.lean#L515) |
| SL003-53 | anatoliiohorodnyk/lean-fc-proofs | `erdos_10.variants.two_pows` | directly_verified | Direct | yes | [link](https://github.com/anatoliiohorodnyk/lean-fc-proofs/blob/5da9642575b26c2c816a49bcb56b33fed5456619/Proofs/T_Erdos10_erdos_10_variants_two_pows.lean#L340) |
| SL003-54 | plby/lean-proofs | `erdos_559.variants.degree_three` | infrastructure_blocked | transport |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos559.lean#L1275) |
| SL003-55 | plby/lean-proofs | `erdos_841.variants.lower_bound` | undecided |  |  | [link](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos841/LowerBound.lean#L3166) |
| SL003-56 | plby/lean-proofs | `erdos_199` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos199.lean) |
| SL003-57 | williamjblair/lean-proofs | `erdos_394.parts.i` | infrastructure_blocked | locate |  | [link](https://github.com/williamjblair/lean-proofs/blob/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-394/Research/FirstQuestion.lean) |
| SL003-58 | plby/lean-proofs | `erdos_666` | infrastructure_blocked | locate |  | [link](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos666.lean) |
| SL003-59 | VictorLiwentao/lean-oeis-proofs | `three_dvd_a` | auto_bridged_ai | Attempt1 | yes | [link](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewFormalization/A397588.lean#L325) |

"Uses cited" means the accepted proof term depends on the cited theorem, following the attempt's
own auxiliary declarations.

## 7. Reproduce

Bump `experiments/SL-003/RUN` on `main`. The workflow then:
- regenerates the population and sample and compares them byte for byte;
- re-runs Stage A and compares it with the committed records;
- runs Stage B per case (limited by `STAGE_B_CASES` when that file exists);
- publishes one annotation per case.

`python experiments/SL-003/collect.py <annotations.tsv> experiments/SL-003/results/stage_b` and
`python experiments/SL-003/analyze.py` rebuild every number in this report.
