# Task: kernel-checked bridges from cited Lean proofs to Formal Conjectures statements

You are given 13 cases in `cases/`. In each case, a Lean project at a pinned commit contains a cited
theorem that is claimed to resolve a statement in Google DeepMind's Formal Conjectures repository. That
statement has been transported, unchanged in meaning, into the cited project's Lean environment as a
proposition named in `case.json` → `transported_target` (for example `SL003FC.Erdos534.SL003.targetProp`),
defined in `SL003Target.lean`. Formal Conjectures' own definitions live there under the namespace
`SL003FC`. `SL003Target.lean` imports Mathlib and the cited module.

For each case, write Lean 4 files that prove the transported target from the cited theorem.

## Files in each case directory
- `case.json`: the target name, the cited theorem name and its statement text, the repository URL,
  the pinned commit, the toolchain, and the project root inside the repository.
- `SL003Target.lean`: the transported Formal Conjectures statement and definitions.
- `explore.log`: Lean's `#print` output, in the cited environment, for the target, the cited theorem and
  identifiers appearing in either statement (unknown names show as errors).
- `exact_attempt_error.log`: the compiler error from `unfold <target>; exact @<cited theorem>`.

You may `git clone` the cited repository at the pinned commit to read its source. You may rely on your
knowledge of Lean 4 and Mathlib.

## Submission format (checked mechanically)
- Write at most **3** `.lean` files per case per round, in `submissions/round<k>/<case>/`.
- Each file must begin with `import SL003Target`. Files are compiled in name order, and a later file may
  `import` an earlier one by its file stem.
- The final theorem must be named `SL004.bridge_<anything>` (a harness naming requirement) and have
  exactly the type `<transported_target>` (for example
  `theorem SL004.bridge_main : SL003FC.Erdos534.SL003.targetProp := by ...`).
- No `sorry`, no new `axiom`s, no `native_decide`. Only `propext`, `Classical.choice` and `Quot.sound` may
  appear in `#print axioms`.
- The proof must actually use the cited theorem. A proof that does not depend on it is rejected.
- You cannot compile here: there is no Mathlib cache in this machine. Your round-1 files will be
  compiled remotely in the pinned environment, and you will receive the compiler output. You then get one
  more round (round 2), with at most 3 files per case. After that the case is closed.
- If you judge a case impossible (for example, the cited theorem does not imply the target), you may
  submit nothing for it and say why in `submissions/round<k>/NOTES.md`.

## Rules
- Work only inside this directory (`DIRECTORY`). Do not read any other directory on this machine.
- Do not look for, clone or browse the repository `entropysherlock/ScopeLedger` or anything describing
  this experiment. Use the web only for Lean/Mathlib documentation and the cited repositories.
- No human will edit your files.
