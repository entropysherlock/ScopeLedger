# Round 2 notes

- H-10: the round-1 error was in `candidate_eq`. After unfolding, both sides were the same
  `Finset.filter` membership. They differed only in the decidability instances, so `simp only`
  could not close the goal. Round 2 finishes that step with a `first` block, tried in this order:
  1. rewrite each side with `Finset.mem_filter` (`rw` matches instances up to definitional
     equality);
  2. `convert`, which closes instance differences because these instances are subsingletons;
  3. `simp only` with `Finset.mem_filter`.

  The rest of the file is unchanged from round 1, which reported no other errors.
- H-20: the round-1 error was the named argument `(Ω := Ω)`. Round 1 applied it after
  `Iff.mp ... trivial`, where the implicit `Ω` is already instantiated. Round 2 removes it, and `Ω`
  is now inferred from the repackaged `KacCoefficients` argument.
- H-05 and H-54: still no submission, for the reasons given in `round1/NOTES.md`.
