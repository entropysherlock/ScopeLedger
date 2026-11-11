# AI attempts not made (SL-003, attempt round 1)

The AI agent (Claude) made no attempt on these undecided cases. A bridge would need a new mathematical
equivalence between two independently built definitions, beyond the two-attempt budget without a local
Lean environment. Each stays `undecided`.

* SL003-00 (Erdős 235): the cited `gapCDF` counts `internalShortGaps (primeProduct k)` with a Finset
  construction; FC's `proportion` counts list gaps of `coprimeList (primorial (nth Prime k))`. These
  need an equality of the two counts (indexing and boundary gaps), then `Continuous → ContinuousOn`.
* SL003-10 (Erdős 525): the cited `exceptionalFamily N` is over `Fin (N+1) → Bool` with `minModulus`;
  FC's `exceptional n` is over `Fin (n+1) → ℤˣ` with a unit-circle condition. This needs a bijection
  plus an equality of the two analytic conditions.
* SL003-15 (Borwein sine series): the cited theorem assumes `PiIrrBound` (an irrationality-measure
  bound μ(π) ≤ 7.10321, from Zeilberger–Zudilin, arXiv:1912.06345), which the repository does not
  prove. A bridge needs a Lean proof of that bound. FC's docstring discloses this ("conditional on such
  an irrationality measure of pi"), but the `formal_proof` attribute attaches the link to the
  unconditional statement.
* SL003-50 (Erdős 482): the cited statement uses `⌊√2·2^(n-1)⌋₊ % 2`; the target uses the binary digits
  of `√2/2` and adds a second conjunct `Real.ofDigits (…) = √2/2`. This needs a digit-extraction lemma and
  the reconstruction identity.
