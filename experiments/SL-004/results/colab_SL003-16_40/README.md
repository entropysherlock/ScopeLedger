# Independent Colab verification of SL003-16 and SL003-40

Run by Caleb J. Westfall on Google Colab, 2026-11-11, using `colab/verify_sl003_16_40.py`, with:
- ScopeLedger at the engine-freeze commit `ea1712a8a206bc311e1bf74b3b91cf8ec94fdce2`;
- plby/lean-proofs at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` (Lean v4.33.0);
- Formal Conjectures at `da703a5`.

The four candidate-file SHA-256 hashes in the transcript match the repository at the freeze commit.
The run took 24 minutes. The transcript is kept verbatim in `transcript.txt`.

- **SL003-40: certified.** `SL004.bridge40` proves exactly the transported target, uses only the
  standard axioms, passes `leanchecker` replay, and depends on `Erdos690.erdos_690`. This agrees with
  GitHub run 43094411580.
- **SL003-16: unresolved.** `SL004.corr690_kth` is certified. `B01_bridge.lean` fails at 19:42. The
  hypothesis `hinc` has type `(fun p => ↑(primeFactorDensity 4 p)) p ≤ (fun p => …) q`, which is not
  beta-reduced, so `exact_mod_cast` cannot match it against `primeFactorDensity 4 p ≤
  primeFactorDensity 4 q` in ℚ. The remaining obligation is a beta-reduction before the cast (for
  example `have h := hinc p q hp hq h1 h2; simp only at h; exact_mod_cast h`). No mathematics is
  missing, but the development phase is frozen, so the case stays unresolved in SL-004's development
  record.
