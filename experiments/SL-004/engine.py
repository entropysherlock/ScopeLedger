#!/usr/bin/env python3
"""SL-004 Theorem Transport Engine (automatic layer). Generates candidate bridge files; Lean decides.

  engine.py <target prop> <cited theorem> <out dir>

Writes one Lean file per strategy instance into <out dir>. Each file imports `SL003Target` (the Formal
Conjectures statement transported under `SL003FC` by SL-003 v1.1) and states

    theorem SL004.bridge_<strategy> : <target prop>

so the runner's type guard, axiom check, leanchecker replay and dependency check apply unchanged. The
engine never asserts a correspondence: every step is a tactic that Lean must check, and the kernel
replays the result.

Method ("anti-unify, then close by twins"):
  1. Logical normalisation of both statements with a fixed simp set: `True ↔ P`, eventual bounds
     written as `∃ N, ∀ n ≥ N`, `≥`/`>` orientation, bounded quantifiers.
  2. Projection: when the cited statement is a conjunction, each conjunct up to depth 4 is a
     candidate.
  3. Anti-unification by `convert … using k` (k = 1..4). This leaves exactly the subterms where the
     two statements differ.
  4. Twin closure: each residual goal is closed by definitional equality with irreducibility
     overridden (`with_unfolding_all rfl`). This succeeds when the two definitions compile to the same
     term up to their own names, which happens when one repository copied the other's source,
     including well-founded recursion, because `WellFounded.fix` of the same functional does not
     mention the defined constant. Otherwise `rfl`/`simp` close it, or the candidate fails.
Structure twins (re-declared `structure`s) and semantic re-representations (`sSup` vs `Finset.sup`,
`sInf` vs `Nat.find`, ...) are not handled automatically; they are the AI layer's job, supported by
the correspondence library `SL004Lib.lean`.
"""
import sys
from pathlib import Path

NORM = ("true_iff, iff_true, Filter.eventually_atTop, ge_iff_le, gt_iff_lt, exists_prop, and_imp, "
        "not_not, Set.mem_setOf_eq")
# Residual-goal closers, in order: definitional (twins), simp, and the extremal characterisation
# `sInf {n | P n} = Nat.find h` (least element), which needs no information about either side.
CLOSE = ("first | rfl | with_unfolding_all rfl | simp | (with_unfolding_all simp)"
         " | (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)"
         " | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩))"
         " | (apply funext; intro; first | with_unfolding_all rfl"
         " | (with_unfolding_all (apply IsLeast.csInf_eq; exact ⟨Nat.find_spec _, fun _ hm => Nat.find_min' _ hm⟩)))")
PROJ = ["", ".1", ".2", ".2.1", ".2.2", ".2.2.1", ".2.2.2"]


def candidates(tp: str, cited: str):
    c = f"@{cited}"
    out = {}
    out["E1_twin_exact"] = f"unfold {tp}\n  with_unfolding_all exact {c}"
    out["E2_iff_mp"] = f"unfold {tp}\n  first | exact ({c}).mp trivial | with_unfolding_all exact ({c}).mp trivial"
    for i, p in enumerate(PROJ):
        h = f"({c}){p}" if p else c
        for k in (1, 2, 3, 4):
            out[f"E3_convert_p{i}_k{k}"] = (
                f"unfold {tp}\n  have h := {h}\n  convert h using {k} <;> ({CLOSE})")
        out[f"E4_norm_p{i}"] = (
            f"unfold {tp}\n  have h := {h}\n  simp only [{NORM}] at h ⊢\n"
            f"  first\n    | exact h\n    | with_unfolding_all exact h\n"
            f"    | (convert h using 2 <;> ({CLOSE}))\n    | (convert h using 4 <;> ({CLOSE}))")
    return out


def baseline_candidates(tp: str, cited: str):
    """Baselines (PROTOCOL section 3): exact, plain convert + rfl (no unfolding), aesop, exact?."""
    c = f"@{cited}"
    return {
        "B1_exact": f"unfold {tp}\n  exact {c}",
        "B2_convert_rfl": f"unfold {tp}\n  have h := {c}\n  convert h using 3 <;> rfl",
        "B3_aesop": f"unfold {tp}\n  have h := {c}\n  aesop",
        "B4_exact_q": f"unfold {tp}\n  have h := {c}\n  exact?",
    }


def write(tp: str, cited: str, out: Path, gen=None, prefix="E"):
    out.mkdir(parents=True, exist_ok=True)
    names = []
    for name, tac in (gen or candidates)(tp, cited).items():
        f = out / f"{prefix}_{name}.lean"
        hb = 2000000 if name == "B4_exact_q" else 400000
        f.write_text(f"import SL003Target\n\nset_option maxHeartbeats {hb} in\n"
                     f"theorem SL004.bridge_{name} : {tp} := by\n  {tac}\n")
        names.append(f.name)
    return names


if __name__ == "__main__":
    print(len(write(sys.argv[1], sys.argv[2], Path(sys.argv[3]))), "candidates")
