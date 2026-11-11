"""SL-003 analysis: one outcome per sampled case, rates with uncertainty, frozen decision rules.

  analyze.py            reads results/stage_a/*.json and results/stage_b/*.json, writes results/summary.json

Stage B results are the `SL-003 <case>` annotation JSON of the final launch for each case, saved as
results/stage_b/<case>.json. A case with no Stage B record keeps its Stage A outcome.
Intervals: Clopper-Pearson (exact binomial, 95%) on n = 60, and a cluster bootstrap over repositories
(2,000 resamples, fixed seed 0) because links in one repository are correlated (PROTOCOL section 7).
"""
import glob
import json
import random
from collections import Counter
from pathlib import Path

from scipy.stats import beta

HERE = Path(__file__).resolve().parent
DEFINITE = {"directly_verified", "auto_bridged_deterministic", "auto_bridged_ai", "human_assisted",
            "certified_defect_link", "certified_defect_statement"}


def cp(k, n, a=0.05):
    lo = 0.0 if k == 0 else beta.ppf(a / 2, k, n - k + 1)
    hi = 1.0 if k == n else beta.ppf(1 - a / 2, k + 1, n - k)
    return [round(float(lo), 3), round(float(hi), 3)]


def load():
    cases = []
    for f in sorted(glob.glob(str(HERE / "results/stage_a/SL003-*.json"))):
        a = json.loads(Path(f).read_text())
        b_path = HERE / "results/stage_b" / Path(f).name
        b = json.loads(b_path.read_text()) if b_path.exists() else None
        outcome = (b or a)["outcome"]
        cause = (b or a).get("cause")
        if outcome == "ready_for_stage_b":
            outcome, cause = "infrastructure_blocked", "not_run"
        cases.append({"case_id": a["case_id"],
                      # unresolved links (no repository) form singleton clusters
                      "repo": a.get("repo") or f"unresolved:{a['case_id']}", "outcome": outcome, "cause": cause,
                      "text_identical": a.get("text_identical"), "core_identical": a.get("core_identical"),
                      "method": (b or {}).get("method"),
                      "link_not_exercised": ((b or {}).get("control_without_cited") or {}).get("proved") is True})
    return cases


def rate(cases, pred, among=lambda c: True):
    pool = [c for c in cases if among(c)]
    k = sum(1 for c in pool if pred(c))
    return {"k": k, "n": len(pool), "p": round(k / len(pool), 3) if pool else None,
            "clopper_pearson_95": cp(k, len(pool)) if pool else None}


def cluster_boot(cases, pred, among=lambda c: True, B=2000, seed=0):
    by = {}
    for c in cases:
        by.setdefault(c["repo"], []).append(c)
    repos = sorted(by)
    rng = random.Random(seed)
    vals = []
    for _ in range(B):
        pool = [c for r in (rng.choice(repos) for _ in repos) for c in by[r] if among(c)]
        if pool:
            vals.append(sum(1 for c in pool if pred(c)) / len(pool))
    vals.sort()
    return [round(vals[int(0.025 * len(vals))], 3), round(vals[int(0.975 * len(vals)) - 1], 3)] if vals else None


def main():
    cases = load()
    assert len(cases) == 60, len(cases)
    out = {"n": 60, "outcomes": Counter(c["outcome"] for c in cases),
           "blocked_causes": Counter(c["cause"] for c in cases if c["outcome"] == "infrastructure_blocked")}
    T = lambda c: c["outcome"] not in ("infrastructure_blocked",) and not c["outcome"].startswith("certified_defect_link")
    D = [c for c in cases if c["outcome"] in DEFINITE]
    defects = [c for c in cases if c["outcome"].startswith("certified_defect")]
    t = [c for c in cases if T(c)]
    not_direct = [c for c in t if c["outcome"] != "directly_verified"]
    ai = [c for c in not_direct if c["outcome"] == "auto_bridged_ai"]
    blocked = [c for c in cases if c["outcome"] == "infrastructure_blocked"]
    out["sets"] = {"D": len(D), "T": len(t), "defects": len(defects), "not_direct_in_T": len(not_direct),
                   "ai_bridged_of_not_direct": len(ai), "blocked": len(blocked)}
    if defects and len(D) >= 42:
        verdict = "STRONG SUCCESS"
    elif not defects and t and len(not_direct) >= 0.2 * len(t) and not_direct and len(ai) >= 0.5 * len(not_direct):
        verdict = "SUCCESS (assurance)"
    elif t and sum(1 for c in t if c["outcome"] == "directly_verified") >= 0.9 * len(t):
        verdict = "FAILURE (need)"
    elif len(blocked) > 30:
        verdict = "FAILURE (feasibility)"
    else:
        verdict = "INCONCLUSIVE"
    # Rule order as written in PROTOCOL section 13; FAILURE (feasibility) is also reported independently.
    out["decision"] = {"verdict": verdict, "feasibility_failure_condition_met": len(blocked) > 30}
    preds = {
        "definite": lambda c: c["outcome"] in DEFINITE,
        "certified_any": lambda c: c["outcome"] in ("directly_verified", "auto_bridged_deterministic",
                                                    "auto_bridged_ai", "human_assisted"),
        "directly_verified": lambda c: c["outcome"] == "directly_verified",
        "infrastructure_blocked": lambda c: c["outcome"] == "infrastructure_blocked",
        "locate_blocked": lambda c: c["outcome"] == "infrastructure_blocked" and c["cause"] == "locate",
        "text_identical": lambda c: bool(c["text_identical"]),
    }
    out["rates_over_60"] = {k: {**rate(cases, p), "cluster_bootstrap_95": cluster_boot(cases, p)}
                            for k, p in preds.items()}
    out["rates_over_T"] = {k: {**rate(cases, p, T), "cluster_bootstrap_95": cluster_boot(cases, p, T)}
                           for k, p in preds.items() if k in ("certified_any", "directly_verified")}
    out["baselines"] = {
        "textual_identity": rate(cases, lambda c: bool(c["text_identical"])),
        "exact_direct": rate(cases, preds["directly_verified"]),
        "exact_plus_cascade": rate(cases, lambda c: c["outcome"] in ("directly_verified",
                                                                     "auto_bridged_deterministic")),
        "full_pipeline_with_ai": rate(cases, preds["certified_any"]),
        "not_run": ["SemantEq", "BEq+", "Comparator", "AI agent without the pipeline"],
    }
    out["link_not_exercised"] = [c["case_id"] for c in cases if c["link_not_exercised"]]
    out["repos"] = len({c["repo"] for c in cases})
    out["cases"] = cases
    (HERE / "results/summary.json").write_text(json.dumps(out, indent=1, ensure_ascii=False, default=dict) + "\n")
    print(json.dumps({k: v for k, v in out.items() if k != "cases"}, indent=1, default=dict))


if __name__ == "__main__":
    main()
