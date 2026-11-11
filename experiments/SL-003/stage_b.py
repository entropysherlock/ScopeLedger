#!/usr/bin/env python3
"""SL-003 Stage B for one case (PROTOCOL.md sections 7-10).

  stage_b.py <stage-a json> <env root (target repo checked out at the pin)> <formal-conjectures dir> <out dir>

Steps: Mathlib cache -> build the cited module -> axioms of the cited declaration -> transport the
target -> Direct, then the fixed cascade (and AI attempt files, if present in ai/<case>/) -> axioms
and leanchecker replay of the first success. Fails closed; every stop is named. Prints one public
annotation with the result and writes <out>/result.json.
"""
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(cmd, cwd, timeout, env=None):
    t = time.time()
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env,
                           stdin=subprocess.DEVNULL)
        return p.returncode, p.stdout + p.stderr, round(time.time() - t)
    except subprocess.TimeoutExpired:
        return None, "TIMEOUT", round(time.time() - t)


def axioms(log, name):
    m = re.search(r"'" + re.escape(name) + r"' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    if not m:
        return None
    return sorted(a.strip() for a in (m.group(2) or "").split(",") if a.strip())


def main():
    sa = json.loads(Path(sys.argv[1]).read_text())
    root, fc, out = Path(sys.argv[2]).resolve(), sys.argv[3], Path(sys.argv[4]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    case = sa["case_id"]
    R = {"case_id": case, "stage": "B", "url": sa["url"], "target": sa["target"],
         "cited": sa.get("cited_qualified"), "module": sa.get("cited_module"),
         "toolchain": (sa.get("environment") or {}).get("toolchain"), "steps": {}}

    def finish(outcome, **kw):
        R.update(outcome=outcome, **kw)
        (out / "result.json").write_text(json.dumps(R, indent=1, ensure_ascii=False) + "\n")
        short = {k: R.get(k) for k in ("case_id", "outcome", "cause", "detail", "method", "cited_axioms",
                                       "proof_axioms", "replay", "toolchain")}
        short["seconds"] = {k: v.get("seconds") for k, v in R["steps"].items()}
        print(f"::notice title=SL-003 {case}::" + json.dumps(short, ensure_ascii=False)[:3500])
        return 0

    # 1. dependencies
    if "mathlib" in (sa.get("environment") or {}).get("packages", {}):
        ok = False
        for _ in range(3):
            rc, log, s = run(["lake", "exe", "cache", "get"], root, 1500)
            R["steps"]["cache"] = {"rc": rc, "seconds": s}
            if rc == 0:
                ok = True
                break
            time.sleep(30)
        if not ok:
            return finish("infrastructure_blocked", cause="build", detail="Mathlib cache unavailable: " + log[-300:])
    # 2. build the cited module
    rc, log, s = run(["lake", "build", sa["cited_module"]], root, 3600)
    (out / "build.log").write_text(log)
    R["steps"]["build"] = {"rc": rc, "seconds": s}
    if rc != 0:
        return finish("infrastructure_blocked", cause="build",
                      detail=("timeout" if rc is None else "lake build failed: ") + " | ".join(
                          [l for l in log.splitlines() if "error" in l][:4])[:600])
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=root, capture_output=True,
                               text=True).stdout.strip()
    work = out / "lean"
    work.mkdir(exist_ok=True)
    env = {**os.environ, "LEAN_PATH": f"{work}:{lean_path}"}
    # 3. axioms of the cited declaration
    (work / "CitedAxioms.lean").write_text(f"import {sa['cited_module']}\n#print axioms {sa['cited_qualified']}\n")
    rc, log, s = run(["lean", "CitedAxioms.lean"], work, 1200, env)
    R["steps"]["cited_axioms"] = {"rc": rc, "seconds": s}
    cax = axioms(log, sa["cited_qualified"])
    R["cited_axioms"] = cax
    if cax is None:
        return finish("infrastructure_blocked", cause="build", detail="cited declaration not found after build: "
                      + log[-300:])
    if [a for a in cax if a not in ALLOWED]:
        return finish("certified_defect_link", detail=f"cited declaration depends on {cax}",
                      method="axiom report of a successfully built declaration")
    # 4. transport
    rc_t = subprocess.run([sys.executable, str(HERE / "transport.py"), sys.argv[1], fc, str(work),
                           sa["cited_module"], sa["cited_qualified"]], capture_output=True, text=True)
    R["transport_edits"] = json.loads((work / "edits.json").read_text()) if (work / "edits.json").exists() else None
    if rc_t.returncode != 0:
        return finish("infrastructure_blocked", cause="transport", detail=(rc_t.stdout + rc_t.stderr)[-400:])
    rc, log, s = run(["lean", "-o", "SL003Target.olean", "SL003Target.lean"], work, 1200, env)
    R["steps"]["transport_elaborate"] = {"rc": rc, "seconds": s}
    if rc != 0 or re.search(r':\d+:\d+: error', log):
        (out / "transport.log").write_text(log)
        return finish("infrastructure_blocked", cause="transport",
                      detail="transported target does not elaborate: " + " | ".join(
                          [l for l in log.splitlines() if "error" in l][:3])[:600])
    # 5. attempts, in fixed order
    attempts = [("directly_verified", "Direct")] + \
        [("auto_bridged_deterministic", f.stem) for f in sorted(work.glob("Cascade*.lean"))]
    ai_dir = HERE / "ai" / case
    for f in sorted(ai_dir.glob("Attempt*.lean"))[:2] if ai_dir.exists() else []:
        shutil.copy(f, work / f.name)
        attempts.append(("auto_bridged_ai", f.stem))
    budget_det = 600
    for outcome, mod in attempts:
        tmo = 1200 if outcome == "auto_bridged_ai" else max(60, budget_det)
        rc, log, s = run(["lean", "-o", f"{mod}.olean", f"{mod}.lean"], work, tmo, env)
        if outcome != "auto_bridged_ai":
            budget_det -= s
        R["steps"][mod] = {"rc": rc, "seconds": s, "first_error": next(
            (l for l in log.splitlines() if ": error" in l), None)}
        (out / f"{mod}.log").write_text(log)
        if rc == 0 and not re.search(r':\d+:\d+: error', log) and "sorry" not in log:
            thm = re.search(r'theorem\s+(\S+)', (work / f"{mod}.lean").read_text()).group(1)
            (work / "ProofAxioms.lean").write_text(f"import {mod}\n#print axioms {thm}\n")
            _, alog, _ = run(["lean", "ProofAxioms.lean"], work, 600, env)
            pax = axioms(alog, thm)
            R["proof_axioms"] = pax
            if pax is None or [a for a in pax if a not in ALLOWED]:
                R["steps"][mod]["rejected"] = f"axioms {pax}"
                continue
            if shutil.which("leanchecker"):
                rc2, clog, s2 = run(["leanchecker", mod], work, 1800, env)
                R["replay"] = {"tool": "leanchecker", "rc": rc2, "seconds": s2, "tail": clog[-200:]}
                if rc2 != 0:
                    R["steps"][mod]["rejected"] = "leanchecker replay failed"
                    continue
            else:
                R["replay"] = {"tool": None, "note": "leanchecker not present in this toolchain"}
            return finish(outcome, method=mod)
    return finish("undecided", detail="target elaborates; direct, cascade" +
                  (" and AI attempts" if ai_dir.exists() else "") + " did not prove it within budget")


if __name__ == "__main__":
    sys.exit(main())
