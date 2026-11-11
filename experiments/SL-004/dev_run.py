#!/usr/bin/env python3
"""SL-004 development runner: compile candidate Lean files in a cited project's own environment.

  dev_run.py <SL-003 stage-a json> <env root> <formal-conjectures dir> <candidates dir> <out dir>

Steps: Mathlib cache, `lake build` of the cited module, SL-003 transport v1.1 (writes SL003Target.lean
with the Formal Conjectures statement under `SL003FC`), then every `*.lean` file in <candidates dir>
in name order, each compiled to an .olean so later files may import earlier ones. Every log is kept in
<out dir>. A declaration named `SL004.bridge*` that compiles is then checked like an SL-003 success:
type guard against the transported target, axioms, leanchecker replay, and transitive use of the cited
theorem. Results go to <out dir>/dev.json. Nothing here certifies anything by itself.
"""
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
SL003 = HERE.parent / "SL-003"
sys.path.insert(0, str(SL003))
import stage_b  # noqa: E402  (run, lean_module, first_error, axioms, USES, ALLOWED)


def main():
    sa = json.loads(Path(sys.argv[1]).read_text())
    root, fc, cand, out = (Path(sys.argv[2]).resolve(), sys.argv[3], Path(sys.argv[4]).resolve(),
                           Path(sys.argv[5]).resolve())
    out.mkdir(parents=True, exist_ok=True)
    sa["cited_module"] = stage_b.lean_module(sa["cited_module"])
    R = {"case_id": sa["case_id"], "cited": sa["cited_qualified"], "module": sa["cited_module"],
         "toolchain": (sa.get("environment") or {}).get("toolchain"), "steps": {}, "files": {}}

    def done(status, **kw):
        R.update(status=status, **kw)
        (out / "dev.json").write_text(json.dumps(R, indent=1, ensure_ascii=False) + "\n")
        print(f"::notice title=SL-004 dev {sa['case_id']}::" + json.dumps(
            {"status": status, "files": {k: v.get("ok") for k, v in R["files"].items()},
             "bridges": R.get("bridges")}, ensure_ascii=False)[:3000])
        return 0

    t0 = time.time()
    if "mathlib" in (sa.get("environment") or {}).get("packages", {}):
        for _ in range(3):
            rc, log, s = stage_b.run(["lake", "exe", "cache", "get"], root, 1500)
            if rc == 0:
                break
            time.sleep(30)
        R["steps"]["cache"] = {"rc": rc, "seconds": s}
    rc, log, s = stage_b.run(["lake", "build", sa["cited_module"]], root, 3600)
    (out / "build.log").write_text(log)
    R["steps"]["build"] = {"rc": rc, "seconds": s}
    if rc != 0:
        return done("build_failed")
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=root, capture_output=True,
                               text=True).stdout.strip()
    which = subprocess.run(["elan", "which", "lean"], cwd=root, capture_output=True, text=True)
    bindir = Path(which.stdout.strip()).parent
    LEAN, CHECKER = str(bindir / "lean"), bindir / "leanchecker"
    work = out / "lean"
    work.mkdir(exist_ok=True)
    import os
    env = {**os.environ, "LEAN_PATH": f"{work}:{lean_path}", "PATH": f"{bindir}:{os.environ.get('PATH', '')}"}
    tr = subprocess.run([sys.executable, str(SL003 / "transport.py"), sys.argv[1], fc, str(work),
                         sa["cited_module"], sa["cited_qualified"]], capture_output=True, text=True)
    (out / "transport.log").write_text(tr.stdout + tr.stderr)
    m = re.search(r'TRANSPORT_OK (\S+)', tr.stdout)
    if not m:
        return done("transport_failed")
    tp = m.group(1)
    R["target_prop"] = tp
    rc, log, s = stage_b.run([LEAN, "-o", "SL003Target.olean", "SL003Target.lean"], work, 1200, env)
    (out / "SL003Target.log").write_text(log)
    if rc != 0:
        return done("target_failed")
    bridges = {}
    # The shared correspondence library is compiled first, in the same environment, so candidates may
    # `import SL004Lib`. Its own success or failure is recorded like any other file.
    lib = sorted((HERE / "lib").glob("*.lean")) if (HERE / "lib").exists() else []
    for f in lib + sorted(cand.glob("*.lean")):
        shutil.copy(f, work / f.name)
        mod = f.stem
        rc, log, s = stage_b.run([LEAN, "-o", f"{mod}.olean", f"{mod}.lean"], work, 3600, env)
        (out / f"{mod}.log").write_text(log)
        ok = rc == 0 and not re.search(r':\d+:\d+: error', log)
        R["files"][f.name] = {"ok": ok, "rc": rc, "seconds": s, "first_error": stage_b.first_error(log)}
        if not ok:
            continue
        for thm in re.findall(r'^theorem\s+(SL004\.(?:bridge|relation|corr)\S*)', (work / f.name).read_text(), re.M):
            # bridge*: must prove exactly the transported target. relation*/corr*: scoped results whose
            # statement is printed and recorded as stated; never counted as proving the target.
            chk = work / f"Check_{mod}.lean"
            guard_line = f"example : {tp} := @{thm}\n\n" if ".bridge" in thm else ""
            chk.write_text(f"import {mod}\n\n{guard_line}#check @{thm}\n\n#print axioms {thm}\n")
            _, clog, _ = stage_b.run([LEAN, chk.name], work, 600, env)
            pax = stage_b.axioms(clog, thm)
            guard = not re.search(r':\d+:\d+: error', clog)
            rep = None
            if CHECKER.exists():
                rc2, rlog, _ = stage_b.run([str(CHECKER), mod], work, 3600, env)
                rep = rc2 == 0
            (work / "Uses.lean").write_text(stage_b.USES.format(mod=mod, thm=thm, cited=sa["cited_qualified"]))
            _, ulog, _ = stage_b.run([LEAN, "Uses.lean"], work, 300, env)
            um = re.search(r'USES_CITED (true|false)', ulog)
            st = re.search(r'@' + re.escape(thm) + r'\s*:\s*(.*?)(?=\n\S|\Z)', clog, re.S)
            bridges[thm] = {"file": f.name, "kind": thm.split(".")[1].rstrip("0123456789_"),
                            "statement": st.group(1).strip()[:2000] if st else None,
                            "proves_target": guard if ".bridge" in thm else None, "axioms": pax,
                            "standard_axioms": pax is not None and all(a in stage_b.ALLOWED for a in pax),
                            "leanchecker": rep, "uses_cited": (um.group(1) == "true") if um else None}
    R["bridges"] = bridges
    R["seconds_total"] = round(time.time() - t0)
    return done("ok")


if __name__ == "__main__":
    sys.exit(main())
