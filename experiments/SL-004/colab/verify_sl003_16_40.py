# SL-004 independent verification of SL003-16 and SL003-40 (Erdős 690) on Google Colab.
# Paste this whole cell into Colab and run it. Expected time: 20–60 minutes (Mathlib cache + project build).
# It runs the frozen ScopeLedger runner (experiments/SL-004/dev_run.py) on the round-5 Lean files, inside the
# cited project's own pinned environment, with the unchanged acceptance checks:
#   type guard (proves exactly the transported Formal Conjectures statement), axioms (standard only),
#   leanchecker replay, and the transitive dependency on the cited theorem.
# Nothing here is trusted by itself: every number printed comes from Lean.

# ----------------------------- settings -----------------------------
SCOPELEDGER_REPO = "https://github.com/entropysherlock/ScopeLedger"
SCOPELEDGER_COMMIT = "ea1712a8a206bc311e1bf74b3b91cf8ec94fdce2"   # engine-freeze commit (round-5 Lean files unchanged)
FC_REPO = "https://github.com/google-deepmind/formal-conjectures"
FC_COMMIT = "da703a5f239f734a47ede2f4e99b9ccc9e644cb5"
CASES = ["SL003-16", "SL003-40"]
WORK = "/content/sl004_verify"
RUN_ENGINE = False   # True also runs the 37 automatic-engine candidates (adds ~10 minutes)
# --------------------------------------------------------------------

import hashlib, json, os, shutil, subprocess, sys, time, zipfile
from pathlib import Path

t0 = time.time()


def sh(cmd, cwd=None, check=True):
    print("$", cmd, flush=True)
    r = subprocess.run(cmd, shell=True, cwd=cwd, text=True, capture_output=True)
    if r.stdout.strip():
        print(r.stdout[-2000:], flush=True)
    if r.returncode != 0:
        print(r.stderr[-3000:], flush=True)
        if check:
            raise SystemExit(f"command failed ({r.returncode}): {cmd}")
    return r


work = Path(WORK)
work.mkdir(parents=True, exist_ok=True)

# 1. elan (Lean toolchain manager); each project's own lean-toolchain picks the Lean version.
if not Path.home().joinpath(".elan/bin/elan").exists():
    sh("curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh")
    sh("sh /tmp/elan-init.sh -y --default-toolchain none")
os.environ["PATH"] = str(Path.home() / ".elan/bin") + ":" + os.environ["PATH"]

# 2. ScopeLedger at the freeze commit.
sl = work / "ScopeLedger"
if not sl.exists():
    sh(f"git clone -q {SCOPELEDGER_REPO} {sl}")
sh(f"git -C {sl} fetch -q origin {SCOPELEDGER_COMMIT} || true", check=False)
sh(f"git -C {sl} checkout -q {SCOPELEDGER_COMMIT}")
assert sh(f"git -C {sl} rev-parse HEAD").stdout.strip() == SCOPELEDGER_COMMIT

results = {}
for case in CASES:
    sa_path = sl / "experiments/SL-003/results/stage_a" / f"{case}.json"
    sa = json.loads(sa_path.read_text())
    root_rel = sa["environment"]["root"] or "."
    repo, commit, fc_path = sa["repo"], sa["pinned_commit"], sa["fc_path"]
    print(f"\n===== {case}: {repo} @ {commit}, root {root_rel}, FC {fc_path}", flush=True)

    # 3. Formal Conjectures at the frozen commit (only the file this case needs).
    fc = work / f"fc_{case}"
    if not fc.exists():
        sh(f"git clone -q --filter=blob:none --no-checkout {FC_REPO} {fc}")
        sh(f"git -C {fc} sparse-checkout set --no-cone /{fc_path}")
        sh(f"git -C {fc} checkout -q {FC_COMMIT}")

    # 4. The cited project at its pinned commit (shared between cases from the same repository).
    tgt = work / ("target_" + repo.replace("/", "__") + "_" + commit[:12])
    if not tgt.exists():
        sh(f"git clone -q --filter=blob:none --no-checkout https://github.com/{repo} {tgt}")
        if root_rel != ".":
            sh(f'git -C {tgt} sparse-checkout set --no-cone "/{root_rel}/**" "/*"')
        sh(f"git -C {tgt} checkout -q {commit}")
    assert sh(f"git -C {tgt} rev-parse HEAD").stdout.strip() == commit
    root = tgt / root_rel

    # 5. The frozen runner: Mathlib cache, build of the cited module, SL-003 transport, the SL004Lib library,
    #    then the round-5 candidates, each followed by the acceptance checks.
    out = work / "out" / case
    if out.exists():
        shutil.rmtree(out)
    env = dict(os.environ, SL004_ENGINE="1" if RUN_ENGINE else "0")
    r = subprocess.run([sys.executable, str(sl / "experiments/SL-004/dev_run.py"), str(sa_path), ".", str(fc),
                        str(sl / "experiments/SL-004/dev" / case), str(out)],
                       cwd=root, env=env, text=True, capture_output=True)
    (work / "out" / f"{case}.runner.log").write_text(r.stdout + "\n" + r.stderr)
    print(r.stdout[-1500:], r.stderr[-1500:], flush=True)
    results[case] = json.loads((out / "dev.json").read_text()) if (out / "dev.json").exists() else {"status": "no dev.json"}

# 6. Report, with hashes so the evidence can be checked against the repository.
print("\n\n================ SL-004 Colab verification: SL003-16 and SL003-40 ================")
for case, d in results.items():
    print(f"\n{case}: runner status = {d.get('status')}, toolchain = {d.get('toolchain')}, target = {d.get('target_prop')}")
    for f, v in (d.get("files") or {}).items():
        print(f"  file {f}: compiled = {v.get('ok')}" + (f"\n    first error: {v.get('first_error')}" if not v.get("ok") else ""))
    for thm, b in (d.get("bridges") or {}).items():
        print(f"  {thm}: proves_target = {b.get('proves_target')}, standard_axioms = {b.get('standard_axioms')} "
              f"{b.get('axioms')}, leanchecker = {b.get('leanchecker')}, uses_cited = {b.get('uses_cited')}")
    certified = [t for t, b in (d.get("bridges") or {}).items() if ".bridge" in t and b.get("proves_target")
                 and b.get("standard_axioms") and b.get("leanchecker") is not False and b.get("uses_cited")]
    print(f"  CERTIFIED BRIDGE: {certified[0] if certified else 'none'}")
    for f in sorted((sl / "experiments/SL-004/dev" / case).glob("*.lean")):
        print(f"  sha256 {hashlib.sha256(f.read_bytes()).hexdigest()}  {f.name}")

zpath = Path("/content/sl004_colab_SL003-16_40.zip")
with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as z:
    for p in (work / "out").rglob("*"):
        if p.is_file() and p.suffix not in (".olean", ".ilean", ".c") and p.stat().st_size < 5_000_000:
            z.write(p, p.relative_to(work))
print(f"\nAll logs: {zpath} (download it from the Colab file panel). Total time: {round((time.time() - t0) / 60)} min.")
print(json.dumps({c: {"status": d.get("status"), "bridges": d.get("bridges")} for c, d in results.items()}, indent=1)[:6000])
