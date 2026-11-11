#!/usr/bin/env python3
"""SL-004 held-out sample (PROTOCOL section 2).

  heldout.py            writes heldout_sample.jsonl and heldout_meta.json

Population: the 997 SL-003 links minus the 60 SL-003 sampled links (937). n = 60, drawn without
replacement with `random.Random(SEED)`, where SEED is the full SHA of the commit that added
`experiments/SL-004/ENGINE_FROZEN`. That commit freezes the engine, so this sample cannot have existed
while the engine was developed. Refuses to run before the freeze.
"""
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SL003 = HERE.parent / "SL-003"
N = 60


def freeze_commit():
    out = subprocess.run(["git", "log", "--diff-filter=A", "--format=%H", "--", "ENGINE_FROZEN"],
                         cwd=HERE, capture_output=True, text=True).stdout.split()
    if not out:
        sys.exit("ENGINE_FROZEN has not been committed: the held-out sample does not exist yet")
    return out[-1]


def main():
    pop = [json.loads(l) for l in (SL003 / "population.jsonl").read_text().splitlines() if l.strip()]
    used = {json.loads(l)["population_index"] for l in (SL003 / "sample.jsonl").read_text().splitlines() if l.strip()}
    pool = [r for r in pop if r["index"] not in used]
    assert len(pop) == 997 and len(used) == 60 and len(pool) == 937, (len(pop), len(used), len(pool))
    seed = freeze_commit()
    picked = random.Random(seed).sample(range(len(pool)), N)
    out = []
    for order, i in enumerate(picked):
        r = pool[i]
        repo = subprocess.run([sys.executable, "-c", "import sys;sys.path.insert(0,sys.argv[1]);import population as p;"
                               "print(p.repo_of(sys.argv[2]))", str(SL003), r["url"]],
                              capture_output=True, text=True).stdout.strip()
        out.append({"order": order, "population_index": r["index"], "case_id": f"H-{order:02d}", "repo": repo, **r})
    (HERE / "heldout_sample.jsonl").write_text("".join(json.dumps(o, ensure_ascii=False) + "\n" for o in out))
    meta = {"seed": seed, "method": "random.Random(seed).sample(range(937), 60) over SL-003 population minus SL-003 sample",
            "python": sys.version.split()[0],
            "population_sha256": hashlib.sha256((SL003 / "population.jsonl").read_bytes()).hexdigest(),
            "repos_in_sample": len({o["repo"] for o in out})}
    (HERE / "heldout_meta.json").write_text(json.dumps(meta, indent=1) + "\n")
    print(json.dumps(meta, indent=1))


if __name__ == "__main__":
    main()
