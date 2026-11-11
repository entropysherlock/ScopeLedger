#!/usr/bin/env python3
"""SL-003 population and sample (PROTOCOL.md sections 2-4).

  population.py enumerate <formal-conjectures checkout at FC_COMMIT>   -> population.jsonl
  population.py sample    <formal-conjectures checkout at FC_COMMIT>   -> sample.jsonl

`sample` takes its seed from git: the SHA-1 of the first commit that added PROTOCOL.md (the freeze
commit). It refuses to run if that commit does not exist or the population is not 997 links.
"""
import hashlib
import json
import random
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FC_COMMIT = "da703a5f239f734a47ede2f4e99b9ccc9e644cb5"
N_ELIGIBLE = 997
N_SAMPLE = 60
ATTR = re.compile(r'formal_proof\s+using\s+(\w+)\s+at\s+"([^"]+)"')


def enumerate_links(fc: str) -> list[dict]:
    head = subprocess.run(["git", "-C", fc, "rev-parse", "HEAD"], check=True, capture_output=True,
                          text=True).stdout.strip()
    if head != FC_COMMIT:
        sys.exit(f"Formal Conjectures checkout is at {head}, expected {FC_COMMIT}")
    rows = []
    for f in sorted(Path(fc, "FormalConjectures").rglob("*.lean")):
        rel = f.relative_to(fc).as_posix()
        s = f.read_text(encoding="utf-8")
        for m in ATTR.finditer(s):
            t = re.search(r'\n\s*(?:theorem|lemma)\s+(\S+)', s[m.end():])
            rows.append({"fc_path": rel, "offset": m.start(), "kind": m.group(1), "url": m.group(2),
                         "target": t.group(1) if t else None,
                         "target_line": s[:m.end() + t.start() + 1].count("\n") + 2 if t else None})
    rows.sort(key=lambda r: (r["fc_path"], r["offset"]))
    return rows


def eligible(rows):
    return [r for r in rows if r["kind"] == "lean4"]


def host(url):
    m = re.match(r'https?://([^/]+)/', url)
    return m.group(1) if m else url


def repo_of(url):
    m = re.match(r'https?://(?:gist\.)?github(?:usercontent)?\.com/([^/]+/[^/#?]+)', url)
    return m.group(1) if m else host(url)


def freeze_commit() -> str:
    out = subprocess.run(["git", "-C", str(HERE), "log", "--diff-filter=A", "--format=%H", "--",
                          "PROTOCOL.md"], check=True, capture_output=True, text=True).stdout.split()
    if not out:
        sys.exit("PROTOCOL.md has not been committed; the sample cannot be drawn")
    return out[-1]


def main():
    cmd, fc = sys.argv[1], sys.argv[2]
    rows = enumerate_links(fc)
    el = eligible(rows)
    summary = {"fc_commit": FC_COMMIT, "formal_proof_attributes": len(rows), "eligible_lean4": len(el),
               "distinct_targets": len({(r["fc_path"], r["target"]) for r in el}),
               "hosts": dict(sorted({h: sum(1 for r in el if host(r["url"]) == h)
                                     for h in {host(r["url"]) for r in el}}.items(), key=lambda x: -x[1]))}
    if len(el) != N_ELIGIBLE:
        sys.exit(f"eligible population is {len(el)}, protocol requires {N_ELIGIBLE}: {summary}")
    if cmd == "enumerate":
        Path(HERE, "population.jsonl").write_text(
            "".join(json.dumps({"index": i, **r}, ensure_ascii=False) + "\n" for i, r in enumerate(el)))
        Path(HERE, "population_summary.json").write_text(json.dumps(summary, indent=1) + "\n")
        print(json.dumps(summary, indent=1))
        return 0
    if cmd == "sample":
        seed = freeze_commit()
        idx = random.Random(seed).sample(range(N_ELIGIBLE), N_SAMPLE)
        out = []
        for order, i in enumerate(idx):
            r = el[i]
            out.append({"order": order, "population_index": i, "case_id": f"SL003-{order:02d}",
                        "repo": repo_of(r["url"]), **r})
        Path(HERE, "sample.jsonl").write_text("".join(json.dumps(o, ensure_ascii=False) + "\n" for o in out))
        meta = {"seed": seed, "method": "random.Random(seed).sample(range(997), 60)",
                "python": sys.version.split()[0],
                "population_sha256": hashlib.sha256(Path(HERE, "population.jsonl").read_bytes()).hexdigest(),
                "repos_in_sample": len({o["repo"] for o in out})}
        Path(HERE, "sample_meta.json").write_text(json.dumps(meta, indent=1) + "\n")
        print(json.dumps(meta, indent=1))
        return 0
    raise SystemExit(f"unknown command {cmd}")


if __name__ == "__main__":
    sys.exit(main())
