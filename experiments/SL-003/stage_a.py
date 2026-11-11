#!/usr/bin/env python3
"""SL-003 Stage A: retrieval, pinning, location, environment and statements (PROTOCOL.md 5-8).

  stage_a.py <formal-conjectures checkout at FC_COMMIT> <work dir> [case_id ...]

Deterministic; no prover, no model. Writes results/stage_a/<case_id>.json and summary.json.
"""
import hashlib
import json
import re
import subprocess
import sys
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "SL-001"))
import sl001  # noqa: E402  (theorem_statement, core, norm)

CUTOFF = "2026-11-11T09:09:17Z"
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:public\s+|private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|alias)\s+(\S+)', re.M)


def theorem_statement(src, name, raw=False):
    """Text between `theorem NAME` and the `:=` that starts the proof (amendment 3).

    SL-001's helper cut at the first `:=`, which truncates statements containing `letI x := ...`.
    Here the proof's `:=` is the first one at bracket depth 0 followed by `by`, `sorry`, or a line end;
    if there is none, the first depth-0 `:=`.
    """
    m = re.search(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)*(?:theorem|lemma)\s+' + re.escape(name)
                  + r'(?=[\s:({\[])', src, re.M)
    if not m:
        return None
    rest = src[m.end():m.end() + 20000]
    depth, first = 0, None
    for i, ch in enumerate(rest):
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth -= 1
        elif ch == ":" and rest[i + 1:i + 2] == "=" and depth == 0:
            if first is None:
                first = i
            if re.match(r'\s*(by\b|sorry\b|\n|$)', rest[i + 2:i + 40]):
                return rest[:i].strip() if raw else sl001.norm(rest[:i])
    if first is None:
        return None
    return rest[:first].strip() if raw else sl001.norm(rest[:first])


def sh(*a, cwd=None, check=True):
    p = subprocess.run(a, cwd=cwd, capture_output=True, text=True)
    if check and p.returncode:
        raise RuntimeError(f"{' '.join(a)}: {p.stderr.strip()[:300]}")
    return p.stdout


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest() if s is not None else None


def parse_url(url):
    m = re.match(r'https://github\.com/([^/]+/[^/]+)/blob/([^/]+)/([^#?]+)(?:#L(\d+))?', url)
    if m:
        return {"kind": "github", "repo": m.group(1), "ref": m.group(2), "path": m.group(3),
                "line": int(m.group(4)) if m.group(4) else None}
    m = re.match(r'https://gist\.githubusercontent\.com/([^/]+)/([0-9a-f]+)/raw/([0-9a-f]{40})/([^#?]+)', url)
    if m:
        return {"kind": "gist", "repo": f"gist:{m.group(2)}", "ref": m.group(3), "path": m.group(4), "line": None}
    m = re.match(r'https://gist\.github\.com/([^/]+)/([0-9a-f]+)(?:/([0-9a-f]{40}))?', url)
    if m:
        return {"kind": "gist", "repo": f"gist:{m.group(2)}", "ref": m.group(3), "path": None, "line": None}
    if "palomar-registry.org" in url:
        return {"kind": "palomar", "repo": None, "ref": None, "path": None, "line": None}
    return {"kind": "other", "repo": None, "ref": None, "path": None, "line": None}


def clone(work: Path, u: dict) -> Path:
    if u["kind"] == "gist":
        gid = u["repo"].split(":")[1]
        url, d = f"https://gist.github.com/{gid}.git", work / "gists" / gid
    else:
        url, d = f"https://github.com/{u['repo']}", work / "repos" / u["repo"].replace("/", "__")
    if not (d / ".git").exists() and not (d / "HEAD").exists():
        d.parent.mkdir(parents=True, exist_ok=True)
        sh("git", "clone", "-q", "--filter=blob:none", "--no-checkout", "--bare", url, str(d))
    return d


def resolve(d: Path, u: dict):
    ref = u["ref"]
    if ref and re.fullmatch(r'[0-9a-f]{40}', ref):
        ok = subprocess.run(["git", "-C", str(d), "cat-file", "-e", ref + "^{commit}"]).returncode == 0
        if not ok:
            subprocess.run(["git", "-C", str(d), "fetch", "-q", "--filter=blob:none", "origin", ref])
            ok = subprocess.run(["git", "-C", str(d), "cat-file", "-e", ref + "^{commit}"]).returncode == 0
        return (ref, "url_sha") if ok else (None, "sha_missing_upstream")
    cand = ref or "HEAD"
    for r in ([f"refs/heads/{cand}", f"refs/tags/{cand}", cand] if ref else ["HEAD"]):
        out = subprocess.run(["git", "-C", str(d), "rev-list", "-1", f"--before={CUTOFF}", r],
                             capture_output=True, text=True).stdout.strip()
        if out:
            return out, f"resolved_{'branch' if ref else 'default_branch'}_at_cutoff"
    return None, "ref_unresolvable"


def locate(src: str, line, target: str):
    decls = [(src[:m.start()].count("\n") + 1 + m.group(0).count("\n") - (1 if m.group(0).startswith("\n") else 0),
              m.group(1)) for m in DECL.finditer(src)]
    if line:
        above = [d for d in decls if d[0] <= line + 1]
        if above:
            ln, nm = max(above)
            if line - ln <= 40:
                return nm, "anchor"
    last = target.split(".")[-1]
    named = [nm for _, nm in decls if nm.split(".")[-1] == last]
    if len(named) == 1:
        return named[0], "name"
    if len(decls) == 1:
        return decls[0][1], "only_theorem"
    return None, "not_located"


def environment(d: Path, commit: str, path: str):
    parts = path.split("/")[:-1]
    for k in range(len(parts), -1, -1):
        base = "/".join(parts[:k])
        pre = (base + "/") if base else ""
        tc = subprocess.run(["git", "-C", str(d), "show", f"{commit}:{pre}lean-toolchain"], capture_output=True, text=True)
        mf = subprocess.run(["git", "-C", str(d), "show", f"{commit}:{pre}lake-manifest.json"], capture_output=True, text=True)
        if tc.returncode == 0 and mf.returncode == 0:
            try:
                pk = json.loads(mf.stdout).get("packages", [])
            except json.JSONDecodeError:
                return {"root": base, "error": "manifest_unparseable"}
            src_dirs = []
            for lf in ("lakefile.toml", "lakefile.lean"):
                t = subprocess.run(["git", "-C", str(d), "show", f"{commit}:{pre}{lf}"], capture_output=True,
                                   text=True)
                if t.returncode == 0:
                    src_dirs += re.findall(r'srcDir\s*(?::=|=)\s*"([^"]*)"', t.stdout)
            return {"root": base, "toolchain": tc.stdout.strip(), "src_dirs": sorted(set(src_dirs)),
                    "packages": {p.get("name"): p.get("rev") for p in pk},
                    "depends_on_formal_conjectures": any("formal" in (p.get("name") or "").lower()
                                                         and "conjecture" in (p.get("name") or "").lower() for p in pk)}
    return None


def palomar(url):
    try:
        html = urllib.request.urlopen(url, timeout=30).read().decode("utf-8", "replace")
    except Exception as e:  # noqa: BLE001
        return None, f"palomar_unreachable: {e!r}"[:200]
    m = re.search(r'https://github\.com/([^/"\s]+/[^/"\s]+)/(?:blob|tree)/([0-9a-f]{40})/([^"#\s]+\.lean)', html)
    if not m:
        return None, "palomar_no_pinned_github_source"
    return {"kind": "github", "repo": m.group(1), "ref": m.group(2), "path": m.group(3), "line": None}, "palomar_resolved"


def run_case(c: dict, fc: str, work: Path) -> dict:
    r = {"case_id": c["case_id"], "url": c["url"], "fc_path": c["fc_path"], "target": c["target"],
         "stage": "A", "certifies": "nothing; deterministic observations only"}
    fc_src = Path(fc, c["fc_path"]).read_text(encoding="utf-8")
    tgt = theorem_statement(fc_src, c["target"])
    r["target_statement_raw"] = theorem_statement(fc_src, c["target"], raw=True)
    r["target_statement"] = tgt
    r["target_statement_sha256"] = sha(tgt)
    u = parse_url(c["url"])
    r["source_kind"] = u["kind"]
    if u["kind"] == "palomar":
        u2, note = palomar(c["url"])
        r["palomar"] = note
        if not u2:
            return {**r, "outcome": "infrastructure_blocked", "cause": "retrieval", "detail": note}
        u = u2
    if u["kind"] == "other":
        return {**r, "outcome": "infrastructure_blocked", "cause": "retrieval", "detail": "non-git host"}
    try:
        d = clone(work, u)
    except Exception as e:  # noqa: BLE001
        return {**r, "outcome": "infrastructure_blocked", "cause": "retrieval", "detail": str(e)[:300]}
    commit, how = resolve(d, u)
    r.update(repo=u["repo"], ref=u["ref"], pinned_commit=commit, pin_method=how, cited_path=u["path"],
             anchor_line=u["line"])
    if not commit:
        return {**r, "outcome": "infrastructure_blocked", "cause": "retrieval", "detail": how}
    if u["path"] is None:
        files = [f for f in sh("git", "-C", str(d), "ls-tree", "-r", "--name-only", commit).split() if f.endswith(".lean")]
        if len(files) != 1:
            return {**r, "outcome": "infrastructure_blocked", "cause": "locate", "detail": f"{len(files)} .lean files"}
        u["path"] = r["cited_path"] = files[0]
    src = subprocess.run(["git", "-C", str(d), "show", f"{commit}:{u['path']}"], capture_output=True, text=True)
    if src.returncode:
        return {**r, "outcome": "infrastructure_blocked", "cause": "retrieval", "detail": "file absent at pin"}
    r["cited_file_sha256"] = sha(src.stdout)
    name, how = locate(src.stdout, u["line"], c["target"])
    r.update(cited_decl=name, locate_method=how)
    if not name:
        return {**r, "outcome": "infrastructure_blocked", "cause": "locate",
                "detail": "file exists at pin; the link names no declaration that the anchor or name rules identify"}
    st = theorem_statement(src.stdout, name)
    r["cited_statement"] = st
    r["cited_statement_sha256"] = sha(st)
    r["text_identical"] = bool(st and tgt and sl001.norm(st) == sl001.norm(tgt))
    core_t, core_c = (sl001.core(tgt) if tgt else (None, None)), (sl001.core(st) if st else (None, None))
    r["core_identical"] = bool(st and tgt and core_t == core_c)
    r["cited_has_sorry_text"] = bool(re.search(r'\bsorry\b', re.sub(r'/-.*?-/|--.*', '', src.stdout, flags=re.S)))
    env = environment(d, commit, u["path"])
    r["environment"] = env
    if not env or env.get("error"):
        return {**r, "outcome": "infrastructure_blocked", "cause": "environment",
                "detail": (env or {}).get("error", "no lean-toolchain + lake-manifest.json above the cited file")}
    # Header line of the declaration itself (amendment 3): a declaration line outside block comments,
    # not a mention of the name in a docstring above the enclosing namespace.
    nc = re.sub(r'/-.*?-/', lambda mm: "\n" * mm.group(0).count("\n"), src.stdout, flags=re.S)
    hdr = next((i for i, l in enumerate(nc.split("\n"), 1)
                if re.match(r'^\s*(?:@\[[^\]]*\]\s*)*(?:public\s+|private\s+|protected\s+|noncomputable\s+)*'
                            r'(?:theorem|lemma|alias)\s+' + re.escape(name) + r'(?=[\s:({\[]|$)', l)), None)
    r["cited_qualified"] = sl001.qualified_name(src.stdout, hdr, name) if hdr else name
    rel = u["path"][len(env["root"]) + 1:] if env["root"] else u["path"]
    # Module name relative to the longest library srcDir containing the file (amendment 3); Lake names
    # modules from the srcDir, not from the package root.
    sd = max((x.strip("./") for x in env.get("src_dirs", []) if x.strip("./")
              and rel.startswith(x.strip("./") + "/")), key=len, default="")
    r["cited_module"] = (rel[len(sd) + 1:] if sd else rel)[:-len(".lean")].replace("/", ".")
    r["module_path_in_env"] = rel
    return {**r, "outcome": "ready_for_stage_b"}


def main():
    fc, work = sys.argv[1], Path(sys.argv[2])
    only = set(sys.argv[3:])
    out = HERE / "results" / "stage_a"
    out.mkdir(parents=True, exist_ok=True)
    cases = [json.loads(l) for l in (HERE / "sample.jsonl").read_text().splitlines() if l.strip()]
    res = []
    for c in cases:
        if only and c["case_id"] not in only:
            continue
        try:
            r = run_case(c, fc, work)
        except Exception as e:  # noqa: BLE001 - an exception is infrastructure, never a finding
            r = {"case_id": c["case_id"], "outcome": "infrastructure_blocked", "cause": "harness", "detail": repr(e)[:300]}
        res.append(r)
        (out / f"{c['case_id']}.json").write_text(json.dumps(r, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
        print(c["case_id"], r["outcome"], r.get("cause", ""), r.get("detail", "")[:80], flush=True)
    if not only:
        summ = {}
        for r in res:
            k = r["outcome"] + (f":{r['cause']}" if r.get("cause") else "")
            summ[k] = summ.get(k, 0) + 1
        summ["text_identical"] = sum(1 for r in res if r.get("text_identical"))
        summ["core_identical"] = sum(1 for r in res if r.get("core_identical"))
        (out / "summary.json").write_text(json.dumps(summ, indent=1, sort_keys=True) + "\n")
        print(json.dumps(summ, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
