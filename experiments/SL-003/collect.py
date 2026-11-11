"""Turn the public check-run annotations of one SL-003 launch into results files.

  collect.py <annotations.tsv> <out dir>

Each line of the TSV is `<annotation title>\t<message>` as published by the workflow. Writes
<out dir>/<case>.json (the Stage B summary, plus `errors` when present) and, for Stage A records that
CI published because they differ from the committed ones, <out dir>/stage_a_ci/<file>.
"""
import json
import sys
from pathlib import Path


def main():
    tsv, out = Path(sys.argv[1]), Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    recs = {}
    for line in tsv.read_text(encoding="utf-8").splitlines():
        if "\t" not in line:
            continue
        title, msg = line.split("\t", 1)
        if title.startswith("SL-003 stage_a_ci "):
            (out / "stage_a_ci").mkdir(exist_ok=True)
            (out / "stage_a_ci" / title.split()[-1]).write_text(msg + "\n")
            continue
        if title.startswith("SL-003 errors "):
            recs.setdefault(title.split()[-1], {})["errors"] = json.loads(msg)
        elif title.startswith("SL-003 SL003-"):
            recs.setdefault(title.split()[-1], {}).update(json.loads(msg))
    for case, r in sorted(recs.items()):
        (out / f"{case}.json").write_text(json.dumps(r, indent=1, ensure_ascii=False) + "\n")
    print(len(recs), "Stage B records")


if __name__ == "__main__":
    main()
