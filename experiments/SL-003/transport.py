#!/usr/bin/env python3
"""Build the transported target block (PROTOCOL.md section 8) and the attempt files (section 9).

  transport.py <stage-a json> <formal-conjectures checkout> <out dir> <cited module>

Writes, in <out dir>:
  SL003Target.lean    Formal Conjectures definitions + `def SL003.targetProp : Prop := <target>`
  Direct.lean         `theorem SL003.direct : SL003.targetProp := by unfold SL003.targetProp; exact <cited>`
  CascadeK.lean       the fixed cascade, one tactic per file
  edits.json          every edit applied to the Formal Conjectures text
Fails closed: any construct outside the permitted edits stops with a reason in edits.json.
"""
import json
import re
import sys
from pathlib import Path

KEEP = re.compile(r'^(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*'
                  r'(def|abbrev|structure|inductive|instance|class|open|namespace|end|section|variable|'
                  r'notation|local\s+notation|scoped|set_option|universe|noncomputable\s+section|'
                  r'infix|infixl|infixr|prefix|postfix|macro_rules|syntax|attribute)\b')
DROP = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)*(theorem|lemma|example)\b')


def blocks(src: str):
    """Split into top-level blocks. A block starts at a non-indented line, except inside an open
    docstring or an unclosed attribute bracket, or right after a line ending in a continuation token."""
    out, cur, in_doc = [], [], False
    for l in src.split("\n"):
        starts = bool(l) and not l[0].isspace()
        prev = cur[-1].rstrip() if cur else ""
        joined = "\n".join(cur)
        open_attr = joined.lstrip().startswith("@[") and joined.count("[") > joined.count("]")
        cont = prev.endswith((",", "(", "→", "↔", ":=", "∧", "∨", "∀", "∃"))
        if starts and cur and not in_doc and not open_attr and not cont:
            out.append(cur)
            cur = []
        cur.append(l)
        if not in_doc and "/--" in l and "-/" not in l.split("/--", 1)[1]:
            in_doc = True
        elif in_doc and "-/" in l:
            in_doc = False
    if cur:
        out.append(cur)
    return out


def build(stage_a: dict, fc: str, module: str, cited_qualified: str):
    src = Path(fc, stage_a["fc_path"]).read_text(encoding="utf-8")
    src = re.sub(r'/-(?![-!]).*?-/', '', src, flags=re.S)     # plain block comments (licence header)
    src = re.sub(r'/-!.*?-/', '', src, flags=re.S)            # module docs
    edits, kept = ["removed comments and module docs"], []
    pending = []          # docstring / attribute / `set_option ... in` lines waiting for their declaration
    for b in blocks(src):
        text = "\n".join(b).rstrip()
        head = text.strip().split("\n")[0] if text.strip() else ""
        if not head or head.startswith("--"):
            continue
        is_attr_only = text.lstrip().startswith("@[") and text.count("[") == text.count("]") \
            and re.fullmatch(r'\s*(@\[.*?\]\s*)+', text, re.S) is not None
        if head.startswith("/--") or is_attr_only or re.fullmatch(r'set_option\s+\S+\s+\S+\s+in', text.strip()):
            pending.append(text)
            continue
        if head.startswith(("import ", "public import ")) or head == "module":
            edits.append(f"removed: {head[:60]}")
            pending = []
            continue
        if head.startswith("@[expose] public section") or head == "public section":
            kept.append("section")
            edits.append("public section -> section")
            pending = []
            continue
        full = "\n".join(pending + [text])
        core = re.sub(r'^(?:\s*(?:/--.*?-/|@\[.*?\]|set_option\s+\S+\s+\S+\s+in))*\s*', '', full, flags=re.S)
        if DROP.match(core):
            edits.append(f"removed declaration: {core.split(chr(10))[0][:70]}")
            pending = []
            continue
        if KEEP.match(core):
            cleaned = re.sub(r'@\[category.*?\]\s*', '', full, flags=re.S)
            if cleaned != full:
                edits.append("removed @[category ...] attribute")
            kept.append(cleaned)
            pending = []
            continue
        return None, edits + [f"STOP: unrecognized top-level construct: {core[:80]}"]
    stmt = stage_a["target_statement"]
    binders, colon_body = split_binders(stmt or "")
    if colon_body is None:
        return None, edits + ["STOP: could not find the statement's top-level ':'"]
    body = colon_body
    m = re.match(r'^answer\(\s*(True|False|sorry)\s*\)\s*↔\s*(.*)$', body, re.S)
    if m:
        if m.group(1) == "sorry":
            return None, edits + ["STOP: answer(sorry) target (problem still open in Formal Conjectures)"]
        body = m.group(2) if m.group(1) == "True" else f"¬ ({m.group(2)})"
        edits.append(f"answer({m.group(1)}) wrapper rewritten")
    if binders:
        # A theorem `(x : α) : P x` has type `∀ (x : α), P x`; this is how Lean elaborates it (amendment 2).
        body = f"∀ {binders}, {body}"
        edits.append("binders before ':' written as a leading ∀ (the theorem's elaborated type)")
    ns = namespace_at_target(src, stage_a["target"])
    header = "import Mathlib\nimport " + module + "\n\n"
    target = (header + "\n".join(kept).strip() + "\n\n"
              + (f"namespace {ns}\n\n" if ns else "")
              + f"/-- SL-003 transported target: {stage_a['fc_path']} `{stage_a['target']}`. -/\n"
              + f"def SL003.targetProp : Prop :=\n  {body}\n\n"
              + (f"end {ns}\n" if ns else ""))
    return target, edits


def namespace_at_target(src, target):
    stack = []
    for l in src.split("\n"):
        m = re.match(r'^\s*namespace\s+(\S+)', l)
        if m:
            stack.append(m.group(1))
        m = re.match(r'^\s*end\s+(\S+)\s*$', l)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
        if re.match(r'^\s*(?:@\[[^\]]*\]\s*)*theorem\s+' + re.escape(target) + r'\b', l):
            break
    return ".".join(stack)


OPEN, CLOSE = "([{⦃⟨", ")]}⦄⟩"


def split_binders(stmt):
    """Split `binders : type` at the first ':' at bracket depth 0. Returns (binders, type) or (None, None)."""
    depth = 0
    for i, ch in enumerate(stmt):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif ch == ":" and depth == 0 and stmt[i + 1:i + 2] not in ("=", ":"):
            return stmt[:i].strip(), stmt[i + 1:].strip()
    return None, None


CASCADE = ["simpa using @{c}", "exact_mod_cast @{c}", "simpa [{defs}] using @{c}", "exact (@{c}).1", "exact (@{c}).2"]


def main():
    sa = json.loads(Path(sys.argv[1]).read_text())
    fc, out, module, cited = sys.argv[2], Path(sys.argv[3]), sys.argv[4], sys.argv[5]
    out.mkdir(parents=True, exist_ok=True)
    target, edits = build(sa, fc, module, cited)
    (out / "edits.json").write_text(json.dumps(edits, indent=1, ensure_ascii=False) + "\n")
    if target is None:
        print("TRANSPORT_STOP", edits[-1])
        return 3
    (out / "SL003Target.lean").write_text(target)
    ns = namespace_at_target(Path(fc, sa["fc_path"]).read_text(encoding="utf-8"), sa["target"])
    tp = (ns + "." if ns else "") + "SL003.targetProp"
    defs = ", ".join(sorted(set(re.findall(r'^(?:noncomputable\s+)?def\s+(\S+)', target, re.M)) - {"SL003.targetProp"}))
    (out / "Direct.lean").write_text(f"import SL003Target\n\ntheorem SL003.direct : {tp} := by\n  unfold {tp}\n  exact @{cited}\n")
    for k, t in enumerate(CASCADE):
        if "{defs}" in t and not defs:
            continue
        (out / f"Cascade{k}.lean").write_text(
            f"import SL003Target\n\ntheorem SL003.cascade{k} : {tp} := by\n  unfold {tp}\n  {t.format(c=cited, defs=defs)}\n")
    print("TRANSPORT_OK", tp, len(edits), "edits")
    return 0


if __name__ == "__main__":
    sys.exit(main())
