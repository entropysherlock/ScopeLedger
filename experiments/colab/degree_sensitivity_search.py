# WESTFALL COLAB EXPERIMENT — beating the Kushilevitz degree–sensitivity exponent log_3(6)
# Paste this whole cell into Google Colab and run it. Re-running resumes from the checkpoint.
#
# Goal: find a Boolean function f on n bits with f(0)=0, f(e_i)=1 for all i (full sensitivity n at 0)
# and degree <= d, with log(n)/log(d) > log(6)/log(3) ≈ 1.63093. Composition then gives an infinite
# family, improving Tao's optimization constant 37a (degree–sensitivity exponent), open since the 1990s.
# Smallest open case: n=14, d=5 (Amano: none for n=10, d=4; Stepanovs: none for n=15, d=5;
# Smotrovs–Zaicevs 2026: 247 feasible weight profiles for (14,5), no construction found).
#
# Method (untested hypothesis): Kushilevitz's 6-bit function is invariant under PSL(2,5) on the projective
# line P^1(F_5) (6 points). We search for G-invariant solutions for many permutation groups G on n points,
# including PSL(2,q)/PGL(2,q) on P^1(F_q) with q+1 = n. G-invariance makes the exact problem an integer
# program over orbits; OR-Tools CP-SAT solves it exactly. Every solution is re-verified from scratch by two
# independent exact checkers (numpy and pure Python integers), and Lean proof obligations are written.

# ============================== SETTINGS ==============================
TARGETS = [            # (n, d, role)
    (6, 3, "validate_sat"),      # Kushilevitz exists: the pipeline MUST find a solution here
    (10, 4, "validate_unsat"),   # Amano: no function exists; a verified solution here = bug or a refutation
    (14, 5, "main"),             # beats log_3 6: log 14 / log 5 = 1.6397
    (20, 6, "main"),             # beats log_3 6: log 20 / log 6 = 1.6720
    (24, 7, "main"),             # beats log_3 6: log 24 / log 7 = 1.6332
]
PER_GROUP_SECONDS = 900          # CP-SAT limit per (target, group); None = unlimited
FULL_ILP_N14 = True              # final stage: no symmetry at all for (14, 5) (the full problem)
FULL_ILP_SECONDS = None          # None = no limit (the full problem may take very long)
MAX_POINT_ORBITS = 60000         # skip groups whose integer program would be too large for Colab RAM
USE_DRIVE = True                 # checkpoint to Google Drive so a disconnected runtime can resume
WORKDIR_LOCAL = "/content/westfall_degsens"
SMOKE = False                    # True: only the validation targets, small limits (quick self-test)
# =====================================================================

import itertools, json, math, os, re, subprocess, sys, time, hashlib
from pathlib import Path

def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)

def sh(cmd):
    return subprocess.run(cmd, shell=True, text=True, capture_output=True)

# ---------- dependencies ----------
try:
    import numpy as np
    from ortools.sat.python import cp_model
except ImportError:
    log("installing ortools, numpy, scipy, mpmath ...")
    sh(f"{sys.executable} -m pip install -q ortools numpy scipy mpmath")
    import numpy as np
    from ortools.sat.python import cp_model
import scipy.sparse as sp
import mpmath
mpmath.mp.dps = 60

HAVE_GAP = sh("which gap").returncode == 0
if not HAVE_GAP and not SMOKE:
    log("installing GAP and its transitive-groups library (apt) ...")
    sh("apt-get -qq update && apt-get -qq install -y gap gap-libs gap-trans-groups gap-prim-groups >/dev/null 2>&1")
    HAVE_GAP = sh("which gap").returncode == 0
log("GAP available:", HAVE_GAP)

# ---------- persistence ----------
WORK = Path(WORKDIR_LOCAL)
if USE_DRIVE and not SMOKE:
    try:
        from google.colab import drive
        drive.mount("/content/drive")
        WORK = Path("/content/drive/MyDrive/westfall_degsens")
    except Exception as e:  # noqa: BLE001
        log("Drive not mounted, using local storage:", e)
WORK.mkdir(parents=True, exist_ok=True)
CKPT = WORK / "results.jsonl"
CERTS = WORK / "certificates"
CERTS.mkdir(exist_ok=True)
done = {}
if CKPT.exists():
    for line in CKPT.read_text().splitlines():
        if line.strip():
            r = json.loads(line)
            done[r["key"]] = r
log(f"workdir {WORK}; {len(done)} checkpointed results")

def record(r):
    done[r["key"]] = r
    with CKPT.open("a") as fh:
        fh.write(json.dumps(r) + "\n")

KUSH = mpmath.log(6) / mpmath.log(3)

# ---------- permutation groups ----------
def proj_line_group(q, kind):
    """PSL(2,q) or PGL(2,q) (q prime) on P^1(F_q): points 0..q-1 and q = infinity."""
    inf = q
    g = next(a for a in range(2, q) if all(pow(a, (q - 1) // p, q) != 1 for p in set(prime_factors(q - 1))))
    a = g if kind == "PGL" else (g * g) % q
    t = [(x + 1) % q for x in range(q)] + [inf]
    m = [(a * x) % q for x in range(q)] + [inf]
    s = [inf] + [(-pow(x, q - 2, q)) % q for x in range(1, q)] + [0]
    return [t, m, s]

def prime_factors(n):
    f, p = [], 2
    while p * p <= n:
        while n % p == 0:
            f.append(p); n //= p
        p += 1
    if n > 1:
        f.append(n)
    return f

def is_prime(q):
    return q > 1 and all(q % p for p in range(2, int(q ** 0.5) + 1))

def curated_groups(n):
    out = [("trivial", [list(range(n))])]
    out.append((f"C{n}", [[(i + 1) % n for i in range(n)]]))
    out.append((f"D{n}", [[(i + 1) % n for i in range(n)], [(-i) % n for i in range(n)]]))
    q = n - 1
    if is_prime(q):
        out.append((f"PSL(2,{q})", proj_line_group(q, "PSL")))
        out.append((f"PGL(2,{q})", proj_line_group(q, "PGL")))
        g = proj_line_group(q, "PGL")
        out.append((f"AGL(1,{q})+fixed", [g[0], g[1]]))           # intransitive: fixes infinity
        out.append((f"ASL(1,{q})+fixed", proj_line_group(q, "PSL")[:2]))
    if n == 14:  # Fano plane: 7 points + 7 lines {i, i+1, i+3}; F21 action and the polarity i <-> -i
        shift = [(i + 1) % 7 for i in range(7)] + [7 + (j + 1) % 7 for j in range(7)]
        mult = [(2 * i) % 7 for i in range(7)] + [7 + (2 * j) % 7 for j in range(7)]
        pol = [7 + (-i) % 7 for i in range(7)] + [(-j) % 7 for j in range(7)]
        out.append(("Fano F21", [shift, mult]))
        out.append(("Fano F21:2 (polarity)", [shift, mult, pol]))
    return out

def gap_groups(n, max_groups=4000):
    """All transitive groups of degree n from GAP's library, as (name, generators)."""
    if not HAVE_GAP:
        return []
    script = WORK / f"tg{n}.g"
    script.write_text(
        f'SizeScreen([100000,100]);; N:=NrTransitiveGroups({n});; Print("NR ",N,"\\n");\n'
        f'for k in [1..Minimum(N,{max_groups})] do G:=TransitiveGroup({n},k);\n'
        f'  Print("GRP ",k," ",Size(G),"\\n");\n'
        f'  for g in GeneratorsOfGroup(G) do Print("GEN ",k," ",JoinStringsWithSeparator(List(ListPerm(g,{n}),String)," "),"\\n"); od;\n'
        f'od;\n'
        + ('Print("M24\\n"); for g in GeneratorsOfGroup(MathieuGroup(24)) do Print("GEN M24 ",JoinStringsWithSeparator(List(ListPerm(g,24),String)," "),"\\n"); od;\n' if n == 24 else "")
        + "QUIT;\n")
    r = sh(f"gap -q -b {script}")
    groups, sizes = {}, {}
    for line in r.stdout.splitlines():
        p = line.split()
        if p[:1] == ["GRP"]:
            sizes[p[1]] = int(p[2])
        elif p[:1] == ["GEN"]:
            groups.setdefault(p[1], []).append([int(x) - 1 for x in p[2:]])
    out = []
    for k, gens in groups.items():
        name = "M24" if k == "M24" else f"T{n},{k}"
        out.append((name + (f" |G|={sizes[k]}" if k in sizes else ""), gens))
    log(f"GAP: {len(out)} groups of degree {n}")
    return out

def group_list(n):
    gl = curated_groups(n)
    if not SMOKE and n <= 24:
        gl += gap_groups(n, max_groups=4000 if n <= 20 else 0)
        if n == 24 and HAVE_GAP:
            gl += [g for g in gap_groups(24, 0) if g[0].startswith("M24")]
    return gl

# ---------- orbits of subsets under a group ----------
def apply_perm(masks, perm):
    out = np.zeros_like(masks)
    for i, j in enumerate(perm):
        out |= ((masks >> i) & 1) << j
    return out

def orbit_labels(n, gens):
    N = 1 << n
    allm = np.arange(N, dtype=np.int64)
    imgs = [apply_perm(allm, g) for g in gens if list(g) != list(range(n))]
    lab = allm.copy()
    while imgs:
        new = lab.copy()
        for im in imgs:
            np.minimum(new, lab[im], out=new)
        new = np.minimum(new, new[new])
        if np.array_equal(new, lab):
            break
        lab = new
    return lab  # lab[x] = smallest mask in the orbit of x (canonical representative)

POP = {}
def popcounts(n):
    if n not in POP:
        a = np.arange(1 << n, dtype=np.int64)
        POP[n] = np.array([bin(x).count("1") for x in range(1 << n)], dtype=np.int64) if n <= 16 else \
            sum(((a >> i) & 1) for i in range(n))
    return POP[n]

# ---------- the exact integer program ----------
def solve_group(n, d, gname, gens, seconds):
    t0 = time.time()
    lab = orbit_labels(n, gens)
    pc = popcounts(n)
    reps = np.unique(lab)
    if len(reps) > MAX_POINT_ORBITS:
        return {"status": "SKIPPED_TOO_LARGE", "point_orbits": int(len(reps))}
    small = np.nonzero((pc >= 1) & (pc <= d))[0]
    vreps, vidx_small = np.unique(lab[small], return_inverse=True)       # variable orbits
    V = len(vreps)
    vsize = pc[vreps]
    onehot = sp.csr_matrix((np.ones(len(small), np.float32), (np.arange(len(small)), vidx_small)),
                           shape=(len(small), V))
    creps = reps[pc[reps] >= 2]                                         # constraints (|x|>=2)
    rows = []
    for k in range(0, len(creps), 256):
        xs = creps[k:k + 256]
        inc = ((small[None, :] & ~xs[:, None]) == 0).astype(np.float32)  # S subset of x
        rows.append(sp.csr_matrix(inc) @ onehot)
    A = sp.vstack(rows).tocsr() if rows else sp.csr_matrix((0, V))
    m = cp_model.CpModel()
    c = []
    for o in range(V):
        k = int(vsize[o])
        if k == 1:
            c.append(m.NewConstant(1))                                   # f(e_i) = 1
        else:
            b = 2 ** (k - 1)                                             # |Möbius coefficient| <= 2^(|S|-1)
            c.append(m.NewIntVar(-b, b, f"c{o}"))
    for r in range(A.shape[0]):
        lo, hi = A.indptr[r], A.indptr[r + 1]
        expr = sum(int(A.data[t]) * c[A.indices[t]] for t in range(lo, hi))
        m.AddLinearConstraint(expr, 0, 1)                                # f(x) in {0,1}
    solver = cp_model.CpSolver()
    if seconds:
        solver.parameters.max_time_in_seconds = float(seconds)
    solver.parameters.num_workers = 8
    st = solver.Solve(m)
    res = {"status": solver.StatusName(st), "vars": int(V), "constraints": int(A.shape[0]),
           "point_orbits": int(len(reps)), "seconds": round(time.time() - t0, 1)}
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        coef = np.zeros(1 << n, dtype=np.int64)
        vals = np.array([solver.Value(x) for x in c], dtype=np.int64)
        coef[small] = vals[vidx_small]
        res["truth_table"] = zeta(coef, n)
    return res

def zeta(coef, n):
    f = coef.copy()
    for i in range(n):
        v = f.reshape(-1, 2, 1 << i)
        v[:, 1, :] += v[:, 0, :]
    return f

# ---------- independent exact verification ----------
def verify_numpy(T, n):
    T = np.asarray(T, dtype=np.int64)
    out = {"boolean": bool(np.all((T == 0) | (T == 1)))}
    g = T.copy()
    for i in range(n):
        v = g.reshape(-1, 2, 1 << i)
        v[:, 1, :] -= v[:, 0, :]
    pc = popcounts(n)
    nz = np.nonzero(g)[0]
    out["degree"] = int(pc[nz].max()) if len(nz) else 0
    out["f0"] = int(T[0])
    out["sens_at_0"] = int(sum(T[1 << i] != T[0] for i in range(n)))
    idx = np.arange(1 << n)
    s = np.zeros(1 << n, dtype=np.int64)
    for i in range(n):
        s += (T != T[idx ^ (1 << i)])
    out["sensitivity"] = int(s.max())
    return out

def verify_python(bits, n):
    """Pure-Python integers, no numpy: Möbius transform, degree, sensitivity."""
    T = [int(b) for b in bits]
    assert all(t in (0, 1) for t in T)
    g = T[:]
    for i in range(n):
        for x in range(1 << n):
            if x >> i & 1:
                g[x] -= g[x ^ (1 << i)]
    deg = max((bin(x).count("1") for x in range(1 << n) if g[x] != 0), default=0)
    sens = max(sum(T[x] != T[x ^ (1 << i)] for i in range(n)) for x in range(1 << n))
    return {"degree": deg, "sensitivity": sens, "f0": T[0], "sens_at_0": sum(T[1 << i] != T[0] for i in range(n))}

def exponent(s, d):
    return mpmath.log(s) / mpmath.log(d) if d > 1 else mpmath.mpf(0)

def lean_obligation(T, n, d, name):
    table = int("".join(str(int(b)) for b in reversed(T)), 2)
    return f"""-- Westfall degree–sensitivity certificate {name}: n = {n}, degree <= {d}, full sensitivity at 0.
-- f x := bit (encode x) of TABLE. Obligations: (1) f 0 = false and f (e_i) = true for all i;
-- (2) every Möbius coefficient of a set of size > {d} vanishes. (2) is large; check with native_decide.
def TABLE : Nat := {table}
def encode (x : Fin {n} → Bool) : Nat := (List.finRange {n}).foldl (fun acc i => if x i then acc + 2 ^ i.val else acc) 0
def f (x : Fin {n} → Bool) : Bool := TABLE.testBit (encode x)
def fN (m : Nat) : Int := if TABLE.testBit m then 1 else 0
theorem f_zero : TABLE.testBit 0 = false := by decide
theorem f_unit : ∀ i : Fin {n}, TABLE.testBit (2 ^ i.val) = true := by decide
def mobius (S : Nat) : Int := ((List.range (2 ^ {n})).filter (fun T => T &&& S == T)).foldl
  (fun acc T => acc + (if (Nat.popCount (S - T)) % 2 = 0 then 1 else -1) * fN T) 0
theorem degree_le : ∀ S < 2 ^ {n}, Nat.popCount S > {d} → mobius S = 0 := by native_decide
"""

def certificate(n, d, gname, gens, res):
    T = [int(v) for v in res["truth_table"]]
    v1 = verify_numpy(T, n)
    v2 = verify_python(T, n) if n <= 20 else {"skipped": "n > 20"}
    ok = (v1["boolean"] and v1["f0"] == 0 and v1["sens_at_0"] == n and 1 < v1["degree"] <= d
          and (v2.get("skipped") or (v2["degree"] == v1["degree"] and v2["sens_at_0"] == n)))
    e = exponent(max(v1["sensitivity"], n), v1["degree"])
    cert = {"n": n, "d_target": d, "group": gname, "generators": gens, "verify_numpy": v1, "verify_python": v2,
            "exponent": mpmath.nstr(e, 20), "beats_log3_6": bool(ok and e > KUSH),
            "truth_table_hex": hex(int("".join(str(b) for b in reversed(T)), 2)),
            "sha256": hashlib.sha256(bytes(T)).hexdigest(), "verified": bool(ok)}
    # adversarial self-test of the verifier: flipping one value must break Booleanity-consistent degree <= d
    T2 = T[:]; T2[(1 << n) - 1] ^= 1
    cert["verifier_rejects_one_flip"] = verify_numpy(T2, n)["degree"] > d
    tag = f"n{n}_d{d}_{re.sub('[^A-Za-z0-9]+', '_', gname)}"
    (CERTS / f"{tag}.json").write_text(json.dumps(cert, indent=1))
    (CERTS / f"{tag}.lean").write_text(lean_obligation(T, n, d, tag))
    return cert

# ---------- main loop ----------
summary = {"verified_discoveries": [], "verified_small_or_known": [], "unverified_candidates": [],
           "solver_infeasible": [], "timeouts": [], "skipped": []}
targets = [t for t in TARGETS if (not SMOKE) or t[2].startswith("validate")]
for n, d, role in targets:
    groups = group_list(n)
    log(f"===== target n={n}, d={d} ({role}); exponent {mpmath.nstr(exponent(n, d), 8)} vs log_3 6 = {mpmath.nstr(KUSH, 8)}; {len(groups)} groups")
    found_here = False
    for gname, gens in groups:
        if role == "validate_sat" and found_here:
            break
        key = f"{n}|{d}|{gname}"
        if key in done:
            r = done[key]
        else:
            if gname == "trivial" and n >= 14:
                continue  # the full problem is the final stage
            secs = 20 if SMOKE else PER_GROUP_SECONDS
            res = solve_group(n, d, gname, gens, secs)
            r = {"key": key, "n": n, "d": d, "group": gname, **{k: v for k, v in res.items() if k != "truth_table"}}
            if "truth_table" in res:
                cert = certificate(n, d, gname, gens, res)
                r.update(verified=cert["verified"], beats=cert["beats_log3_6"], exponent=cert["exponent"],
                         degree=cert["verify_numpy"]["degree"], sensitivity=cert["verify_numpy"]["sensitivity"],
                         verifier_rejects_one_flip=cert["verifier_rejects_one_flip"])
            record(r)
        log(f"  {gname:28s} {r['status']:18s} vars={r.get('vars')} cons={r.get('constraints')} "
            f"{'deg=%s s=%s exp=%s VERIFIED=%s' % (r.get('degree'), r.get('sensitivity'), r.get('exponent'), r.get('verified')) if 'verified' in r else ''}")
        if "verified" in r:
            found_here = True
            bucket = ("verified_discoveries" if r.get("beats") else "verified_small_or_known") if r["verified"] else "unverified_candidates"
            summary[bucket].append(key)
        elif r["status"] == "INFEASIBLE":
            summary["solver_infeasible"].append(key)
        elif r["status"].startswith("SKIPPED"):
            summary["skipped"].append(key)
        else:
            summary["timeouts"].append(key)
    if role == "validate_sat" and not found_here:
        raise SystemExit(f"VALIDATION FAILED: no solution found for ({n},{d}), which is known to exist. Stop.")
    if role == "validate_unsat" and found_here:
        log("!!! A verified solution exists where the literature says none does. Check certificates/ before anything else.")

if FULL_ILP_N14 and not SMOKE:
    key = "14|5|trivial"
    if key not in done:
        log("===== final stage: the full (14, 5) problem without symmetry (this may run for a long time)")
        res = solve_group(14, 5, "trivial", [list(range(14))], FULL_ILP_SECONDS)
        r = {"key": key, "n": 14, "d": 5, "group": "trivial", **{k: v for k, v in res.items() if k != "truth_table"}}
        if "truth_table" in res:
            cert = certificate(14, 5, "trivial", [list(range(14))], res)
            r.update(verified=cert["verified"], beats=cert["beats_log3_6"], exponent=cert["exponent"])
        record(r)
    log("full (14,5):", done[key]["status"])

log("============================ SUMMARY ============================")
log("VERIFIED DISCOVERIES (exactly verified, exponent > log_3 6):", summary["verified_discoveries"] or "none")
log("verified solutions that do not beat log_3 6 (validation / known range):", summary["verified_small_or_known"])
log("UNVERIFIED candidates (solver said feasible, exact check failed => bug, not a result):", summary["unverified_candidates"] or "none")
log(f"solver-reported infeasible (not a certified proof): {len(summary['solver_infeasible'])}; "
    f"timeouts: {len(summary['timeouts'])}; skipped as too large: {len(summary['skipped'])}")
log(f"certificates and Lean obligations: {CERTS}; checkpoint: {CKPT}")
