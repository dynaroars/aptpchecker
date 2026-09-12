#!/usr/bin/env python3
"""Generate integer MILPs, run exact SCIP, keep only UNSAT VIPR pairs that branch.

Pairs are named alike, e.g. prob1.mps / prob1.vipr. A pair is kept only if SCIP
proves infeasibility and the certificate contains an `uns` (case-split). Instances
are knapsack-like: the LP relaxation is feasible, the integer hull is empty, and
gcd(weights)=1 so a single modular cut does not finish the proof.

Run from lean_impl/benchmark/ (APTP_SCIP or --scip if `scip` is not on PATH):

  python3 generate_samples.py --n-vars 5 --n-constraints 5 --n-problems 20 --out-dir 5x5
  python3 generate_samples.py --n-vars 5 --n-constraints 10 --n-problems 20 --out-dir 5x10
  python3 generate_samples.py --n-vars 10 --n-constraints 10 --n-problems 20 --out-dir 10x10
  python3 generate_samples.py --n-vars 10 --n-constraints 20 --n-problems 20 --out-dir 10x20
  python3 generate_samples.py --n-vars 20 --n-constraints 20 --n-problems 20 --out-dir 20x20
"""

from __future__ import annotations

import argparse
import math
import os
import random
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

N_VARS = 4
N_CONSTRAINTS = 3
N_PROBLEMS = 5

# Coprime-friendly knapsack weights (same family as uns_knapsack: 6,10,15).
WEIGHT_POOL = (4, 6, 9, 10, 14, 15, 21, 22, 25, 26, 33, 34, 35, 38, 39)

DEFAULT_SCIP_CANDIDATES = (
    Path.home() / "opt/scipoptsuite-10.0.1/build/bin/scip",
)


def find_scip(explicit: str | None) -> str:
    if explicit:
        return explicit
    env = os.environ.get("APTP_SCIP")
    if env:
        return env
    which = shutil.which("scip")
    if which:
        return which
    for cand in DEFAULT_SCIP_CANDIDATES:
        if cand.is_file():
            return str(cand)
    sys.exit("SCIP not found. Pass --scip or set APTP_SCIP.")


def gcd_all(xs: list[int]) -> int:
    g = 0
    for x in xs:
        g = math.gcd(g, x)
    return g


def achievable_sums(weights: list[int], ubs: list[int]) -> set[int]:
    possible = {0}
    for w, ub in zip(weights, ubs):
        nxt = set(possible)
        for s in possible:
            for k in range(1, ub + 1):
                nxt.add(s + k * w)
        possible = nxt
    return possible


def fractional_point(weights: list[int], ubs: list[int], t: int) -> list[float] | None:
    for j, w in enumerate(weights):
        q = t / w
        if 0 <= q <= ubs[j] + 1e-12:
            x = [0.0] * len(weights)
            x[j] = q
            return x
    x = [0.0] * len(weights)
    rem = float(t)
    for j, w in enumerate(weights):
        take = min(float(ubs[j]), rem / w)
        x[j] = take
        rem -= take * w
        if rem < 1e-9:
            return x
    return None


def generate_instance(
    n_vars: int, n_cons: int, rng: random.Random
) -> tuple[list[list[int]], list[str], list[int], list[int], list[int]] | None:
    """Knapsack equality with a bounded-sum gap; extra rows keep a fractional point."""
    weights = [rng.choice(WEIGHT_POOL) for _ in range(n_vars)]
    if gcd_all(weights) != 1:
        weights[-1] = rng.choice((5, 7, 11, 13, 15))
    if gcd_all(weights) != 1:
        return None
    ubs = [rng.randint(1, 3) for _ in range(n_vars)]
    lbs = [0] * n_vars
    sums = achievable_sums(weights, ubs)
    max_s = max(sums)
    gaps = [t for t in range(min(weights), max_s) if t not in sums]
    if not gaps:
        return None
    t = rng.choice(gaps)
    xfrac = fractional_point(weights, ubs, t)
    if xfrac is None:
        return None

    A = [[0] * n_vars for _ in range(n_cons)]
    senses = ["L"] * n_cons
    b = [0] * n_cons
    A[0] = list(weights)
    senses[0] = "E"
    b[0] = t
    extra_from = 1
    if n_cons >= 2 and sum(xfrac) >= 1.0 - 1e-9:
        A[1] = [1] * n_vars
        senses[1] = "G"
        b[1] = 1
        extra_from = 2
    for i in range(extra_from, n_cons):
        coeffs = [rng.randint(-5, 5) for _ in range(n_vars)]
        if all(c == 0 for c in coeffs):
            coeffs[rng.randrange(n_vars)] = 1
        val = sum(c * xj for c, xj in zip(coeffs, xfrac))
        if rng.random() < 0.5:
            senses[i] = "L"
            b[i] = math.floor(val) + rng.randint(1, 4)
        else:
            senses[i] = "G"
            b[i] = math.ceil(val) - rng.randint(1, 4)
        A[i] = coeffs
    return A, senses, b, lbs, ubs


def write_mps(
    path: Path,
    name: str,
    A: list[list[int]],
    senses: list[str],
    b: list[int],
    lbs: list[int],
    ubs: list[int],
) -> None:
    n_cons, n_vars = len(senses), len(lbs)
    lines = [f"NAME {name}", "ROWS", " N obj"]
    for i, sense in enumerate(senses):
        lines.append(f" {sense} c{i}")
    lines.append("COLUMNS")
    lines.append("    M1 'MARKER' 'INTORG'")
    for j in range(n_vars):
        entries = [(f"c{i}", A[i][j]) for i in range(n_cons) if A[i][j] != 0]
        if not entries:
            lines.append(f"    x{j} obj 0")
        else:
            for k in range(0, len(entries), 2):
                chunk = " ".join(f"{rn} {val}" for rn, val in entries[k : k + 2])
                lines.append(f"    x{j} {chunk}")
    lines.append("    M2 'MARKER' 'INTEND'")
    lines.append("RHS")
    for i, rhs in enumerate(b):
        lines.append(f"    rhs c{i} {rhs}")
    lines.append("BOUNDS")
    for j in range(n_vars):
        lines.append(f" LI BND x{j} {lbs[j]}")
        lines.append(f" UI BND x{j} {ubs[j]}")
    lines.append("ENDATA")
    path.write_text("\n".join(lines) + "\n")


def vipr_text(path: Path) -> str:
    if not path.is_file() or path.stat().st_size == 0:
        return ""
    return path.read_text(errors="replace")


def vipr_is_infeas(text: str) -> bool:
    return "RTP infeas" in text or "RTP\ninfeas" in text


def vipr_has_uns(text: str) -> bool:
    return "{ uns" in text


def run_scip(scip: str, mps: Path, vipr: Path, timeout: float) -> str:
    if vipr.exists():
        vipr.unlink()
    cmd = [
        scip,
        "-c", "set exact enable TRUE",
        "-c", "set presolving maxrounds 0",
        "-c", "set separating maxrounds 0",
        "-c", "set separating maxroundsroot 0",
        "-c", f"set limits time {timeout}",
        "-c", f"set certificate filename {vipr}",
        "-c", f"read {mps}",
        "-c", "optimize",
        "-c", "quit",
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if "problem is solved [infeasible]" in out:
        return "infeasible"
    if "optimal solution found" in out:
        return "feasible"
    if "time limit" in out.lower():
        return "timeout"
    return "other"


def parse_args() -> argparse.Namespace:
    here = Path(__file__).resolve().parent
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--n-vars", type=int, default=N_VARS, help="number of integer variables")
    p.add_argument("--n-constraints", type=int, default=N_CONSTRAINTS, help="number of rows")
    p.add_argument("--n-problems", type=int, default=N_PROBLEMS, help="UNSAT+uns pairs to keep")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--timeout", type=float, default=30.0, help="SCIP time limit (seconds)")
    p.add_argument("--max-attempts", type=int, default=0, help="0 → 50× n-problems")
    p.add_argument("--out-dir", type=Path, default=here)
    p.add_argument("--scip", default=None, help="exact SCIP binary (else APTP_SCIP or PATH)")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    if args.n_vars < 1 or args.n_constraints < 1 or args.n_problems < 1:
        sys.exit("n-vars, n-constraints, and n-problems must be ≥ 1")
    scip = find_scip(args.scip)
    out_dir = args.out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    max_attempts = args.max_attempts or 50 * args.n_problems
    rng = random.Random(args.seed)
    print(
        f"scip={scip}  n_vars={args.n_vars}  n_constraints={args.n_constraints}  "
        f"n_problems={args.n_problems}  seed={args.seed}  out={out_dir}  require=uns"
    )

    kept = 0
    for attempt in range(1, max_attempts + 1):
        if kept >= args.n_problems:
            break
        inst = generate_instance(args.n_vars, args.n_constraints, rng)
        if inst is None:
            print(f"  attempt {attempt}: skip (no knapsack gap / gcd≠1)")
            continue
        A, senses, b, lbs, ubs = inst
        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            stem = f"try{attempt}"
            mps, vipr = tmp_dir / f"{stem}.mps", tmp_dir / f"{stem}.vipr"
            write_mps(mps, stem, A, senses, b, lbs, ubs)
            try:
                status = run_scip(scip, mps, vipr, args.timeout)
            except subprocess.TimeoutExpired:
                status = "timeout"
            text = vipr_text(vipr)
            has_infeas, has_uns = vipr_is_infeas(text), vipr_has_uns(text)
            n_uns = text.count("{ uns")
            print(f"  attempt {attempt}: {status}  infeas={has_infeas}  uns={n_uns}")
            if not (status == "infeasible" and has_infeas and has_uns):
                continue
            kept += 1
            dest_mps = out_dir / f"prob{kept}.mps"
            dest_vipr = out_dir / f"prob{kept}.vipr"
            shutil.copy2(mps, dest_mps)
            shutil.copy2(vipr, dest_vipr)
            print(f"  kept {dest_mps.name} + {dest_vipr.name}  (uns×{n_uns})")

    print(f"kept {kept}/{args.n_problems} UNSAT pairs with uns")
    return 0 if kept == args.n_problems else 2


if __name__ == "__main__":
    raise SystemExit(main())
