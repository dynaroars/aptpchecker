#!/usr/bin/env python3
"""Measure end-to-end kernel certification over the VIPR benchmark corpus.

Infeasibility certificates use reconstruction (slice + subset proof + kernel
replay). Range certificates use complete kernel replay because reconstruction is
not implemented for range results.
"""

from __future__ import annotations

import argparse
import csv
import os
import signal
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--checker", type=Path, default=REPO / ".lake/build/bin/viprcheck")
    p.add_argument("--infeas-dir", type=Path, default=ROOT / "infeas")
    p.add_argument("--range-dir", type=Path, default=ROOT / "range")
    p.add_argument("--output", type=Path, default=ROOT / "results/kernel.csv")
    p.add_argument("--timeout", type=float, default=300.0, help="per-instance seconds")
    p.add_argument(
        "--classes",
        nargs="+",
        choices=("infeas", "range"),
        default=("infeas", "range"),
        help="result classes to measure",
    )
    p.add_argument("--no-warmup", action="store_true")
    return p.parse_args()


def terminate_process_group(proc: subprocess.Popen[str]) -> str:
    if proc.poll() is not None:
        out, _ = proc.communicate()
        return out
    os.killpg(proc.pid, signal.SIGTERM)
    try:
        out, _ = proc.communicate(timeout=5)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, _ = proc.communicate()
    return out


def run_one(
    checker: Path, cert: Path, kernel_mode: str, proof_dir: Path, timeout: float
) -> tuple[dict[str, str], str]:
    cmd = [str(checker), "--kernel-mode", kernel_mode, str(cert),
           "--proof-dir", str(proof_dir)]
    env = os.environ.copy()
    env["VIPR_LAKE"] = "lake"
    start = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        cwd=REPO,
        env=env,
        start_new_session=True,
    )
    try:
        out, _ = proc.communicate(timeout=timeout)
        wall = time.monotonic() - start
        if "ACCEPT" in out and proc.returncode == 0:
            status = "pass"
        else:
            status = "reject"
        # Sanity-check that the generated proof did not introduce a known escape hatch.
        clean = ("sorryAx" not in out) and ("ofReduceBool" not in out)
        if status == "pass" and not clean:
            status = "unclean"
        return {
            "wall_s": f"{wall:.2f}",
            "timeout_s": f"{timeout:.0f}",
            "status": status,
            "returncode": str(proc.returncode),
        }, out
    except subprocess.TimeoutExpired:
        out = terminate_process_group(proc)
        wall = time.monotonic() - start
        return {
            "wall_s": f"{wall:.2f}",
            "timeout_s": f"{timeout:.0f}",
            "status": "timeout",
            "returncode": "",
        }, out
    except KeyboardInterrupt:
        terminate_process_group(proc)
        raise


def main() -> None:
    args = parse_args()
    jobs: list[tuple[Path, str, str]] = []
    if "infeas" in args.classes:
        jobs.extend((cert, "infeas", "reconstruct") for cert in args.infeas_dir.glob("*.vipr"))
    if "range" in args.classes:
        jobs.extend((cert, "range", "full") for cert in args.range_dir.glob("*.vipr"))
    # Smallest-first so results stream in and likely timeouts run last.
    jobs.sort(key=lambda job: job[0].stat().st_size)
    if not jobs:
        raise SystemExit("no certificates selected")
    args.output.parent.mkdir(parents=True, exist_ok=True)

    if not args.no_warmup:
        warm, _, warm_mode = jobs[0]
        print(f"warmup: {warm.stem} ({warm_mode})", flush=True)
        with tempfile.TemporaryDirectory(prefix="vipr-kernel-warm-") as proof_dir:
            run_one(args.checker, warm, warm_mode, Path(proof_dir), args.timeout)

    rows = []
    fields = [
        "instance",
        "rtp",
        "mode",
        "wall_s",
        "timeout_s",
        "status",
        "returncode",
    ]
    for cert, rtp, kernel_mode in jobs:
        inst = cert.stem
        with tempfile.TemporaryDirectory(prefix=f"vipr-kernel-{inst}-") as proof_dir:
            res, output = run_one(
                args.checker, cert, kernel_mode, Path(proof_dir), args.timeout
            )
        rows.append({
            "instance": inst,
            "rtp": rtp,
            "mode": f"kernel-{kernel_mode}",
            **res,
        })
        print(
            f"{inst:12s}  {kernel_mode:11s}  {res['status']:8s}  "
            f"{res['wall_s']:>8s}s",
            flush=True,
        )
        if res["status"] not in ("pass", "timeout"):
            print(output, flush=True)
        # rewrite after every instance so an interruption keeps partial data
        with args.output.open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=fields)
            w.writeheader()
            w.writerows(rows)
    print(f"\nwrote {args.output}")


if __name__ == "__main__":
    main()
