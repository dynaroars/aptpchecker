#!/usr/bin/env python3
"""Run the reference C++ VIPR completion-and-checking pipeline sequentially."""

from __future__ import annotations

import argparse
import csv
import subprocess
import tempfile
from decimal import Decimal
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--checker",
        type=Path,
        required=True,
        help="path to the reference viprchk executable",
    )
    parser.add_argument(
        "--completer",
        type=Path,
        required=True,
        help="path to the reference viprcomp executable",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("benchmarks"),
        help="benchmark corpus root",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("benchmarks/results/cpp.csv"),
        help="CSV output path",
    )
    parser.add_argument(
        "--no-warmup",
        action="store_true",
        help="skip the untimed executable warmup",
    )
    parser.add_argument(
        "--fail-fast",
        action="store_true",
        help="stop at the first completion or checking failure",
    )
    return parser.parse_args()


def parse_time(path: Path) -> tuple[str, str, str]:
    values: dict[str, str] = {}
    for line in path.read_text().splitlines():
        key, value = line.split(maxsplit=1)
        values[key] = value
    return values["real"], values["user"], values["sys"]


def run_stage(command: list[str]) -> tuple[int, str, str, str]:
    with tempfile.NamedTemporaryFile(prefix="vipr-cpp-time-", delete=False) as handle:
        time_path = Path(handle.name)
    try:
        completed = subprocess.run(
            ["/usr/bin/time", "-p", "-o", str(time_path), *command],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        wall, user, system = parse_time(time_path)
        return completed.returncode, wall, user, system
    finally:
        time_path.unlink(missing_ok=True)


def run_one(
    checker: Path, completer: Path, certificate: Path, completed_certificate: Path
) -> dict[str, str | int]:
    completion = run_stage(
        [
            str(completer),
            "--soplex=off",
            "--threads=1",
            f"--outfile={completed_certificate}",
            str(certificate),
        ]
    )
    if completion[0] == 0:
        checking = run_stage([str(checker), str(completed_certificate)])
    else:
        checking = (-1, "0.00", "0.00", "0.00")
    status = (
        "pass"
        if completion[0] == 0 and checking[0] == 0
        else f"complete_{completion[0]}_check_{checking[0]}"
    )
    pipeline_wall = Decimal(completion[1]) + Decimal(checking[1])
    try:
        return {
            "instance": certificate.stem,
            "rtp": certificate.parent.name,
            "bytes": certificate.stat().st_size,
            "completion_wall_s": completion[1],
            "completion_user_s": completion[2],
            "completion_sys_s": completion[3],
            "checker_wall_s": checking[1],
            "checker_user_s": checking[2],
            "checker_sys_s": checking[3],
            "pipeline_wall_s": f"{pipeline_wall:.2f}",
            "status": status,
        }
    finally:
        completed_certificate.unlink(missing_ok=True)


def main() -> int:
    args = parse_args()
    checker = args.checker.resolve()
    completer = args.completer.resolve()
    root = args.root.resolve()
    certificates = sorted((root / "infeas").glob("*.vipr"))
    certificates += sorted((root / "range").glob("*.vipr"))
    if not certificates:
        raise SystemExit(f"no VIPR certificates found below {root}")

    with tempfile.TemporaryDirectory(prefix="vipr-cpp-completed-") as directory:
        completed_root = Path(directory)
        if not args.no_warmup:
            warm = min(certificates, key=lambda path: path.stat().st_size)
            warm_completed = completed_root / f"{warm.stem}_warm_complete.vipr"
            subprocess.run(
                [
                    str(completer),
                    "--soplex=off",
                    "--threads=1",
                    f"--outfile={warm_completed}",
                    str(warm),
                ],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=True,
            )
            subprocess.run(
                [str(checker), str(warm_completed)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=True,
            )
            warm_completed.unlink()

        rows: list[dict[str, str | int]] = []
        for certificate in certificates:
            print(f"{certificate.parent.name:6s} {certificate.stem}", flush=True)
            completed_certificate = completed_root / f"{certificate.stem}_complete.vipr"
            row = run_one(checker, completer, certificate, completed_certificate)
            rows.append(row)
            if args.fail_fast and row["status"] != "pass":
                raise SystemExit(f"{certificate} failed: {row['status']}")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {args.output}")
    failures = [row for row in rows if row["status"] != "pass"]
    print(f"{len(rows) - len(failures)} passed; {len(failures)} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
