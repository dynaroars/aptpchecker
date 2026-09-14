#!/usr/bin/env python3
"""Run the native VIPR checker benchmark sequentially and write a CSV report."""

from __future__ import annotations

import argparse
import csv
import re
import subprocess
import tempfile
from pathlib import Path


REPORT_RE = re.compile(
    r"vars (?P<vars>\d+)\s+int (?P<int_vars>\d+)\s+"
    r"con (?P<constraints>\d+)\s+steps (?P<steps>\d+)"
)
REASONS_RE = re.compile(
    r"asm×(?P<asm>\d+)\s+lin×(?P<lin>\d+)\s+rnd×(?P<rnd>\d+)\s+"
    r"uns×(?P<uns>\d+)\s+sol×(?P<sol>\d+)"
)
SLICE_RE = re.compile(
    r"slice: (?P<constraints>\d+) → (?P<sliced_constraints>\d+) constraints,\s+"
    r"(?P<steps>\d+) → (?P<sliced_steps>\d+) steps"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--checker",
        type=Path,
        default=Path(".lake/build/bin/viprcheck"),
        help="path to the compiled checker",
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
        default=Path("benchmarks/results/checker.csv"),
        help="CSV output path",
    )
    parser.add_argument(
        "--no-warmup",
        action="store_true",
        help="skip the untimed executable warmup",
    )
    parser.add_argument(
        "--modes",
        nargs="+",
        choices=("full", "slice"),
        help="override the replay modes (slice modes are skipped for range certificates)",
    )
    return parser.parse_args()


def parse_time(path: Path) -> tuple[str, str, str]:
    values: dict[str, str] = {}
    for line in path.read_text().splitlines():
        key, value = line.split(maxsplit=1)
        values[key] = value
    return values["real"], values["user"], values["sys"]


def run_one(checker: Path, certificate: Path, mode: str) -> dict[str, str | int]:
    with tempfile.NamedTemporaryFile(prefix="vipr-time-", delete=False) as handle:
        time_path = Path(handle.name)
    try:
        command = [
            "/usr/bin/time",
            "-p",
            "-o",
            str(time_path),
            str(checker),
            "--native-mode",
            mode,
            str(certificate),
        ]
        completed = subprocess.run(command, capture_output=True, text=True, check=False)
        output = completed.stdout + completed.stderr
        report = REPORT_RE.search(output)
        reasons = REASONS_RE.search(output)
        sliced = SLICE_RE.search(output)
        if report is None or reasons is None:
            raise RuntimeError(f"could not parse checker report for {certificate}:\n{output}")
        wall, user, system = parse_time(time_path)
        constraints = int(report.group("constraints"))
        steps = int(report.group("steps"))
        return {
            "instance": certificate.stem,
            "rtp": certificate.parent.name,
            "bytes": certificate.stat().st_size,
            "variables": int(report.group("vars")),
            "integer_variables": int(report.group("int_vars")),
            "constraints": constraints,
            "steps": steps,
            "asm": int(reasons.group("asm")),
            "lin": int(reasons.group("lin")),
            "rnd": int(reasons.group("rnd")),
            "uns": int(reasons.group("uns")),
            "sol": int(reasons.group("sol")),
            "checked_constraints": (
                int(sliced.group("sliced_constraints")) if sliced is not None else constraints
            ),
            "checked_steps": int(sliced.group("sliced_steps")) if sliced is not None else steps,
            "mode": mode,
            "wall_s": wall,
            "user_s": user,
            "sys_s": system,
            "status": "pass" if completed.returncode == 0 else f"exit_{completed.returncode}",
        }
    finally:
        time_path.unlink(missing_ok=True)


def main() -> int:
    args = parse_args()
    checker = args.checker.resolve()
    root = args.root.resolve()
    certificates = sorted((root / "infeas").glob("*.vipr"))
    certificates += sorted((root / "range").glob("*.vipr"))
    if not certificates:
        raise SystemExit(f"no VIPR certificates found below {root}")

    if not args.no_warmup:
        warm = min(certificates, key=lambda path: path.stat().st_size)
        subprocess.run(
            [str(checker), "--native-mode", "full", str(warm)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=True,
        )

    rows: list[dict[str, str | int]] = []
    for certificate in certificates:
        if args.modes is None:
            modes = ("full", "slice") if certificate.parent.name == "infeas" else ("full",)
        else:
            modes = tuple(
                mode
                for mode in args.modes
                if certificate.parent.name == "infeas" or not mode.endswith("slice")
            )
        for mode in modes:
            print(f"{certificate.stem:12s} {mode:5s}", flush=True)
            row = run_one(checker, certificate, mode)
            rows.append(row)
            if row["status"] != "pass":
                raise SystemExit(f"{certificate} failed in {mode} mode")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
