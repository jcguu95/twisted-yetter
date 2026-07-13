"""Compute the heuristic optimistic runtime floor from compact E(2) probes."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import json
import math
from pathlib import Path
import subprocess


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_value(*args: str) -> str | None:
    try:
        return subprocess.check_output(["git", *args], text=True).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--probe", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    probe = json.loads(args.probe.read_text())
    component_count = int(probe["component_count"])
    simple_object_count = int(probe["simple_object_count"])
    threshold = float(probe["fast_threshold_seconds"])
    total = simple_object_count**component_count
    estimated_fast = 0.0
    for row in probe["no_sigma_strata"]:
        population = math.comb(component_count, int(row["two_count"]))
        estimated_fast += population * int(row["fast_count"]) / int(row["sample_count"])

    optimistic_seconds = (total - estimated_fast) * threshold
    script_path = Path(__file__).resolve()
    result = {
        "schema": "twisted-yetter.e2-su2-2-optimistic-runtime-floor.v1",
        "status": "HEURISTIC_OPTIMISTIC_RUNTIME_FLOOR_NOT_RIGOROUS_BOUND",
        "generator_script": str(script_path.relative_to(Path.cwd())),
        "generator_script_sha256": sha256(script_path),
        "generator_script_git_blob": git_value("hash-object", str(script_path)),
        "probe": str(args.probe),
        "probe_sha256": sha256(args.probe),
        "sector_total": total,
        "estimated_fast_sector_count": estimated_fast,
        "fast_threshold_seconds": threshold,
        "optimistic_worker_seconds": optimistic_seconds,
        "optimistic_worker_years": optimistic_seconds / (365.25 * 24 * 3600),
        "optimistic_two_worker_years": optimistic_seconds / (2 * 365.25 * 24 * 3600),
        "optimistic_120_worker_days": optimistic_seconds / (120 * 24 * 3600),
        "assumptions": [
            "No-sigma stratum sample rates are extrapolated to their full strata.",
            "Uncounted fast sectors are ignored.",
            "Estimated fast sectors cost zero seconds.",
            "Every remaining sector costs exactly the 0.01-second threshold.",
        ],
        "repo": {
            "git_commit": git_value("rev-parse", "HEAD"),
            "git_dirty": bool(git_value("status", "--short")),
        },
        "utc_finish": datetime.now(UTC).isoformat(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
