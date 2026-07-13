"""Collect concise Figure 2 comparison artifacts into one validation matrix."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

from experiments.scripts.morse_singleton_workload import atomic_write_json, file_sha256


REPO_ROOT = Path(__file__).resolve().parents[2]


def command(argv):
    try:
        return subprocess.check_output(
            argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--run-metadata", action="append", type=Path, default=[])
    parser.add_argument("comparisons", nargs="+", type=Path)
    args = parser.parse_args()

    rows = []
    for path in args.comparisons:
        payload = json.loads(path.read_text())
        rows.append(
            {
                "source": str(path),
                "source_sha256": file_sha256(path),
                "source_schema": payload.get("schema"),
                "status": payload["status"],
                "category": payload["category"],
                "category_id": payload["category_id"],
                "standard_character": payload["standard_character"],
                "yasui_raw": payload["yasui_raw"],
                "yasui_normalized": payload["yasui_normalized"],
                "standard_cp2_plus_one_omega": payload[
                    "standard_cp2_plus_one_omega"
                ],
                "difference": payload["difference"],
                "normalization_convention": payload["normalization_convention"],
                "environment": payload.get("environment"),
                "utc_start": payload.get("utc_start"),
                "utc_finish": payload.get("utc_finish"),
                "elapsed_seconds": payload.get("elapsed_seconds"),
            }
        )
    rows.sort(key=lambda row: (row["category_id"], row["standard_character"]))
    metadata = []
    for path in args.run_metadata:
        item = json.loads(path.read_text())
        metadata.append(
            {
                "path": str(path),
                "sha256": file_sha256(path),
                "schema": item.get("schema"),
                "status": item.get("status"),
                "run_id": item.get("run_id"),
                "category": item.get("category"),
                "workers": item.get("workers"),
                "utc_start": item.get("utc_start"),
                "utc_finish": item.get("utc_finish"),
                "elapsed_seconds": item.get("elapsed_seconds"),
                "repo": item.get("repo"),
                "environment": item.get("environment"),
            }
        )
    payload = {
        "schema": "twisted-yetter.native-morse-figure2-cross-category-matrix.v1",
        "status": "pass" if all(row["status"] == "pass" for row in rows) else "needs-review",
        "mathematical_status": "NUMERICAL_CROSS_PRESENTATION_CONSISTENCY_MATRIX_NOT_A_THEOREM",
        "generator_script": "experiments/scripts/morse_collect_comparison_matrix.py",
        "argv": sys.argv,
        "comparison_count": len(rows),
        "comparisons": rows,
        "run_metadata": metadata,
        "scope": {
            "presentation": "Yasui Figure 2 CP2(a=1), corrected R1 Morse transcription",
            "comparison": "Tham 5.11 D^-2 normalization versus standard +1-framed CP2 presentation",
            "categories": sorted({row["category"] for row in rows}),
            "warning": "This validates the current evaluator on the recorded cases; universal is an engineering scope claim, not a theorem about all fusion categories.",
        },
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "git_dirty": bool(command(["git", "status", "--short"])),
        },
        "environment": {
            "hostname": platform.node(),
            "platform": platform.platform(),
            "python": sys.version,
            "cpu_count": os.cpu_count(),
        },
        "generated_at_utc": datetime.now(UTC).isoformat(),
    }
    atomic_write_json(args.output, payload)
    print(args.output.resolve())
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
