#!/usr/bin/env python3
"""Compare SU(3)_2 AnyonWiki Yasui aggregates across selected conventions."""

from __future__ import annotations

from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


REPO_ROOT = Path(__file__).resolve().parents[2]
PRIMARY = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-su3-2-anyonwiki-aggregate-v1.json"
)
CAT2 = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-su3-2-anyonwiki-cat-1-3-2-aggregate-v1.json"
)
PRIMARY_CONTROLS = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "anyon-wiki-su3-2"
    / "su3-2-anyonwiki-fr-braid-evaluator-basic-controls-v1.json"
)
CAT2_CONTROLS = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "anyon-wiki-su3-2"
    / "su3-2-anyonwiki-fr-braid-evaluator-basic-controls-cat-1-3-2-v1.json"
)
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-su3-2-anyonwiki-convention-comparison-v1.json"
)


def read_json(path: Path):
    return json.loads(path.read_text())


def write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(argv: list[str]) -> str | None:
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def complex_from_json(payload: dict[str, str]) -> complex:
    return complex(float(payload["real"]), float(payload["imag"]))


def complex_json(value: complex) -> dict[str, str]:
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def artifact_record(path: Path) -> dict:
    payload = read_json(path)
    return {
        "path": rel(path),
        "sha256": sha256(path),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
    }


def main() -> int:
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    primary = read_json(PRIMARY)
    cat2 = read_json(CAT2)
    controls = read_json(PRIMARY_CONTROLS)
    cat2_controls = read_json(CAT2_CONTROLS)

    primary_ratio = complex_from_json(primary["primary_ratio_to_untwisted"])
    split_ratio = complex_from_json(
        primary["cp2_2cpbar_split_reference"]["primary_ratio_to_baseline"]
    )
    cat2_ratio = complex_from_json(cat2["primary_ratio_to_untwisted"])
    primary_split_ratio_error = primary_ratio - split_ratio
    primary_cat2_ratio_difference = primary_ratio - cat2_ratio

    payload = {
        "schema": "twisted-yetter.yasui-su3-2-anyonwiki-convention-comparison.v1",
        "status": "pass_with_convention_warning",
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/scripts/yasui_su3_2_anyonwiki_convention_compare.py",
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "dirty": bool(command(["git", "status", "--short"])),
            "status_short": command(["git", "status", "--short"]),
        },
        "inputs": {
            "primary_aggregate": artifact_record(PRIMARY),
            "cat_1_3_2_direct_labeled_aggregate": artifact_record(CAT2),
            "primary_controls": artifact_record(PRIMARY_CONTROLS),
            "cat_1_3_2_controls": artifact_record(CAT2_CONTROLS),
        },
        "primary_working_convention": {
            "anyonwiki_category_parameter": primary["category"]["anyonwiki_category_parameter"],
            "braiding_convention": primary["category"]["braiding_convention"],
            "controls_status": controls["status"],
            "yasui_untwisted_raw": primary["aggregate_untwisted"]["raw"],
            "yasui_primary_component_a_twist_raw": primary["aggregate_primary_component_a_twist"]["raw"],
            "yasui_primary_ratio_to_untwisted": primary["primary_ratio_to_untwisted"],
            "cp2_split_primary_ratio_to_baseline": primary["cp2_2cpbar_split_reference"]["primary_ratio_to_baseline"],
            "yasui_vs_cp2_split_primary_ratio_error": complex_json(primary_split_ratio_error),
            "yasui_vs_cp2_split_primary_ratio_abs_error": repr(float(abs(primary_split_ratio_error))),
            "primary_abs_difference_from_untwisted": primary["primary_abs_difference_from_untwisted"],
        },
        "direct_cat_1_3_2_observation": {
            "anyonwiki_category_parameter": cat2["category"]["anyonwiki_category_parameter"],
            "braiding_convention": cat2["category"]["braiding_convention"],
            "controls_status": cat2_controls["status"],
            "yasui_untwisted_raw": cat2["aggregate_untwisted"]["raw"],
            "yasui_primary_component_a_twist_raw": cat2["aggregate_primary_component_a_twist"]["raw"],
            "yasui_primary_ratio_to_untwisted": cat2["primary_ratio_to_untwisted"],
            "ratio_difference_from_primary_working_convention": complex_json(primary_cat2_ratio_difference),
            "ratio_abs_difference_from_primary_working_convention": repr(float(abs(primary_cat2_ratio_difference))),
            "interpretation": (
                "The direct cat_1_3_2 labeled table passes local modular/Hopf controls but "
                "does not match the full Yasui braid aggregate under this naive label choice. "
                "Do not use it as an invariant cross-check until the scalar gauge and any "
                "needed fusion-ring automorphism from the admitted gauge-equivalence artifact "
                "are explicitly applied to this evaluator convention."
            ),
        },
        "verdict": {
            "selected_for_current_yasui_run": "cat_1_3_1 with anyonwiki_direct evaluator convention",
            "primary_component_a_twist_signal": "nonbaseline",
            "primary_component_a_ratio": primary["primary_ratio_to_untwisted"],
            "remote_server_needed": False,
            "reason_remote_server_not_needed": "rank 6 and multiplicity-free; full 216-sector aggregate completed locally in under one second on this run",
        },
        "claim_boundary": (
            "Comparison and convention-warning artifact for the numeric SU(3)_2 "
            "AnyonWiki Yasui a=1 aggregate. This records a working convention and "
            "a direct-labeled cat_1_3_2 caution; it is not a theorem-level "
            "gauge-invariant proof."
        ),
    }
    write_json(OUTPUT, payload)
    print(
        json.dumps(
            {
                "artifact": rel(OUTPUT),
                "status": payload["status"],
                "primary_ratio": payload["primary_working_convention"]["yasui_primary_ratio_to_untwisted"]["display"],
                "primary_vs_split_abs_error": payload["primary_working_convention"]["yasui_vs_cp2_split_primary_ratio_abs_error"],
                "cat2_ratio_abs_difference": payload["direct_cat_1_3_2_observation"]["ratio_abs_difference_from_primary_working_convention"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
