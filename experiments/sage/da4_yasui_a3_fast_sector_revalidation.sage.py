"""Revalidate fast Yasui a=3 D(A4) singleton sectors with the same evaluator.

This script recomputes selected already-completed singleton chunks with
``DA4FRBraidEvaluator.fixed_label_value`` and compares against the recorded
JSON values.  It writes only a validation artifact; it does not overwrite chunk
outputs.
"""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

import numpy as np
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
EVALUATOR_PATH = REPO_ROOT / "experiments" / "sage" / "yasui_figure3_a3_da4_untwisted_chunked.sage.py"
MTC_PATH = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "drinfeld-double-a4-omega0-mtc-fr-data-v1.json"
)
CHUNK_DIR = REPO_ROOT / "experiments" / "results" / "yasui" / "figure3-a3-da4-omega0-untwisted-chunks-v1"
OUTPUT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure3-a3-da4-omega0-untwisted-fast-sector-revalidation-v1.json"
TOLERANCE = 1e-7


def load_evaluator_module():
    spec = importlib.util.spec_from_file_location("da4_yasui_a3_evaluator_for_revalidation", EVALUATOR_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def command(argv: list[str]) -> str:
    return subprocess.check_output(argv, cwd=REPO_ROOT, text=True).strip()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def cplx(payload: dict) -> complex:
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


def chunk_path(index: int, chunk_dir: Path = CHUNK_DIR) -> Path:
    return chunk_dir / f"chunk-{index:07d}-{index + 1:07d}.json"


def selected_indices(chunk_dir: Path, limit: int = 24) -> list[int]:
    candidates = []
    for path in chunk_dir.glob("chunk-*.json"):
        data = json.loads(path.read_text())
        elapsed = float(data.get("elapsed_seconds", 999999))
        if elapsed <= 1.0:
            candidates.append((int(data["sector_index"]), elapsed))
    candidates.sort(key=lambda item: (item[1], item[0]))
    return [index for index, _elapsed in candidates[:limit]]


def parse_args(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--indices", help="Comma-separated sector indices to recompute.")
    parser.add_argument("--recorded-root", type=Path, default=CHUNK_DIR)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--limit", type=int, default=24)
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    recorded_root = args.recorded_root.resolve()
    output = args.output.resolve()
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    module = load_evaluator_module()
    mtc = json.loads(MTC_PATH.read_text())
    evaluator = module.DA4FRBraidEvaluator(mtc)
    braid = module.build_braid_payload()
    rows = []
    if args.indices:
        indices = [int(item) for item in args.indices.split(",") if item.strip()]
    else:
        indices = selected_indices(recorded_root, args.limit)
    for index in indices:
        recorded_path = chunk_path(index, recorded_root)
        recorded = json.loads(recorded_path.read_text())
        fixed_labels = tuple(recorded["fixed_component_labels"])
        recomputed = module.compute_sector_payload(
            evaluator,
            braid,
            mtc,
            index,
            fixed_labels,
            {
                "mode": "fast-sector-revalidation",
                "recorded_root": rel(recorded_root),
                "repo": module.repo_metadata(),
                "tool_versions": module.tool_versions(),
            },
        )
        recorded_value = cplx(recorded["weighted_untwisted_contribution"])
        recomputed_value = cplx(recomputed["weighted_untwisted_contribution"])
        difference = recomputed_value - recorded_value
        rows.append(
            {
                "sector_index": index,
                "fixed_component_labels": list(fixed_labels),
                "recorded_artifact": rel(recorded_path),
                "recorded_elapsed_seconds": recorded["elapsed_seconds"],
                "recomputed_elapsed_seconds": recomputed["elapsed_seconds"],
                "recorded_weighted_untwisted_contribution": recorded["weighted_untwisted_contribution"],
                "recomputed_weighted_untwisted_contribution": recomputed["weighted_untwisted_contribution"],
                "difference": complex_json(difference),
                "abs_difference": repr(float(abs(difference))),
                "pass": bool(abs(difference) <= TOLERANCE),
            }
        )
    failures = [row for row in rows if not row["pass"]]
    payload = {
        "schema": "twisted-yetter.yasui-figure3-a3-da4-fast-sector-revalidation.v1",
        "status": "pass" if not failures else "fail",
        "generator_script": "experiments/sage/da4_yasui_a3_fast_sector_revalidation.sage.py",
        "argv": sys.argv[1:],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/da4_yasui_a3_fast_sector_revalidation.sage.py '
            + " ".join(sys.argv[1:])
        ),
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "tolerance": TOLERANCE,
        "claim_boundary": "Local revalidation of fast already-completed sectors using the same D(A4) FR evaluator; not a Linux/Mac cross-check.",
        "source": {
            "mtc_artifact": rel(MTC_PATH),
            "mtc_sha256": file_sha256(MTC_PATH),
            "chunk_dir": rel(recorded_root),
            "evaluator_script": rel(EVALUATOR_PATH),
            "evaluator_method": "DA4FRBraidEvaluator.fixed_label_value",
        },
        "tool_versions": {
            "sage": SAGE_VERSION,
            "python": sys.version,
            "numpy": np.__version__,
        },
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "dirty": bool(command(["git", "status", "--short"])),
            "status_short": command(["git", "status", "--short"]),
        },
        "summary": {
            "row_count": len(rows),
            "failure_count": len(failures),
            "max_abs_difference": repr(float(max((float(row["abs_difference"]) for row in rows), default=0.0))),
        },
        "failures": failures,
        "rows": rows,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": payload["status"], "artifact": rel(output), "failure_count": len(failures), "row_count": len(rows), "max_abs_difference": payload["summary"]["max_abs_difference"]}, sort_keys=True))
    return 0 if payload["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
