"""Aggregate Yasui a=1 c3w1 D(A4), component-A twisted singleton chunks."""

from __future__ import annotations

from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


REPO_ROOT = Path(__file__).resolve().parents[2]
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "yasui"
CHUNK_DIR = (
    RESULT_DIR
    / "figure3-a1-r1-normalized-da4-c3w1-twisted-component-a-singleton-chunks-v1"
)
MANIFEST_PATH = (
    RESULT_DIR
    / "figure3-a1-r1-normalized-da4-c3w1-twisted-component-a-singleton-manifest-v1.json"
)
OUTPUT = (
    RESULT_DIR
    / "figure3-a1-r1-normalized-da4-c3w1-twisted-component-a-singleton-aggregate-v1.json"
)
EXPECTED_SECTOR_TOTAL = 2744


def command(argv: list[str]) -> str | None:
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text())


def complex_from_json(value: dict) -> complex:
    return complex(float(value["real"]), float(value["imag"]))


def complex_json(value: complex) -> dict[str, str]:
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def chunk_path(index: int) -> Path:
    return CHUNK_DIR / f"chunk-{index:07d}-{index + 1:07d}.json"


def repo_metadata() -> dict:
    status_short = command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(status_short),
        "status_short": status_short,
    }


def main() -> int:
    utc_start = datetime.now(UTC).isoformat()
    started = time.monotonic()
    manifest = read_json(MANIFEST_PATH)
    labels = manifest["simple_labels"]
    global_dimension = sum(
        float(item["quantum_dimension"]) ** 2
        for item in read_json(
            REPO_ROOT
            / "experiments"
            / "results"
            / "mtc-candidates"
            / "drinfeld-double-a4-c3w1-mtc-fr-data-v1.json"
        )["simple_objects"]
    )

    rows = []
    errors = []
    total = 0.0 + 0.0j
    present_indices = []
    for index in range(EXPECTED_SECTOR_TOTAL):
        path = chunk_path(index)
        if not path.exists():
            errors.append({"sector_index": index, "error": "missing-chunk", "path": rel(path)})
            continue
        payload = read_json(path)
        present_indices.append(index)
        if payload.get("sector_index") != index:
            errors.append(
                {
                    "sector_index": index,
                    "error": "sector-index-mismatch",
                    "recorded": payload.get("sector_index"),
                    "path": rel(path),
                }
            )
        if payload.get("mtc_id") != manifest.get("mtc_id"):
            errors.append({"sector_index": index, "error": "mtc-id-mismatch", "path": rel(path)})
        if payload.get("link_twist") != manifest.get("link_twist"):
            errors.append({"sector_index": index, "error": "link-twist-mismatch", "path": rel(path)})
        if "weighted_twisted_contribution" not in payload:
            errors.append(
                {
                    "sector_index": index,
                    "error": "missing-weighted-twisted-contribution",
                    "path": rel(path),
                }
            )
            continue
        contribution = complex_from_json(payload["weighted_twisted_contribution"])
        total += contribution
        rows.append(
            {
                "sector_index": index,
                "fixed_component_labels": payload.get("fixed_component_labels"),
                "weighted_twisted_contribution": payload["weighted_twisted_contribution"],
                "elapsed_seconds": payload.get("elapsed_seconds"),
                "hostname": (payload.get("environment") or {}).get("hostname"),
                "worker_id": (payload.get("run_context") or {}).get("worker_id"),
            }
        )

    status = "pass" if not errors and len(present_indices) == EXPECTED_SECTOR_TOTAL else "incomplete"
    payload = {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-da4-c3w1-twisted-component-a-singleton-aggregate.v1",
        "status": status,
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": (
            "python experiments/sage/"
            "yasui_figure3_a1_r1_normalized_da4_c3w1_twisted_a_aggregate.py"
        ),
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "repo": repo_metadata(),
        "source": {
            "chunk_dir": rel(CHUNK_DIR),
            "manifest": rel(MANIFEST_PATH),
            "manifest_sha256": file_sha256(MANIFEST_PATH),
        },
        "case": {
            "mtc_id": manifest.get("mtc_id"),
            "category_id": manifest.get("category_id"),
            "category_twist": manifest.get("category_twist"),
            "link_id": manifest.get("link_id"),
            "yetter_twist": manifest.get("yetter_twist"),
            "link_twist": manifest.get("link_twist"),
            "component_order_in_braid": manifest.get("source", {}).get("component_order_in_braid"),
        },
        "sector_total_expected": EXPECTED_SECTOR_TOTAL,
        "sector_total_present": len(present_indices),
        "simple_label_count": len(labels),
        "global_dimension": repr(float(global_dimension)),
        "aggregate_weighted_twisted_contribution": complex_json(total),
        "normalized_by_global_dimension": complex_json(total / global_dimension),
        "errors": errors[:100],
        "error_count": len(errors),
        "rows": rows,
        "claim_boundary": (
            "Numeric aggregate of singleton chunks only. No equality target is asserted here."
        ),
    }
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": status,
                "artifact": rel(OUTPUT),
                "sector_total_present": len(present_indices),
                "error_count": len(errors),
                "aggregate": payload["aggregate_weighted_twisted_contribution"]["display"],
                "normalized": payload["normalized_by_global_dimension"]["display"],
            },
            sort_keys=True,
        )
    )
    return 0 if status == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
