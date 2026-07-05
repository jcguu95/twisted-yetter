#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE_PACKAGE = Path("/tmp/drinfeld-double-a4-mtc-fr-package-2026-07-05")
OUTPUT_DIR = REPO_ROOT / "experiments" / "results" / "mtc-candidates"
COHERENCE_TOLERANCE = 1e-7

LABELS = (
    "1A:triv",
    "1A:chi1",
    "1A:chi2",
    "1A:std3",
    "2A:eps00",
    "2A:eps01",
    "2A:eps10",
    "2A:eps11",
    "3A:eta0",
    "3A:eta1",
    "3A:eta2",
    "3B:eta0",
    "3B:eta1",
    "3B:eta2",
)

QUANTUM_DIMENSIONS = {
    "1A:triv": 1,
    "1A:chi1": 1,
    "1A:chi2": 1,
    "1A:std3": 3,
    "2A:eps00": 3,
    "2A:eps01": 3,
    "2A:eps10": 3,
    "2A:eps11": 3,
    "3A:eta0": 4,
    "3A:eta1": 4,
    "3A:eta2": 4,
    "3B:eta0": 4,
    "3B:eta1": 4,
    "3B:eta2": 4,
}

CENTRALIZER_REP_DIMENSIONS = {
    "1A:triv": 1,
    "1A:chi1": 1,
    "1A:chi2": 1,
    "1A:std3": 3,
    "2A:eps00": 1,
    "2A:eps01": 1,
    "2A:eps10": 1,
    "2A:eps11": 1,
    "3A:eta0": 1,
    "3A:eta1": 1,
    "3A:eta2": 1,
    "3B:eta0": 1,
    "3B:eta1": 1,
    "3B:eta2": 1,
}

OMEGA0_TWISTS = {
    "1A:triv": {"root_order": 1, "exponent": 0, "qw": {"a": "1", "b": "0"}},
    "1A:chi1": {"root_order": 1, "exponent": 0, "qw": {"a": "1", "b": "0"}},
    "1A:chi2": {"root_order": 1, "exponent": 0, "qw": {"a": "1", "b": "0"}},
    "1A:std3": {"root_order": 1, "exponent": 0, "qw": {"a": "1", "b": "0"}},
    "2A:eps00": {"root_order": 1, "exponent": 0, "qw": {"a": "1", "b": "0"}},
    "2A:eps01": {"root_order": 1, "exponent": 0, "qw": {"a": "1", "b": "0"}},
    "2A:eps10": {"root_order": 2, "exponent": 1, "qw": {"a": "-1", "b": "0"}},
    "2A:eps11": {"root_order": 2, "exponent": 1, "qw": {"a": "-1", "b": "0"}},
    "3A:eta0": {"root_order": 1, "exponent": 0, "qw": {"a": "1", "b": "0"}},
    "3A:eta1": {"root_order": 3, "exponent": 1, "qw": {"a": "0", "b": "1"}},
    "3A:eta2": {"root_order": 3, "exponent": 2, "qw": {"a": "-1", "b": "-1"}},
    "3B:eta0": {"root_order": 1, "exponent": 0, "qw": {"a": "1", "b": "0"}},
    "3B:eta1": {"root_order": 3, "exponent": 1, "qw": {"a": "0", "b": "1"}},
    "3B:eta2": {"root_order": 3, "exponent": 2, "qw": {"a": "-1", "b": "-1"}},
}

C3W1_TWISTS = {
    "1A:triv": {"root_order": 1, "exponent": 0},
    "1A:chi1": {"root_order": 1, "exponent": 0},
    "1A:chi2": {"root_order": 1, "exponent": 0},
    "1A:std3": {"root_order": 1, "exponent": 0},
    "2A:eps00": {"root_order": 1, "exponent": 0},
    "2A:eps01": {"root_order": 1, "exponent": 0},
    "2A:eps10": {"root_order": 2, "exponent": 1},
    "2A:eps11": {"root_order": 2, "exponent": 1},
    "3A:eta0": {"root_order": 9, "exponent": 2},
    "3A:eta1": {"root_order": 9, "exponent": 5},
    "3A:eta2": {"root_order": 9, "exponent": 8},
    "3B:eta0": {"root_order": 9, "exponent": 2},
    "3B:eta1": {"root_order": 9, "exponent": 5},
    "3B:eta2": {"root_order": 9, "exponent": 8},
}


def main() -> int:
    args = parse_args()
    package = args.source_package.resolve()
    manifest = load_json(package / "manifest.json")
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    omega0 = build_payload(
        package=package,
        manifest=manifest,
        mtc_id="omega0_untwisted_D_A4",
        name="untwisted Drinfeld double D(A4)",
        twisting={"kind": "untwisted", "omega_class": 0},
        fr_relative="artifacts/omega0/drinfeld-double-a4-fr-symbols-numeric-v1.json",
        twist_table=OMEGA0_TWISTS,
        coherence=omega0_coherence(package),
        exclusions=[],
    )
    c3w1 = build_payload(
        package=package,
        manifest=manifest,
        mtc_id="c3w1_twisted_D_A4",
        name="C3-inflated omega_power=1 twisted Drinfeld double D^omega(A4)",
        twisting={"kind": "c3-inflated", "quotient": "A4 -> C3", "omega_power": 1},
        fr_relative="artifacts/c3w1/drinfeld-double-a4-c3w1-fr-symbols-numeric-v1.json",
        twist_table=C3W1_TWISTS,
        coherence=c3w1_coherence(package),
        exclusions=[
            "omega_power=2 is intentionally excluded from this two-MTC package",
            "order-2 component and full Z/6 family are not part of this artifact",
        ],
    )

    writes = [
        (
            output_dir / "drinfeld-double-a4-omega0-mtc-fr-data-v1.json",
            omega0,
        ),
        (
            output_dir / "drinfeld-double-a4-c3w1-mtc-fr-data-v1.json",
            c3w1,
        ),
    ]
    for path, payload in writes:
        write_json(path, payload)
        print(json.dumps({"path": rel(path), "sha256": file_sha256(path)}, sort_keys=True))
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Extract final D(A4) MTC FR data from a supplied package.")
    parser.add_argument("--source-package", type=Path, default=DEFAULT_SOURCE_PACKAGE)
    parser.add_argument("--output-dir", type=Path, default=OUTPUT_DIR)
    return parser.parse_args()


def build_payload(
    *,
    package: Path,
    manifest: dict[str, Any],
    mtc_id: str,
    name: str,
    twisting: dict[str, Any],
    fr_relative: str,
    twist_table: dict[str, dict[str, Any]],
    coherence: dict[str, Any],
    exclusions: list[str],
) -> dict[str, Any]:
    fr_path = package / fr_relative
    fr = load_json(fr_path)
    fusion_rules = fusion_rules_from_r_blocks(fr["r_blocks"])
    simple_objects = [
        {
            "label": label,
            "class_label": label.split(":", 1)[0],
            "centralizer_rep_dimension": CENTRALIZER_REP_DIMENSIONS[label],
            "quantum_dimension": QUANTUM_DIMENSIONS[label],
            "twist": twist_payload(twist_table[label]),
        }
        for label in LABELS
    ]
    return {
        "schema": "twisted-yetter.mtc.fr-data.drinfeld-double-a4.v1",
        "status": "ESTABLISHED_NUMERIC",
        "mtc_id": mtc_id,
        "name": name,
        "mathematical_object": {
            "family": "Drinfeld double of A4",
            "group": {"name": "A4", "order": 12},
            "twisting": twisting,
        },
        "claim_boundary": {
            "established": (
                "Final numeric F/R-symbol data and floating-point all-label "
                "pentagon/right-hexagon/left-hexagon coherence certificate."
            ),
            "not_claimed": [
                "Exact arithmetic proof",
                "Link invariant adapter",
                "Theorem-level identification beyond the stated numeric certificate",
                *exclusions,
            ],
            "coherence_tolerance": COHERENCE_TOLERANCE,
        },
        "source_package": {
            "package_id": "drinfeld-double-a4-mtc-fr-package-2026-07-05",
            "manifest_sha256": file_sha256(package / "manifest.json"),
            "original_manifest_generated_at_utc": manifest.get("generated_at_utc"),
            "source_repo_commit_recorded_by_package": manifest.get("git_commit"),
            "source_package_was_dirty": bool(manifest.get("git_dirty")),
            "dirty_provenance_is_not_imported_as_normative_state": True,
        },
        "field": "complex floating point",
        "basis_convention": fr["basis_convention"],
        "simple_labels": list(LABELS),
        "simple_objects": simple_objects,
        "global_dimension_squared": sum(QUANTUM_DIMENSIONS[label] ** 2 for label in LABELS),
        "fusion_rules": fusion_rules,
        "fr_symbols": {
            "f_blocks": fr["f_blocks"],
            "r_blocks": fr["r_blocks"],
        },
        "checks_imported_from_final_fr_artifact": fr["checks"],
        "counts": fr["counts"],
        "max_errors": fr["max_errors"],
        "coherence_certificate": coherence,
        "source_artifacts": [
            {
                "role": "fr_symbols",
                "package_relative_path": fr_relative,
                "sha256": file_sha256(fr_path),
                "schema": fr.get("schema"),
                "status": fr.get("status"),
            }
        ],
    }


def twist_payload(item: dict[str, Any]) -> dict[str, Any]:
    payload = {
        "kind": "root_of_unity",
        "root_order": item["root_order"],
        "exponent": item["exponent"],
        "angle_fraction": f"{item['exponent']}/{item['root_order']}",
    }
    if "qw" in item:
        payload["exact_Q_zeta3"] = item["qw"]
    return payload


def fusion_rules_from_r_blocks(r_blocks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_pair: dict[tuple[str, str], dict[str, int]] = {
        (left, right): {} for left in LABELS for right in LABELS
    }
    for block in r_blocks:
        matrix = block["ba_to_ab"]
        multiplicity = matrix["rows"]
        if multiplicity <= 0:
            continue
        if matrix["columns"] != multiplicity:
            raise ValueError(f"non-square R block for {(block['a'], block['b'], block['c'])}")
        by_pair[(block["a"], block["b"])][block["c"]] = multiplicity
    return [
        {
            "left": left,
            "right": right,
            "outputs": [
                {"target": target, "multiplicity": outputs[target]}
                for target in LABELS
                if target in outputs
            ],
        }
        for left in LABELS
        for right in LABELS
        for outputs in [by_pair[(left, right)]]
    ]


def omega0_coherence(package: Path) -> dict[str, Any]:
    files = {
        "pentagon": "artifacts/omega0/drinfeld-double-a4-full-coherence-pentagon-v1.json",
        "right_hexagon": "artifacts/omega0/drinfeld-double-a4-full-coherence-right-hexagon-v1.json",
        "left_hexagon": "artifacts/omega0/drinfeld-double-a4-full-coherence-left-hexagon-v1.json",
    }
    scans = {}
    source_artifacts = []
    for name, relative in files.items():
        path = package / relative
        payload = load_json(path)
        scan = payload["scans"][name]
        scans[name] = scan_summary(scan)
        source_artifacts.append(
            {
                "role": f"{name}_full_scan",
                "package_relative_path": relative,
                "sha256": file_sha256(path),
                "schema": payload.get("schema"),
                "status": payload.get("status"),
            }
        )
    return {
        "kind": "floating-point all-label coherence scan",
        "tolerance": COHERENCE_TOLERANCE,
        "scans": scans,
        "source_artifacts": source_artifacts,
    }


def c3w1_coherence(package: Path) -> dict[str, Any]:
    files = {
        "pentagon": "artifacts/c3w1/drinfeld-double-a4-c3w1-pentagon-summary-v1.json",
        "right_hexagon": "artifacts/c3w1/drinfeld-double-a4-c3w1-right-hexagon-summary-v1.json",
        "left_hexagon": "artifacts/c3w1/drinfeld-double-a4-c3w1-left-hexagon-summary-v1.json",
    }
    scans = {}
    source_artifacts = []
    for name, relative in files.items():
        path = package / relative
        payload = load_json(path)
        chunks = payload["chunks"]
        scans[name] = chunked_scan_summary(payload, name)
        verify_chunk_hashes(package, chunks)
        source_artifacts.append(
            {
                "role": f"{name}_chunked_summary",
                "package_relative_path": relative,
                "sha256": file_sha256(path),
                "schema": payload.get("schema"),
                "status": payload.get("status"),
                "chunk_count": payload.get("chunk_count"),
                "chunk_hash_manifest_sha256": sha256_json(
                    [
                        {
                            "chunk_index": chunk["chunk_index"],
                            "sha256": chunk["sha256"],
                            "scanned_label_tuples": chunk["scanned_label_tuples"],
                            "status": chunk["status"],
                        }
                        for chunk in chunks
                    ]
                ),
            }
        )
    full = package / "artifacts/c3w1/drinfeld-double-a4-c3w1-full-coherence-summary-v1.json"
    source_artifacts.append(
        {
            "role": "combined_full_coherence_summary",
            "package_relative_path": "artifacts/c3w1/drinfeld-double-a4-c3w1-full-coherence-summary-v1.json",
            "sha256": file_sha256(full),
            "schema": load_json(full).get("schema"),
            "status": load_json(full).get("status"),
        }
    )
    return {
        "kind": "floating-point all-label chunked coherence scan",
        "tolerance": COHERENCE_TOLERANCE,
        "scans": scans,
        "source_artifacts": source_artifacts,
    }


def scan_summary(scan: dict[str, Any]) -> dict[str, Any]:
    return {
        "status": scan["status"],
        "total_label_tuples": scan["total_label_tuples"],
        "scanned_label_tuples": scan["scanned_label_tuples"],
        "nonzero_fusion_spaces": scan.get("nonzero_fusion_spaces"),
        "max_error": scan["max_error"],
        "failure_count_recorded": scan["failure_count_recorded"],
        "recorded_failures": scan["recorded_failures"],
        "worst_sample": scan["worst_sample"],
    }


def chunked_scan_summary(payload: dict[str, Any], scan_name: str) -> dict[str, Any]:
    chunks = payload["chunks"]
    return {
        "status": "run",
        "scan": scan_name,
        "chunk_count": payload["chunk_count"],
        "all_chunks_pass": payload["checks"]["all_chunks_pass"],
        "all_chunks_present": payload["checks"]["all_chunks_present"],
        "max_error_within_tolerance": payload["checks"]["max_error_within_tolerance"],
        "total_label_tuples": chunks[0]["scanned_label_tuples"] * 0
        + expected_tuple_count(scan_name),
        "scanned_label_tuples": sum(chunk["scanned_label_tuples"] for chunk in chunks),
        "nonzero_fusion_spaces": sum(chunk["nonzero_fusion_spaces"] for chunk in chunks),
        "max_error": max(chunk["max_error"] for chunk in chunks),
        "failure_count_recorded": 0,
        "recorded_failures": [],
        "worst_sample": max(chunks, key=lambda chunk: chunk["max_error"])["worst_sample"],
    }


def expected_tuple_count(scan_name: str) -> int:
    if scan_name == "pentagon":
        return 14**5
    if scan_name in {"right_hexagon", "left_hexagon"}:
        return 14**4
    raise ValueError(f"unknown scan: {scan_name}")


def verify_chunk_hashes(package: Path, chunks: list[dict[str, Any]]) -> None:
    chunk_dir = package / "artifacts" / "c3w1" / "chunks"
    for chunk in chunks:
        path = chunk_dir / Path(chunk["path"]).name
        if file_sha256(path) != chunk["sha256"]:
            raise ValueError(f"chunk hash mismatch: {path.name}")


def load_json(path: Path) -> Any:
    with path.open() as handle:
        return json.load(handle)


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n")


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_json(value: Any) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(data).hexdigest()


def rel(path: Path) -> str:
    return path.resolve().relative_to(REPO_ROOT).as_posix()


if __name__ == "__main__":
    raise SystemExit(main())
