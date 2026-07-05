#!/usr/bin/env python3
from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "mtc-candidates"
DEFAULT_INPUTS = (
    RESULT_DIR / "drinfeld-double-a4-omega0-mtc-fr-data-v1.json",
    RESULT_DIR / "drinfeld-double-a4-c3w1-mtc-fr-data-v1.json",
)
DEFAULT_OUTPUT = RESULT_DIR / "drinfeld-double-a4-two-mtc-verification-run-v1.json"
COHERENCE_TOLERANCE = 1e-7
FR_TOLERANCE = 1e-10

EXPECTED_T_SPECTRA = {
    "omega0_untwisted_D_A4": {
        "1:0": 8,
        "2:1": 2,
        "3:1": 2,
        "3:2": 2,
    },
    "c3w1_twisted_D_A4": {
        "1:0": 6,
        "2:1": 2,
        "9:2": 2,
        "9:5": 2,
        "9:8": 2,
    },
}


class Verifier:
    def __init__(self) -> None:
        self.failures: list[str] = []
        self.checks: dict[str, bool] = {}

    def check(self, name: str, condition: bool, message: str) -> None:
        self.checks[name] = bool(condition)
        if not condition:
            self.failures.append(message)


def main() -> int:
    args = parse_args()
    started = time.monotonic()
    started_utc = datetime.now(UTC).isoformat()
    verifier = Verifier()

    inputs = [path.resolve() for path in args.inputs]
    data = [load_json(path) for path in inputs]
    summaries = [verify_mtc_payload(verifier, path, payload) for path, payload in zip(inputs, data)]
    verify_pair(verifier, data)

    source_package_summary = None
    if args.source_package is not None:
        source_package_summary = verify_source_package(
            verifier,
            args.source_package.resolve(),
            data,
        )

    finished_utc = datetime.now(UTC).isoformat()
    status = "pass" if not verifier.failures else "fail"
    output = args.output.resolve()
    payload = {
        "schema": "twisted-yetter.drinfeld-double-a4.two-mtc-verification-run.v1",
        "status": status,
        "generator_script": "experiments/scripts/verify_drinfeld_double_a4_mtc_data.py",
        "argv": normalized_argv(args),
        "reproduce_command": reproduce_command(args),
        "utc_start": started_utc,
        "utc_finish": finished_utc,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "dirty": bool(command(["git", "status", "--short"])),
            "status_short": command(["git", "status", "--short"]),
        },
        "tool_versions": {
            "python": sys.version,
        },
        "tolerances": {
            "fr_reconstruction": FR_TOLERANCE,
            "coherence": COHERENCE_TOLERANCE,
        },
        "input_artifacts": [
            {
                "path": rel(path),
                "sha256": file_sha256(path),
                "mtc_id": payload.get("mtc_id"),
                "schema": payload.get("schema"),
                "status": payload.get("status"),
            }
            for path, payload in zip(inputs, data)
        ],
        "checks": verifier.checks,
        "failures": verifier.failures,
        "mtc_summaries": summaries,
        "source_package_checks": source_package_summary,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    write_json(output, payload)
    print(json.dumps({"status": status, "output": rel(output), "failure_count": len(verifier.failures)}, sort_keys=True))
    return 0 if status == "pass" else 1


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Verify canonical D(A4) MTC FR data artifacts.")
    parser.add_argument("--inputs", nargs="*", type=Path, default=list(DEFAULT_INPUTS))
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--source-package", type=Path)
    return parser.parse_args()


def verify_mtc_payload(verifier: Verifier, path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    prefix = payload.get("mtc_id", path.name)
    verifier.check(
        f"{prefix}.schema",
        payload.get("schema") == "twisted-yetter.mtc.fr-data.drinfeld-double-a4.v1",
        f"{rel(path)} has wrong schema",
    )
    verifier.check(f"{prefix}.status", payload.get("status") == "ESTABLISHED_NUMERIC", f"{prefix} status is not ESTABLISHED_NUMERIC")
    verifier.check(f"{prefix}.no_absolute_tmp_or_user_paths", not has_forbidden_absolute_path(payload), f"{prefix} contains imported absolute scratch paths")
    labels = payload["simple_labels"]
    verifier.check(f"{prefix}.simple_count", len(labels) == 14 and len(set(labels)) == 14, f"{prefix} simple labels are not 14 unique labels")
    simple_objects = payload["simple_objects"]
    dims = {item["label"]: item["quantum_dimension"] for item in simple_objects}
    verifier.check(f"{prefix}.simple_objects_match_labels", [item["label"] for item in simple_objects] == labels, f"{prefix} simple object order differs from labels")
    verifier.check(f"{prefix}.global_dimension_squared", sum(value * value for value in dims.values()) == 144, f"{prefix} global dimension squared is not 144")
    verifier.check(f"{prefix}.twists_nonzero", all(item["twist"]["root_order"] > 0 for item in simple_objects), f"{prefix} has a zero/invalid twist")
    spectrum = twist_spectrum(simple_objects)
    expected_spectrum = EXPECTED_T_SPECTRA.get(prefix)
    verifier.check(f"{prefix}.t_spectrum", spectrum == expected_spectrum, f"{prefix} T-spectrum mismatch: {spectrum}")

    fusion = fusion_dict(payload["fusion_rules"], labels)
    verify_fusion_rules(verifier, prefix, labels, fusion)
    fr = payload["fr_symbols"]
    verify_r_blocks(verifier, prefix, labels, fusion, fr["r_blocks"])
    verify_f_blocks(verifier, prefix, labels, fusion, fr["f_blocks"])
    verify_fr_checks(verifier, prefix, payload)
    verify_coherence_certificate(verifier, prefix, payload["coherence_certificate"])

    return {
        "mtc_id": prefix,
        "simple_count": len(labels),
        "global_dimension_squared": payload.get("global_dimension_squared"),
        "nonzero_f_blocks": len(fr["f_blocks"]),
        "nonzero_r_blocks": len(fr["r_blocks"]),
        "t_spectrum": spectrum,
        "max_errors": payload.get("max_errors"),
        "coherence_max_errors": {
            name: scan["max_error"]
            for name, scan in payload["coherence_certificate"]["scans"].items()
        },
    }


def verify_pair(verifier: Verifier, data: list[dict[str, Any]]) -> None:
    ids = [payload.get("mtc_id") for payload in data]
    verifier.check("pair.expected_ids", set(ids) == set(EXPECTED_T_SPECTRA), f"unexpected MTC ids: {ids}")
    spectra = {payload["mtc_id"]: twist_spectrum(payload["simple_objects"]) for payload in data}
    if set(spectra) == set(EXPECTED_T_SPECTRA):
        omega = spectra["omega0_untwisted_D_A4"]
        c3w1 = spectra["c3w1_twisted_D_A4"]
        primitive_ninth = any(key.startswith("9:") for key in c3w1)
        verifier.check("pair.t_spectra_distinguish", omega != c3w1 and primitive_ninth, "T-spectra do not distinguish omega0 from c3w1")


def verify_fusion_rules(
    verifier: Verifier,
    prefix: str,
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
) -> None:
    complete_pairs = all((left, right, target) in fusion for left in labels for right in labels for target in labels)
    verifier.check(f"{prefix}.fusion_complete_grid", complete_pairs, f"{prefix} fusion rules are not a complete 14^3 grid")
    nonnegative = all(value >= 0 for value in fusion.values())
    integral = all(isinstance(value, int) for value in fusion.values())
    unit = all(
        fusion[(labels[0], label, target)] == (1 if label == target else 0)
        and fusion[(label, labels[0], target)] == (1 if label == target else 0)
        for label in labels
        for target in labels
    )
    verifier.check(f"{prefix}.fusion_nonnegative", nonnegative, f"{prefix} fusion has negative multiplicities")
    verifier.check(f"{prefix}.fusion_integral", integral, f"{prefix} fusion has non-integral multiplicities")
    verifier.check(f"{prefix}.fusion_unit", unit, f"{prefix} fusion unit check failed")


def verify_r_blocks(
    verifier: Verifier,
    prefix: str,
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
    blocks: list[dict[str, Any]],
) -> None:
    seen = {}
    ok = True
    for block in blocks:
        key = (block["a"], block["b"], block["c"])
        matrix = block["ba_to_ab"]
        expected = fusion[key]
        ok = ok and block["a"] in labels and block["b"] in labels and block["c"] in labels
        ok = ok and expected > 0
        ok = ok and matrix["rows"] == expected and matrix["columns"] == expected
        ok = ok and entries_in_bounds(matrix)
        ok = ok and float(block["max_reconstruction_error"]) <= FR_TOLERANCE
        seen[key] = True
    expected_nonzero = {
        (left, right, target)
        for left in labels
        for right in labels
        for target in labels
        if fusion[(left, right, target)] > 0
    }
    verifier.check(f"{prefix}.r_blocks_match_fusion", ok and set(seen) == expected_nonzero, f"{prefix} R blocks do not match nonzero fusion channels")


def verify_f_blocks(
    verifier: Verifier,
    prefix: str,
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
    blocks: list[dict[str, Any]],
) -> None:
    seen = {}
    ok = True
    for block in blocks:
        a, b, c, d = block["a"], block["b"], block["c"], block["d"]
        key = (a, b, c, d)
        expected_left = sum(fusion[(a, b, x)] * fusion[(x, c, d)] for x in labels)
        expected_right = sum(fusion[(b, c, y)] * fusion[(a, y, d)] for y in labels)
        matrix = block["right_to_left"]
        left_basis = block["left_basis_labels"]
        right_basis = block["right_basis_labels"]
        ok = ok and expected_left == expected_right and expected_left > 0
        ok = ok and len(left_basis) == expected_left and len(right_basis) == expected_right
        ok = ok and matrix["rows"] == len(left_basis) and matrix["columns"] == len(right_basis)
        ok = ok and entries_in_bounds(matrix)
        ok = ok and float(block["max_reconstruction_error"]) <= FR_TOLERANCE
        ok = ok and all(valid_left_f_basis(label, a, b, c, d, fusion) for label in left_basis)
        ok = ok and all(valid_right_f_basis(label, a, b, c, d, fusion) for label in right_basis)
        seen[key] = True
    expected_nonzero = {
        (a, b, c, d)
        for a in labels
        for b in labels
        for c in labels
        for d in labels
        if sum(fusion[(a, b, x)] * fusion[(x, c, d)] for x in labels) > 0
    }
    verifier.check(f"{prefix}.f_blocks_match_fusion_tree_bases", ok and set(seen) == expected_nonzero, f"{prefix} F blocks do not match nonzero fusion tree bases")


def verify_fr_checks(verifier: Verifier, prefix: str, payload: dict[str, Any]) -> None:
    checks = payload["checks_imported_from_final_fr_artifact"]
    verifier.check(f"{prefix}.imported_fr_checks_all_true", all(checks.values()), f"{prefix} imported FR checks are not all true")
    max_errors = payload["max_errors"]
    verifier.check(
        f"{prefix}.fr_reconstruction_errors_under_tolerance",
        max_errors["f_reconstruction"] <= FR_TOLERANCE and max_errors["r_reconstruction"] <= FR_TOLERANCE,
        f"{prefix} FR reconstruction error exceeds tolerance",
    )


def verify_coherence_certificate(verifier: Verifier, prefix: str, certificate: dict[str, Any]) -> None:
    expected_counts = {
        "pentagon": 14**5,
        "right_hexagon": 14**4,
        "left_hexagon": 14**4,
    }
    ok = certificate["tolerance"] == COHERENCE_TOLERANCE
    for name, expected_count in expected_counts.items():
        scan = certificate["scans"][name]
        ok = ok and scan["status"] == "run"
        ok = ok and scan["total_label_tuples"] == expected_count
        ok = ok and scan["scanned_label_tuples"] == expected_count
        ok = ok and scan["max_error"] <= COHERENCE_TOLERANCE
        ok = ok and scan["failure_count_recorded"] == 0
        ok = ok and scan["recorded_failures"] == []
        if "all_chunks_pass" in scan:
            ok = ok and scan["all_chunks_pass"] and scan["all_chunks_present"]
            ok = ok and scan["max_error_within_tolerance"]
    verifier.check(f"{prefix}.coherence_certificate_passes", ok, f"{prefix} coherence certificate failed")


def verify_source_package(
    verifier: Verifier,
    package: Path,
    data: list[dict[str, Any]],
) -> dict[str, Any]:
    manifest_path = package / "manifest.json"
    ok = manifest_path.exists()
    checked = 0
    if ok:
        manifest_sha = file_sha256(manifest_path)
        for payload in data:
            ok = ok and payload["source_package"]["manifest_sha256"] == manifest_sha
            artifact_records = list(payload["source_artifacts"])
            artifact_records.extend(payload["coherence_certificate"]["source_artifacts"])
            for record in artifact_records:
                path = package / record["package_relative_path"]
                ok = ok and path.exists() and file_sha256(path) == record["sha256"]
                checked += 1
    verifier.check("source_package.hashes_match_canonical_records", ok, "source package hashes do not match canonical records")
    return {
        "status": "pass" if ok else "fail",
        "package_id": "drinfeld-double-a4-mtc-fr-package-2026-07-05",
        "manifest_sha256": file_sha256(manifest_path) if manifest_path.exists() else None,
        "checked_artifact_count": checked,
    }


def fusion_dict(rules: list[dict[str, Any]], labels: list[str]) -> dict[tuple[str, str, str], int]:
    out = {
        (rule["left"], rule["right"], target): 0
        for rule in rules
        for target in labels
    }
    for rule in rules:
        for output in rule["outputs"]:
            out[(rule["left"], rule["right"], output["target"])] = output["multiplicity"]
    return out


def valid_left_f_basis(
    label: list[Any],
    a: str,
    b: str,
    c: str,
    d: str,
    fusion: dict[tuple[str, str, str], int],
) -> bool:
    x, i, j = label
    return 0 <= i < fusion[(a, b, x)] and 0 <= j < fusion[(x, c, d)]


def valid_right_f_basis(
    label: list[Any],
    a: str,
    b: str,
    c: str,
    d: str,
    fusion: dict[tuple[str, str, str], int],
) -> bool:
    y, i, j = label
    return 0 <= i < fusion[(b, c, y)] and 0 <= j < fusion[(a, y, d)]


def entries_in_bounds(matrix: dict[str, Any]) -> bool:
    rows = matrix["rows"]
    columns = matrix["columns"]
    for entry in matrix["entries"]:
        if not (0 <= entry["row"] < rows and 0 <= entry["column"] < columns):
            return False
        try:
            float(entry["value"]["real"])
            float(entry["value"]["imag"])
        except (KeyError, TypeError, ValueError):
            return False
    return True


def twist_spectrum(simple_objects: list[dict[str, Any]]) -> dict[str, int]:
    counts = Counter(
        f"{item['twist']['root_order']}:{item['twist']['exponent']}"
        for item in simple_objects
    )
    return dict(sorted(counts.items()))


def has_forbidden_absolute_path(value: Any) -> bool:
    for item in iter_strings(value):
        if item.startswith("/tmp/") or item.startswith("/Users/"):
            return True
    return False


def iter_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        out: list[str] = []
        for item in value:
            out.extend(iter_strings(item))
        return out
    if isinstance(value, dict):
        out = []
        for item in value.values():
            out.extend(iter_strings(item))
        return out
    return []


def normalized_argv(args: argparse.Namespace) -> list[str]:
    argv = ["experiments/scripts/verify_drinfeld_double_a4_mtc_data.py"]
    if args.inputs != list(DEFAULT_INPUTS):
        argv.append("--inputs")
        argv.extend(rel(path.resolve()) for path in args.inputs)
    if args.output != DEFAULT_OUTPUT:
        argv.extend(["--output", rel(args.output.resolve())])
    if args.source_package is not None:
        argv.extend(["--source-package", "<local-supplied-package>"])
    return argv


def reproduce_command(args: argparse.Namespace) -> str:
    command_line = "python experiments/scripts/verify_drinfeld_double_a4_mtc_data.py"
    if args.source_package is not None:
        command_line += " --source-package $DRINFELD_DOUBLE_A4_SOURCE_PACKAGE"
    return command_line


def load_json(path: Path) -> Any:
    with path.open() as handle:
        return json.load(handle)


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n")


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(command_args: list[str]) -> str:
    try:
        return subprocess.check_output(command_args, cwd=REPO_ROOT, text=True, stderr=subprocess.STDOUT).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        return f"unavailable: {exc}"


def rel(path: Path) -> str:
    return path.resolve().relative_to(REPO_ROOT).as_posix()


if __name__ == "__main__":
    raise SystemExit(main())
