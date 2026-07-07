#!/usr/bin/env python3
from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "mtc-candidates"
DEFAULT_INPUT = RESULT_DIR / "drinfeld-double-dic12-omega0-mtc-fr-data-v1.json"
DEFAULT_OUTPUT = RESULT_DIR / "drinfeld-double-dic12-omega0-verification-run-v1.json"
BUILDER_PATH = REPO_ROOT / "experiments" / "scripts" / "build_drinfeld_double_dic12_mtc_data.py"
SCHEMA_FR = "twisted-yetter.mtc.fr-data.drinfeld-double-dic12.v1"
SCHEMA_VERIFICATION = "twisted-yetter.drinfeld-double-dic12.verification-run.v1"
FR_TOLERANCE = 1e-10
COHERENCE_TOLERANCE = 1e-7


class Verifier:
    def __init__(self) -> None:
        self.checks: dict[str, bool] = {}
        self.failures: list[str] = []

    def check(self, name: str, condition: bool, message: str) -> None:
        self.checks[name] = bool(condition)
        if not condition:
            self.failures.append(message)


def main() -> int:
    args = parse_args()
    started = time.monotonic()
    started_utc = datetime.now(UTC).isoformat()
    verifier = Verifier()
    input_path = args.input.resolve()
    payload = load_json(input_path)

    verify_payload_shape(verifier, input_path, payload)
    labels = payload["simple_labels"]
    fusion = fusion_dict(payload["fusion_rules"], labels)
    verify_group_and_simples(verifier, payload, labels)
    verify_identity_certificate(verifier, payload)
    verify_fusion(verifier, labels, fusion)
    verify_fr_blocks(verifier, payload, labels, fusion)
    verify_supplementary_equations(verifier, payload, labels, fusion)
    recomputed_coherence = recompute_coherence(payload)
    verify_coherence(verifier, payload, recomputed_coherence)

    status = "pass" if not verifier.failures else "fail"
    output = args.output.resolve()
    result = {
        "schema": SCHEMA_VERIFICATION,
        "status": status,
        "generator_script": "experiments/scripts/verify_drinfeld_double_dic12_mtc_data.py",
        "argv": normalized_argv(args),
        "reproduce_command": reproduce_command(args),
        "utc_start": started_utc,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "repo": repo_payload(),
        "tool_versions": {"python": sys.version},
        "tolerances": {"fr_reconstruction": FR_TOLERANCE, "coherence": COHERENCE_TOLERANCE},
        "input_artifact": {
            "path": rel(input_path),
            "sha256": file_sha256(input_path),
            "schema": payload.get("schema"),
            "status": payload.get("status"),
            "mtc_id": payload.get("mtc_id"),
        },
        "checks": verifier.checks,
        "failures": verifier.failures,
        "summary": {
            "simple_count": len(labels),
            "global_dimension_squared": payload.get("global_dimension_squared"),
            "nonzero_f_blocks": len(payload["fr_symbols"]["f_blocks"]),
            "nonzero_r_blocks": len(payload["fr_symbols"]["r_blocks"]),
            "t_spectrum": twist_spectrum(payload["simple_objects"]),
            "identity_certificate": payload.get("identity_certificate"),
            "max_errors": payload.get("max_errors"),
            "coherence_max_errors": {
                name: scan["max_error"]
                for name, scan in recomputed_coherence["scans"].items()
            },
            "coherence_active_tuple_counts": {
                name: scan["active_tuple_count"]
                for name, scan in recomputed_coherence["scans"].items()
            },
            "checks_imported_from_final_fr_artifact": payload.get("checks_imported_from_final_fr_artifact"),
            "supplementary_equation_checks": payload.get("supplementary_equation_checks"),
        },
        "recomputed_coherence_certificate": recomputed_coherence,
    }
    write_json(output, result)
    print(json.dumps({"status": status, "output": rel(output), "failure_count": len(verifier.failures)}, sort_keys=True))
    return 0 if status == "pass" else 1


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Verify working numeric F/R symbols for untwisted D(Dic_12).")
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def verify_payload_shape(verifier: Verifier, input_path: Path, payload: dict[str, Any]) -> None:
    verifier.check("schema", payload.get("schema") == SCHEMA_FR, "FR artifact has the wrong schema")
    verifier.check("status_working_numeric", payload.get("status") == "WORKING_NUMERIC", "FR artifact status is not WORKING_NUMERIC")
    verifier.check("mtc_id", payload.get("mtc_id") == "omega0_untwisted_D_Dic12", "unexpected mtc_id")
    verifier.check("path_hygiene", not has_forbidden_absolute_path(payload), "artifact contains forbidden absolute scratch/home paths")
    verifier.check("input_under_repo", str(input_path).startswith(str(REPO_ROOT)), "input is not under the repo root")
    for key in [
        "generator_script",
        "argv",
        "reproduce_command",
        "utc_start",
        "utc_finish",
        "elapsed_seconds",
        "repo",
        "tool_versions",
    ]:
        verifier.check(f"metadata.{key}", key in payload, f"missing metadata key {key}")


def verify_group_and_simples(verifier: Verifier, payload: dict[str, Any], labels: list[str]) -> None:
    verifier.check("simple_count_32", len(labels) == 32 and len(set(labels)) == 32, "simple label count is not 32 unique labels")
    verifier.check(
        "simple_objects_match_labels",
        [item["label"] for item in payload["simple_objects"]] == labels,
        "simple object order does not match simple_labels",
    )
    verifier.check(
        "global_dimension_squared_144",
        sum(item["quantum_dimension"] ** 2 for item in payload["simple_objects"]) == 144,
        "global dimension squared is not 144",
    )
    verifier.check("group_order_12", payload["mathematical_object"]["group"]["order"] == 12, "group order is not 12")
    verifier.check(
        "presentation_convention",
        "a^6=1" in payload["mathematical_object"]["group"]["presentation"]
        and "x^2=a^3" in payload["mathematical_object"]["group"]["presentation"],
        "group presentation is not the expected Dic_12 convention",
    )
    verifier.check("twists_nonzero", all(item["twist"]["root_order"] > 0 for item in payload["simple_objects"]), "invalid twist root order")
    expected_t_spectrum = {
        "1:0": 14,
        "2:1": 6,
        "3:1": 3,
        "3:2": 3,
        "4:1": 2,
        "4:3": 2,
        "6:1": 1,
        "6:5": 1,
    }
    verifier.check("t_spectrum", twist_spectrum(payload["simple_objects"]) == expected_t_spectrum, "T-spectrum mismatch")


def verify_identity_certificate(verifier: Verifier, payload: dict[str, Any]) -> None:
    certificate = payload.get("identity_certificate", {})
    group_signature = certificate.get("group_signature", {})
    simple_signature = certificate.get("double_simple_object_signature", {})
    twist_signature = certificate.get("twist_signature", {})
    verifier.check(
        "identity.claimed_category",
        certificate.get("claimed_category") == "Rep(D(Dic_12)) = Z(Vec_Dic12)",
        "identity certificate has wrong claimed category",
    )
    verifier.check(
        "identity.group_signature",
        group_signature.get("order") == 12
        and group_signature.get("conjugacy_class_sizes") == [1, 2, 2, 1, 3, 3]
        and group_signature.get("centralizer_orders") == [12, 6, 6, 12, 4, 4]
        and group_signature.get("centralizer_types") == {
            "1A": "Dic_12",
            "aA": "C6",
            "a2A": "C6",
            "a3A": "Dic_12",
            "xA": "C4",
            "axA": "C4",
        },
        "identity group signature does not match Dic_12",
    )
    verifier.check(
        "identity.simple_signature",
        simple_signature.get("simple_count") == 32
        and simple_signature.get("quantum_dimension_distribution") == {"1": 8, "2": 16, "3": 8}
        and simple_signature.get("global_dimension_squared") == 144
        and simple_signature.get("expected_global_dimension_squared") == 144,
        "identity simple-object signature does not match D(Dic_12)",
    )
    verifier.check(
        "identity.twist_signature",
        twist_signature.get("t_spectrum") == twist_spectrum(payload["simple_objects"]),
        "identity twist signature does not match simple objects",
    )
    verifier.check(
        "identity.modular_cross_checks_present",
        certificate.get("modular_identity_cross_checks", {}).get("s_from_r_and_s_from_twist_fusion_are_checked_against_object_s") is True
        and certificate.get("modular_identity_cross_checks", {}).get("balancing_ribbon_scalars_checked") is True,
        "identity modular cross-check flags are missing",
    )


def verify_fusion(verifier: Verifier, labels: list[str], fusion: dict[tuple[str, str, str], int]) -> None:
    complete = all((a, b, c) in fusion for a in labels for b in labels for c in labels)
    nonnegative = all(value >= 0 for value in fusion.values())
    integral = all(isinstance(value, int) for value in fusion.values())
    unit = all(
        fusion[(labels[0], label, target)] == (1 if label == target else 0)
        and fusion[(label, labels[0], target)] == (1 if label == target else 0)
        for label in labels
        for target in labels
    )
    values = list(fusion.values())
    verifier.check("fusion_complete_grid", complete, "fusion grid is incomplete")
    verifier.check("fusion_nonnegative", nonnegative, "fusion has negative multiplicities")
    verifier.check("fusion_integral", integral, "fusion has non-integral multiplicities")
    verifier.check("fusion_unit", unit, "fusion unit check failed")
    verifier.check("max_fusion_multiplicity_1", max(values) == 1, "max fusion multiplicity is not 1")
    verifier.check("nonzero_fusion_triples_1856", sum(1 for value in values if value) == 1856, "unexpected nonzero fusion triple count")
    max_f_dim = 0
    distribution: Counter[int] = Counter()
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    dim = sum(fusion[(a, b, x)] * fusion[(x, c, d)] for x in labels)
                    if dim:
                        distribution[dim] += 1
                        max_f_dim = max(max_f_dim, dim)
    verifier.check("max_three_object_fusion_space_5", max_f_dim == 5, "max three-object fusion/F-space dimension is not 5")
    verifier.check(
        "f_space_dimension_distribution",
        dict(sorted(distribution.items())) == {1: 57856, 2: 26880, 3: 256, 4: 512, 5: 512},
        "unexpected F-space dimension distribution",
    )


def verify_fr_blocks(
    verifier: Verifier,
    payload: dict[str, Any],
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
) -> None:
    f_blocks = payload["fr_symbols"]["f_blocks"]
    r_blocks = payload["fr_symbols"]["r_blocks"]
    expected_r = {(a, b, c) for a in labels for b in labels for c in labels if fusion[(a, b, c)]}
    seen_r = set()
    r_ok = True
    for block in r_blocks:
        key = (block["a"], block["b"], block["c"])
        matrix = block["ba_to_ab"]
        expected_dim = fusion[key]
        seen_r.add(key)
        r_ok = r_ok and expected_dim > 0 and matrix["rows"] == expected_dim and matrix["columns"] == expected_dim
        r_ok = r_ok and float(block["max_reconstruction_error"]) <= FR_TOLERANCE
        r_ok = r_ok and entries_in_bounds(matrix)
    verifier.check("r_blocks_match_fusion", r_ok and seen_r == expected_r, "R blocks do not match nonzero fusion channels")

    expected_f = set()
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    left_dim = sum(fusion[(a, b, x)] * fusion[(x, c, d)] for x in labels)
                    right_dim = sum(fusion[(b, c, y)] * fusion[(a, y, d)] for y in labels)
                    if left_dim or right_dim:
                        expected_f.add((a, b, c, d, left_dim, right_dim))
    seen_f = set()
    f_ok = True
    for block in f_blocks:
        key = (block["a"], block["b"], block["c"], block["d"])
        left_dim = len(block["left_basis_labels"])
        right_dim = len(block["right_basis_labels"])
        matrix = block["right_to_left"]
        seen_f.add((*key, left_dim, right_dim))
        f_ok = f_ok and left_dim == right_dim and matrix["rows"] == left_dim and matrix["columns"] == right_dim
        f_ok = f_ok and float(block["max_reconstruction_error"]) <= FR_TOLERANCE
        f_ok = f_ok and entries_in_bounds(matrix)
    verifier.check("f_blocks_match_fusion_tree_bases", f_ok and seen_f == expected_f, "F blocks do not match nonzero fusion-tree bases")
    verifier.check("fr_reconstruction_errors", payload["max_errors"]["f_reconstruction"] <= FR_TOLERANCE and payload["max_errors"]["r_reconstruction"] <= FR_TOLERANCE, "FR reconstruction errors exceed tolerance")
    verifier.check(
        "imported_fr_checks_all_true",
        all(payload.get("checks_imported_from_final_fr_artifact", {}).values()),
        "imported/supplementary FR checks are not all true",
    )
    verifier.check("max_f_block_size_5", payload["counts"].get("max_f_block_size") == 5, "max F block size is not 5")
    verifier.check("max_r_block_size_1", payload["counts"].get("max_r_block_size") == 1, "max R block size is not 1")


def verify_supplementary_equations(
    verifier: Verifier,
    payload: dict[str, Any],
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
) -> None:
    builder = load_builder_module()
    group = builder.Dic12Group()
    simples = builder.build_simple_objects(group)
    modules = {simple.label: builder.build_module(group, simple) for simple in simples}
    homs = builder.build_all_hom_spaces(group, simples, modules)
    hom_dims_match = all(len(homs[(a, b, c)]) == fusion[(a, b, c)] for a in labels for b in labels for c in labels)
    verifier.check("pair_hom_dimensions_match_fusion", hom_dims_match, "computed Hom dimensions do not match serialized fusion")

    equations = builder.modular_equation_checks(group, simples, fusion, payload["fr_symbols"]["r_blocks"])
    recorded = payload["supplementary_equation_checks"]
    for name in ["balancing_ribbon_scalars", "s_from_r_matches_object_s", "s_from_twist_fusion_matches_object_s"]:
        verifier.check(
            f"{name}.max_error",
            equations[name]["max_error"] <= FR_TOLERANCE,
            f"{name} exceeds tolerance",
        )
        verifier.check(
            f"{name}.recorded_matches_recomputed",
            abs(recorded[name]["max_error"] - equations[name]["max_error"]) <= 1e-15,
            f"{name} recorded max error differs from recomputation",
        )
    verifier.check(
        "s_matrix_unit_row",
        equations["s_matrix_unit_row"]["max_error"] <= FR_TOLERANCE,
        "S-matrix unit row does not match dimensions",
    )


def recompute_coherence(payload: dict[str, Any]) -> dict[str, Any]:
    builder = load_builder_module()
    labels = payload["simple_labels"]
    fusion = builder.fusion_lookup(payload["fusion_rules"])
    pair_outputs = builder.pair_output_lookup(labels, fusion)
    f_data = builder.FData.from_blocks(payload["fr_symbols"]["f_blocks"])
    r_data = builder.RData.from_blocks(payload["fr_symbols"]["r_blocks"])
    scans = {
        "pentagon": builder.scan_pentagon(labels, fusion, pair_outputs, f_data),
        "right_hexagon": builder.scan_right_hexagon(labels, fusion, pair_outputs, f_data, r_data),
        "left_hexagon": builder.scan_left_hexagon(labels, fusion, pair_outputs, f_data, r_data),
    }
    return {
        "kind": "independently re-read serialized F/R all-active-label coherence scan",
        "status": "pass" if all(scan["max_error"] <= COHERENCE_TOLERANCE for scan in scans.values()) else "fail",
        "tolerance": COHERENCE_TOLERANCE,
        "label_tuple_counts": {
            "pentagon_all_label_tuples": len(labels) ** 5,
            "right_hexagon_all_label_tuples": len(labels) ** 4,
            "left_hexagon_all_label_tuples": len(labels) ** 4,
        },
        "scans": scans,
    }


def verify_coherence(verifier: Verifier, payload: dict[str, Any], recomputed: dict[str, Any]) -> None:
    recorded = payload["coherence_certificate"]
    verifier.check("recorded_coherence_status", recorded.get("status") == "pass", "recorded coherence certificate did not pass")
    verifier.check("recomputed_coherence_status", recomputed.get("status") == "pass", "recomputed coherence certificate did not pass")
    for name in ["pentagon", "right_hexagon", "left_hexagon"]:
        verifier.check(
            f"{name}.max_error",
            recomputed["scans"][name]["max_error"] <= COHERENCE_TOLERANCE,
            f"{name} max error exceeds tolerance",
        )
        verifier.check(
            f"{name}.recorded_matches_recomputed_count",
            recorded["scans"][name]["active_tuple_count"] == recomputed["scans"][name]["active_tuple_count"],
            f"{name} recorded active tuple count differs from recomputation",
        )
        verifier.check(
            f"{name}.recorded_matches_recomputed_error",
            abs(recorded["scans"][name]["max_error"] - recomputed["scans"][name]["max_error"]) <= 1e-15,
            f"{name} recorded max error differs from recomputation",
        )


def load_builder_module() -> Any:
    spec = importlib.util.spec_from_file_location("drinfeld_double_dic12_builder_for_verifier", BUILDER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {BUILDER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["drinfeld_double_dic12_builder_for_verifier"] = module
    spec.loader.exec_module(module)
    return module


def fusion_dict(rules: list[dict[str, Any]], labels: list[str]) -> dict[tuple[str, str, str], int]:
    fusion = {(a, b, c): 0 for a in labels for b in labels for c in labels}
    for rule in rules:
        for output in rule["outputs"]:
            fusion[(rule["left"], rule["right"], output["target"])] = int(output["multiplicity"])
    return fusion


def entries_in_bounds(matrix: dict[str, Any]) -> bool:
    rows = matrix["rows"]
    columns = matrix["columns"]
    return all(0 <= entry["row"] < rows and 0 <= entry["column"] < columns for entry in matrix["entries"])


def twist_spectrum(simple_objects: list[dict[str, Any]]) -> dict[str, int]:
    counter = Counter(f"{item['twist']['root_order']}:{item['twist']['exponent']}" for item in simple_objects)
    return dict(sorted(counter.items()))


def has_forbidden_absolute_path(value: Any) -> bool:
    if isinstance(value, str):
        if value.startswith("/tmp/") or value.startswith("/private/tmp/"):
            return True
        if value.startswith(str(Path.home())) and not value.startswith(str(REPO_ROOT)):
            return True
        return False
    if isinstance(value, list):
        return any(has_forbidden_absolute_path(item) for item in value)
    if isinstance(value, dict):
        return any(has_forbidden_absolute_path(item) for item in value.values())
    return False


def normalized_argv(args: argparse.Namespace) -> list[str]:
    argv = ["python", "experiments/scripts/verify_drinfeld_double_dic12_mtc_data.py"]
    if args.input != DEFAULT_INPUT:
        argv += ["--input", str(args.input)]
    if args.output != DEFAULT_OUTPUT:
        argv += ["--output", str(args.output)]
    return argv


def reproduce_command(args: argparse.Namespace) -> str:
    return " ".join(normalized_argv(args))


def repo_payload() -> dict[str, Any]:
    status = command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(status),
        "status_short": status,
    }


def command(argv: list[str]) -> str:
    return subprocess.check_output(argv, cwd=REPO_ROOT, text=True).strip()


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def load_json(path: Path) -> dict[str, Any]:
    with path.open() as handle:
        return json.load(handle)


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


if __name__ == "__main__":
    raise SystemExit(main())
