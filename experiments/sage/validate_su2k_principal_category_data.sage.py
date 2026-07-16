#!/usr/bin/env sage
"""Strictly revalidate a principal SU(2)_k category-data export."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import stable_content_hash  # noqa: E402


GROWN_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate" / "grown-category-data"
CERT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate" / "grown-category-certificates"
EVALUATOR_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"

EXPORTS = {
    "rank3-ising": {
        "path": GROWN_DIR / "rank3-ising-principal-su2-level2-category-data-export-v1.json",
        "certificate_id": "rank3-ising-principal-su2-level2-strict-export-validation-v1",
    },
    "rank5-su2-4": {
        "path": GROWN_DIR / "rank5-su2-4-principal-su2-level4-category-data-export-v1.json",
        "certificate_id": "rank5-su2-4-principal-su2-level4-strict-export-validation-v1",
    },
}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def git_output(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def file_sha256_id(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def with_hash(payload):
    result = dict(payload)
    result.pop("content_hash", None)
    result["content_hash"] = stable_content_hash(result)
    return result


def load_evaluator_module():
    spec = importlib.util.spec_from_file_location("su2k_validation_source", EVALUATOR_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules["su2k_validation_source"] = module
    spec.loader.exec_module(module)
    return module


def assert_equal(actual, expected, label: str) -> None:
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected!r}, got {actual!r}")


def validate_export(family_id: str, *, started_at_utc: str):
    spec = EXPORTS[family_id]
    export = load_json(spec["path"])
    export_body = dict(export)
    export_hash = export_body.pop("content_hash")
    assert_equal(export_hash, stable_content_hash(export_body), "export content_hash")

    data = export["category_data"]
    category_hash = stable_content_hash(data)
    assert_equal(export["category_data_hash"], category_hash, "category_data_hash")
    assert_equal(data["source_machinery"]["sha256"], file_sha256_id(EVALUATOR_PATH), "source machinery hash")

    su2k = load_evaluator_module()
    evaluator = su2k.SU2KBraidEvaluator(data["level"], exact=True)
    labels = list(data["labels"])
    label_set = set(labels)

    checked = {
        "fusion_entries": 0,
        "f_symbol_entries": 0,
        "r_symbol_entries": 0,
        "twist_entries": 0,
        "dimension_entries": 0,
        "r_inverse_entries": 0,
    }
    for left in labels:
        for right in labels:
            key = f"{left}x{right}"
            expected = [
                output
                for output in evaluator.fusion_outputs(left, right)
                if output in label_set
            ]
            assert_equal(data["fusion"][key], expected, f"fusion {key}")
            checked["fusion_entries"] += 1

    for key, value in data["f_symbols"].items():
        inside = key.removeprefix("F(").removesuffix(")")
        abc, channels = inside.split(";")
        left_channel, right_channel = [int(item) for item in channels.split(",")]
        ab, d = abc.split("->")
        a, b, c = [int(item) for item in ab.split(",")]
        d = int(d)
        expected = str(evaluator.f_symbol(a, b, c, d, left_channel, right_channel))
        assert_equal(value, expected, f"F-symbol {key}")
        checked["f_symbol_entries"] += 1

    for key, value in data["r_symbols"].items():
        positive = key.startswith("R+")
        inside = key.removeprefix("R+(").removeprefix("R-(").removesuffix(")")
        lr, output = inside.split("->")
        left, right = [int(item) for item in lr.split(",")]
        output = int(output)
        expected_value = evaluator.r_symbol(left, right, output, positive=positive)
        assert_equal(value, str(expected_value), f"R-symbol {key}")
        checked["r_symbol_entries"] += 1
        inverse_key = f"R-({left},{right}->{output})" if positive else f"R+({left},{right}->{output})"
        product_value = expected_value * evaluator.r_symbol(left, right, output, positive=not positive)
        if str(product_value) != "1":
            raise AssertionError(f"R inverse product failed for {key} and {inverse_key}: {product_value}")
        checked["r_inverse_entries"] += 1

    for label in labels:
        assert_equal(data["twists"][str(label)], str(evaluator.twist(label)), f"twist {label}")
        assert_equal(data["dimensions"][str(label)], str(evaluator.dimension(label)), f"dimension {label}")
        checked["twist_entries"] += 1
        checked["dimension_entries"] += 1

    assert_equal(checked["fusion_entries"], export["entry_counts"]["fusion_products"], "fusion count")
    assert_equal(checked["f_symbol_entries"], export["entry_counts"]["f_symbols"], "F count")
    assert_equal(checked["r_symbol_entries"], export["entry_counts"]["r_symbols"], "R count")
    assert_equal(checked["twist_entries"], export["entry_counts"]["twists"], "twist count")
    assert_equal(checked["dimension_entries"], export["entry_counts"]["dimensions"], "dimension count")

    return with_hash(
        {
            "schema": "twisted-yetter.su2k-principal-export-validation-certificate.v1",
            "status": "PASS_STRICT_PRINCIPAL_EXPORT_REVALIDATION",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/sage/validate_su2k_principal_category_data.sage.py",
            "reproduce_command": (
                f'DOT_SAGE="$PWD/.sage" sage experiments/sage/validate_su2k_principal_category_data.sage.py '
                f"--family-id {family_id} --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {
                "python": platform.python_version(),
                "sage": getattr(su2k, "SAGE_VERSION", "unknown"),
            },
            "certificate_id": spec["certificate_id"],
            "family_id": family_id,
            "validated_export": {
                "path": str(spec["path"].relative_to(REPO_ROOT)),
                "sha256": file_sha256_id(spec["path"]),
                "content_hash": export["content_hash"],
                "category_data_hash": export["category_data_hash"],
                "status": export["status"],
            },
            "checks": {
                "export_content_hash_fresh": "PASS",
                "category_data_hash_fresh": "PASS",
                "source_machinery_hash_matches": "PASS",
                "fusion_entries_recomputed": "PASS",
                "f_symbol_entries_recomputed": "PASS",
                "r_symbol_entries_recomputed": "PASS",
                "twist_entries_recomputed": "PASS",
                "dimension_entries_recomputed": "PASS",
                "r_inverse_entries_recomputed": "PASS",
                "entry_counts_match": "PASS",
            },
            "checked_entry_counts": checked,
            "formal_row_resolution_allowed": False,
            "formal_ribbon_realization_snapshot_produced": False,
            "explicit_non_claims": [
                "This certificate validates a principal SU(2)_k export only.",
                "This certificate does not enumerate all Galois/mirror/pivotal/ribbon branches.",
                "This certificate is not a row-complete ribbon realization snapshot.",
            ],
        }
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family-id", choices=sorted(EXPORTS), required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    payload = validate_export(args.family_id, started_at_utc=utc_now())
    if args.write:
        write_json(CERT_DIR / f"{payload['certificate_id']}.json", payload)
    else:
        print(json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
