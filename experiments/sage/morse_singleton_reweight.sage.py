"""Reweight native-Morse fixed-label singleton results by a character assignment."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

from sage.env import SAGE_VERSION

from experiments.sage.morse_category_registry import (
    CATEGORY_CHOICES,
    build_category,
    category_payload_path,
)
from experiments.sage.morse_fusion_evaluator import analyze_topology
from experiments.scripts.morse_singleton_workload import atomic_write_json, file_sha256
from experiments.scripts.morse_singleton_workload import (
    canonical_json_bytes,
    iter_singleton_payloads,
    payload_sha256,
)


REPO_ROOT = Path(__file__).resolve().parents[2]


def complex_from_json(payload):
    return complex(float(payload["real"]), float(payload["imag"]))


def complex_json(value):
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def parse_assignment(path, components):
    payload = json.loads(path.read_text())
    if isinstance(payload, list):
        if len(payload) != len(components):
            raise ValueError("assignment list length does not match component count")
        return dict(zip(components, payload, strict=True))
    if set(payload) != set(components):
        raise ValueError("assignment object keys do not match Morse components")
    return payload


def command(argv):
    try:
        return subprocess.check_output(
            argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--category", choices=CATEGORY_CHOICES, required=True)
    parser.add_argument("--level", type=int)
    parser.add_argument("--characters", type=Path, required=True)
    parser.add_argument("--expected-count", type=int, required=True)
    parser.add_argument("--tolerance", type=float, default=1e-8)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("roots", nargs="+", type=Path)
    args = parser.parse_args()

    started = datetime.now(UTC)
    clock = time.perf_counter()
    input_payload = json.loads(args.input.read_text())
    topology = analyze_topology(tuple(input_payload["forms"]))
    components = tuple(topology.component_order)
    characters = parse_assignment(args.characters, components)
    category, display_name, category_id = build_category(args.category, args.level)
    input_sha256 = file_sha256(args.input)

    records = {}
    duplicates = []
    source_identity_hashes = set()
    fixed_source_context_identity_hashes = set()
    source_digest = hashlib.sha256()
    elapsed = []
    source_record_count = 0
    for root in args.roots:
        for path in sorted(root.rglob("worker-context-*.json")):
            context = json.loads(path.read_text())
            identity = context["evaluation_identity"]
            fixed_identity = {
                key: value
                for key, value in identity.items()
                if key != "character_assignments"
            }
            if fixed_identity.get("input_sha256") != input_sha256:
                raise ValueError(f"source input identity mismatch in {path}")
            if fixed_identity.get("category_id") != category_id:
                raise ValueError(f"source category identity mismatch in {path}")
            if tuple(fixed_identity.get("component_order", ())) != components:
                raise ValueError(f"source component order mismatch in {path}")
            fixed_source_context_identity_hashes.add(payload_sha256(fixed_identity))

    for source_locator, payload in iter_singleton_payloads(args.roots):
        if payload.get("status") != "pass":
            continue
        index = int(payload["sector_index"])
        labels_tuple = tuple(payload["labels"])
        if len(labels_tuple) != len(components):
            raise ValueError(f"component count mismatch in {source_locator}")
        fixed_value = complex_from_json(payload["fixed_value"])
        source_identity_hashes.add(payload["evaluation_identity_sha256"])
        source_digest.update(canonical_json_bytes(payload) + b"\n")
        source_record_count += 1
        elapsed.append(float(payload.get("elapsed_seconds", 0.0)))
        if index in records:
            previous = records[index]
            agrees = (
                previous["labels"] == labels_tuple
                and abs(previous["fixed_value"] - fixed_value) <= args.tolerance
            )
            duplicates.append(
                {
                    "sector_index": index,
                    "first_path": previous["path"],
                    "second_path": source_locator,
                    "fixed_results_agree": agrees,
                }
            )
            if not agrees:
                continue
        else:
            records[index] = {
                "labels": labels_tuple,
                "fixed_value": fixed_value,
                "path": source_locator,
            }

    expected = set(range(args.expected_count))
    observed = set(records)
    missing = sorted(expected - observed)
    extra = sorted(observed - expected)
    conflicting = [row for row in duplicates if not row["fixed_results_agree"]]
    weighted = 0.0j
    for index in sorted(observed):
        row = records[index]
        coefficient = 1.0 + 0.0j
        for component, label in zip(components, row["labels"], strict=True):
            coefficient *= complex(category.dimension(label))
            coefficient *= complex(category.character(characters[component], label))
        weighted += coefficient * row["fixed_value"]

    status = (
        "pass"
        if (
            not missing
            and not extra
            and not conflicting
            and len(source_identity_hashes) == 1
            and len(fixed_source_context_identity_hashes) == 1
        )
        else "incomplete-or-needs-review"
    )
    payload_path = category_payload_path(args.category)
    payload = {
        "schema": "twisted-yetter.native-morse-singleton-reweighted-aggregate.v1",
        "status": status,
        "mathematical_status": "NUMERICAL_POSTHOC_CHARACTER_REWEIGHTING_WITH_INPUT_CAVEATS_INHERITED",
        "generator_script": "experiments/sage/morse_singleton_reweight.sage.py",
        "argv": sys.argv,
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python "
        + " ".join(sys.argv),
        "input": str(args.input),
        "input_sha256": input_sha256,
        "category": display_name,
        "category_id": category_id,
        "level": args.level,
        "category_payload": str(payload_path) if payload_path else None,
        "category_payload_sha256": file_sha256(payload_path) if payload_path else None,
        "component_order": list(components),
        "characters": characters,
        "characters_path": str(args.characters),
        "characters_sha256": file_sha256(args.characters),
        "roots": [str(root) for root in args.roots],
        "expected_sector_count": args.expected_count,
        "observed_unique_sector_count": len(observed),
        "missing_sector_count": len(missing),
        "missing_sector_indices": missing,
        "extra_sector_indices": extra,
        "duplicate_count": len(duplicates),
        "conflicting_duplicate_count": len(conflicting),
        "duplicates": duplicates,
        "source_evaluation_identity_sha256_values": sorted(source_identity_hashes),
        "fixed_source_context_identity_sha256_values": sorted(
            fixed_source_context_identity_hashes
        ),
        "source_record_count": source_record_count,
        "source_file_digest_sha256": source_digest.hexdigest(),
        "weighted_aggregate": complex_json(weighted),
        "source_singleton_elapsed_seconds_summary": {
            "count": len(elapsed),
            "sum": sum(elapsed),
            "min": min(elapsed) if elapsed else None,
            "max": max(elapsed) if elapsed else None,
        },
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "git_dirty": bool(command(["git", "status", "--short"])),
        },
        "environment": {
            "hostname": platform.node(),
            "platform": platform.platform(),
            "cpu_count": os.cpu_count(),
            "sage": SAGE_VERSION,
            "python": sys.version,
        },
        "utc_start": started.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "aggregation_elapsed_seconds": time.perf_counter() - clock,
    }
    atomic_write_json(args.output, payload)
    print(args.output.resolve())
    if status != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
