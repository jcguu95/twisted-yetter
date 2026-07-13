"""Aggregate restartable native-Morse singleton checkpoint files."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import time

from experiments.scripts.morse_singleton_workload import (
    atomic_write_json,
    canonical_json_bytes,
    iter_singleton_payloads,
)


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


def close(left, right, tolerance):
    return abs(complex(left) - complex(right)) <= tolerance


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-count", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--tolerance", type=float, default=1e-8)
    parser.add_argument("roots", nargs="+", type=Path)
    args = parser.parse_args()
    started = datetime.now(UTC)
    clock = time.perf_counter()

    records = {}
    duplicates = []
    identity_hashes = set()
    worker_context_hashes = set()
    elapsed = []
    source_record_count = 0
    source_record_digest = hashlib.sha256()
    source_locator_sample = []
    for source_locator, payload in iter_singleton_payloads(args.roots):
        if payload.get("status") != "pass":
            continue
        index = int(payload["sector_index"])
        value = complex_from_json(payload["weighted_value"])
        identity_hashes.add(payload["evaluation_identity_sha256"])
        if payload.get("worker_context_sha256"):
            worker_context_hashes.add(payload["worker_context_sha256"])
        elapsed.append(float(payload["elapsed_seconds"]))
        source_record_digest.update(canonical_json_bytes(payload) + b"\n")
        source_record_count += 1
        if len(source_locator_sample) < 100:
            source_locator_sample.append(source_locator)
        if index in records:
            previous = records[index]
            agrees = close(previous["value"], value, args.tolerance)
            duplicates.append(
                {
                    "sector_index": index,
                    "first_path": previous["path"],
                    "second_path": source_locator,
                    "values_agree": agrees,
                    "absolute_difference": abs(previous["value"] - value),
                }
            )
            if not agrees:
                continue
        else:
            records[index] = {"value": value, "path": source_locator}

    expected = set(range(args.expected_count))
    observed = set(records)
    missing = sorted(expected - observed)
    extra = sorted(observed - expected)
    conflicting = [row for row in duplicates if not row["values_agree"]]
    aggregate = sum((records[index]["value"] for index in sorted(observed)), 0.0j)
    status = "pass" if not missing and not extra and not conflicting and len(identity_hashes) == 1 else "incomplete-or-needs-review"
    payload = {
        "schema": "twisted-yetter.native-morse-singleton-aggregate.v1",
        "status": status,
        "mathematical_status": "NUMERICAL_SINGLETON_AGGREGATE_WITH_INPUT_CAVEATS_INHERITED",
        "generator_script": "experiments/scripts/morse_singleton_aggregate.py",
        "roots": [str(root) for root in args.roots],
        "expected_sector_count": args.expected_count,
        "observed_unique_sector_count": len(observed),
        "missing_sector_count": len(missing),
        "missing_sector_indices": missing,
        "extra_sector_indices": extra,
        "duplicate_count": len(duplicates),
        "conflicting_duplicate_count": len(conflicting),
        "duplicates": duplicates,
        "evaluation_identity_sha256_values": sorted(identity_hashes),
        "worker_context_sha256_values": sorted(worker_context_hashes),
        "weighted_aggregate": complex_json(aggregate),
        "elapsed_seconds_summary": {
            "count": len(elapsed),
            "sum": sum(elapsed),
            "min": min(elapsed) if elapsed else None,
            "max": max(elapsed) if elapsed else None,
        },
        "source_record_count": source_record_count,
        "source_record_digest_sha256": source_record_digest.hexdigest(),
        "source_locator_sample": source_locator_sample,
        "source_locator_sample_truncated": source_record_count > len(source_locator_sample),
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
