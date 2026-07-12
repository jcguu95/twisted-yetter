"""Aggregate contiguous native-Morse evaluator chunks."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import json
from pathlib import Path


def parse_complex(payload):
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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("chunks", nargs="+", type=Path)
    parser.add_argument("--expected-count", type=int, required=True)
    parser.add_argument("--expected-real", type=float)
    parser.add_argument("--expected-imag", type=float, default=0.0)
    parser.add_argument("--tolerance", type=float, default=1e-7)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    rows = [json.loads(path.read_text()) for path in args.chunks]
    ordered = list(zip(args.chunks, rows, strict=True))
    covered = set()
    total = 0.0 + 0.0j
    chunk_records = []
    identity = None
    for path, row in ordered:
        current_identity = (
            row["input"], row["category"], tuple(row["component_order"]),
            tuple(sorted(row["character_assignments"].items())),
        )
        if identity is None:
            identity = current_identity
        elif current_identity != identity:
            raise ValueError(f"chunk identity mismatch: {path}")
        if row.get("sector_indices") is not None:
            indices = tuple(int(index) for index in row["sector_indices"])
            range_payload = None
        else:
            start = int(row["sector_range"]["start"])
            count = int(row["sector_range"]["count"])
            indices = tuple(range(start, start + count))
            range_payload = {"start": start, "count": count}
        overlap = covered.intersection(indices)
        if overlap:
            raise ValueError(f"chunk overlap at {path}: {sorted(overlap)[:10]}")
        covered.update(indices)
        total += parse_complex(row["weighted_partial_sum"])
        chunk_records.append(
            {
                "path": str(path),
                "sector_range": range_payload,
                "sector_count": len(indices),
                "min_sector_index": min(indices),
                "max_sector_index": max(indices),
                "elapsed_seconds": row["elapsed_seconds"],
                "partial_sum": row["weighted_partial_sum"],
            }
        )
    expected_indices = set(range(args.expected_count))
    if covered != expected_indices:
        missing = sorted(expected_indices - covered)
        extra = sorted(covered - expected_indices)
        raise ValueError(
            f"sector coverage mismatch: covered={len(covered)} expected={args.expected_count} "
            f"missing_head={missing[:10]} extra_head={extra[:10]}"
        )

    checks = {"contiguous_complete_sector_coverage": True}
    expected_payload = None
    status = "pass"
    if args.expected_real is not None:
        expected = complex(args.expected_real, args.expected_imag)
        difference = total - expected
        checks["matches_expected"] = abs(difference) <= args.tolerance
        expected_payload = {
            "value": complex_json(expected),
            "difference": complex_json(difference),
            "tolerance": args.tolerance,
        }
        if not checks["matches_expected"]:
            status = "needs-review"

    payload = {
        "schema": "twisted-yetter.native-morse-rt-chunk-aggregate.v1",
        "status": status,
        "mathematical_status": "NUMERICAL_COMPARISON_INHERITS_INPUT_DIAGRAM_CAVEATS",
        "generator_script": "experiments/scripts/morse_native_aggregate.py",
        "input": identity[0],
        "category": identity[1],
        "component_order": list(identity[2]),
        "character_assignments": dict(identity[3]),
        "sector_count": len(covered),
        "value": complex_json(total),
        "expected": expected_payload,
        "checks": checks,
        "chunks": chunk_records,
        "aggregate_worker_seconds": sum(float(row["elapsed_seconds"]) for _, row in ordered),
        "utc_finish": datetime.now(UTC).isoformat(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(args.output.resolve())
    if status != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
