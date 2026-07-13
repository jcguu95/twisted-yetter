"""Aggregate grouped native-Morse chunk sums with exact bin coverage checks."""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path


def complex_json(value):
    value = complex(value)
    return {
        "real": repr(value.real),
        "imag": repr(value.imag),
        "abs": repr(abs(value)),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-bin-count", type=int, required=True)
    parser.add_argument("--expected-sectors-per-bin", type=int, required=True)
    parser.add_argument("--expected-total-sectors", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("chunks", nargs="+", type=Path)
    args = parser.parse_args()
    sums = defaultdict(complex)
    counts = defaultdict(int)
    group_components = None
    identity = None
    chunk_rows = []
    for path in args.chunks:
        payload = json.loads(path.read_text())
        current_identity = (payload["input"], payload["category"])
        if identity is None:
            identity = current_identity
            group_components = tuple(payload["group_components"])
        if current_identity != identity or tuple(payload["group_components"]) != group_components:
            raise ValueError(f"chunk identity/group mismatch: {path}")
        for row in payload["grouped_weighted_partial_sums"]:
            key = tuple(row["labels"])
            value = complex(
                float(row["weighted_partial_sum"]["real"]),
                float(row["weighted_partial_sum"]["imag"]),
            )
            sums[key] += value
            counts[key] += int(row["sector_count"])
        sector_range = payload["sector_range"]
        chunk_rows.append(
            {
                "path": str(path),
                "start": sector_range["start"],
                "count": sector_range["count"],
            }
        )
    ordered_chunks = sorted(chunk_rows, key=lambda row: row["start"])
    cursor = 0
    coverage_ok = True
    for row in ordered_chunks:
        coverage_ok &= row["start"] == cursor
        cursor = row["start"] + row["count"]
    coverage_ok &= cursor == args.expected_total_sectors
    bins_ok = (
        len(sums) == args.expected_bin_count
        and all(count == args.expected_sectors_per_bin for count in counts.values())
        and sum(counts.values()) == args.expected_total_sectors
    )
    rows = [
        {
            "labels": list(key),
            "sector_count": counts[key],
            "weighted_sum": complex_json(sums[key]),
        }
        for key in sorted(sums)
    ]
    total = sum(sums.values(), 0.0 + 0.0j)
    result = {
        "schema": "twisted-yetter.native-morse-grouped-aggregate.v1",
        "status": "pass" if coverage_ok and bins_ok else "needs-review",
        "input": identity[0],
        "category": identity[1],
        "group_components": list(group_components),
        "bin_count": len(rows),
        "expected_bin_count": args.expected_bin_count,
        "expected_sectors_per_bin": args.expected_sectors_per_bin,
        "total_sector_count": sum(counts.values()),
        "contiguous_complete_chunk_coverage": coverage_ok,
        "exact_bin_coverage": bins_ok,
        "total_weighted_sum": complex_json(total),
        "bins": rows,
        "chunks": ordered_chunks,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output.resolve())
    if result["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
