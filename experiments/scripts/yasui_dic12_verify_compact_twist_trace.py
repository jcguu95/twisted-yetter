#!/usr/bin/env python3
"""Verify the compact Yasui a=1 D(Dic12) witness-twist trace."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DEFAULT_TRACE = (
    "experiments/results/yasui/"
    "figure3-a1-r1-normalized-dic12-witness-g-component-a-twist-compact-trace-v1.jsonl"
)

SYMBOLS = {
    "1": 1 + 0j,
    "-1": -1 + 0j,
    "i": 1j,
    "-i": -1j,
}


def parse_pair(pair: list[str]) -> complex:
    return complex(float(pair[0]), float(pair[1]))


def close(z: complex, w: complex, tolerance: float) -> bool:
    return abs(z - w) <= tolerance


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--trace", default=DEFAULT_TRACE)
    parser.add_argument("--tolerance", type=float, default=1e-8)
    args = parser.parse_args()

    trace_path = Path(args.trace)
    with trace_path.open("r", encoding="utf-8") as f:
        metadata = json.loads(next(f))
        powers = metadata["case"]["twist_powers_in_braid_order"]
        aggregate_untwisted = 0j
        aggregate_twisted = 0j
        row_count = 0
        bad_rows = []
        for line_number, line in enumerate(f, start=2):
            row = json.loads(line)
            row_count += 1
            monodromies = [SYMBOLS[symbol] for symbol in row["m"]]
            phase = 1 + 0j
            for monodromy, power in zip(monodromies, powers):
                phase *= monodromy**power
            recorded_phase = SYMBOLS[row["p"]]
            untwisted = parse_pair(row["u"])
            twisted = parse_pair(row["t"])
            expected_twisted = untwisted * phase
            aggregate_untwisted += untwisted
            aggregate_twisted += twisted
            if phase != recorded_phase or not close(twisted, expected_twisted, args.tolerance):
                bad_rows.append(
                    {
                        "line_number": line_number,
                        "sector_index": row.get("i"),
                        "phase": row["p"],
                        "computed_phase": str(phase),
                        "twisted": str(twisted),
                        "expected_twisted": str(expected_twisted),
                    }
                )

    expected_row_count = metadata["row_count"]
    expected_twisted = complex(
        float(metadata["aggregate_twisted"]["real"]),
        float(metadata["aggregate_twisted"]["imag"]),
    )
    expected_untwisted = complex(
        float(metadata["aggregate_untwisted_reconstructed"]["real"]),
        float(metadata["aggregate_untwisted_reconstructed"]["imag"]),
    )
    normalized = aggregate_twisted / float(metadata["standard_split_reference"]["baseline_untwisted_raw"]["abs"]) * 12
    # The normalization above uses the recorded split baseline magnitude only as
    # a display cross-check; the authoritative normalized value is in metadata.
    recorded_normalized = complex(
        float(metadata["normalized_twisted_by_global_dimension_sum_d_squared"]["real"]),
        float(metadata["normalized_twisted_by_global_dimension_sum_d_squared"]["imag"]),
    )
    normalized_by_144 = aggregate_twisted / 144.0

    status = (
        row_count == expected_row_count
        and not bad_rows
        and close(aggregate_twisted, expected_twisted, args.tolerance)
        and close(aggregate_untwisted, expected_untwisted, args.tolerance)
        and close(normalized_by_144, recorded_normalized, args.tolerance)
    )
    report = {
        "status": "pass" if status else "fail",
        "trace": str(trace_path),
        "schema": metadata["schema"],
        "row_count": row_count,
        "expected_row_count": expected_row_count,
        "bad_row_count": len(bad_rows),
        "bad_rows_first_10": bad_rows[:10],
        "aggregate_untwisted": f"{aggregate_untwisted.real}{aggregate_untwisted.imag:+}j",
        "aggregate_twisted": f"{aggregate_twisted.real}{aggregate_twisted.imag:+}j",
        "normalized_twisted_by_144": f"{normalized_by_144.real}{normalized_by_144.imag:+}j",
        "metadata_normalized_twisted": metadata[
            "normalized_twisted_by_global_dimension_sum_d_squared"
        ]["display"],
        "display_ratio_check_against_baseline_magnitude": f"{normalized.real}{normalized.imag:+}j",
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if status else 1


if __name__ == "__main__":
    raise SystemExit(main())
