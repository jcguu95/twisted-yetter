"""Compare a Morse aggregate with a diagonal +/-1 Kirby presentation."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import json
import os
from pathlib import Path
import platform
import sys
import time

from sage.env import SAGE_VERSION

from experiments.sage.morse_category_registry import CATEGORY_CHOICES, build_category
from experiments.scripts.morse_singleton_workload import atomic_write_json, file_sha256


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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--aggregate", type=Path, required=True)
    parser.add_argument("--category", choices=CATEGORY_CHOICES, required=True)
    parser.add_argument("--level", type=int)
    parser.add_argument("--positive", type=int, required=True)
    parser.add_argument("--negative", type=int, required=True)
    parser.add_argument("--tolerance", type=float, default=1e-7)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = datetime.now(UTC)
    clock = time.perf_counter()

    aggregate_payload = json.loads(args.aggregate.read_text())
    category, display_name, category_id = build_category(args.category, args.level)
    gauss_plus = sum(
        complex(category.dimension(label)) ** 2 * complex(category.twist(label))
        for label in category.labels
    )
    gauss_minus = sum(
        complex(category.dimension(label)) ** 2 / complex(category.twist(label))
        for label in category.labels
    )
    expected = gauss_plus**args.positive * gauss_minus**args.negative
    observed_payload = aggregate_payload.get("weighted_aggregate") or aggregate_payload.get(
        "value"
    )
    if observed_payload is None:
        raise ValueError("aggregate has neither weighted_aggregate nor value")
    observed = complex_from_json(observed_payload)
    difference = observed - expected
    payload = {
        "schema": "twisted-yetter.native-morse-diagonal-standard-comparison.v1",
        "status": "pass" if abs(difference) <= args.tolerance else "needs-review",
        "mathematical_status": "NUMERICAL_CROSS_PRESENTATION_CONSISTENCY_NOT_A_THEOREM",
        "generator_script": "experiments/sage/morse_diagonal_standard_compare.sage.py",
        "argv": sys.argv,
        "aggregate": str(args.aggregate),
        "aggregate_sha256": file_sha256(args.aggregate),
        "category": display_name,
        "category_id": category_id,
        "diagonal_standard_presentation": {
            "positive_one_framed_omega_components": args.positive,
            "negative_one_framed_omega_components": args.negative,
            "formula": "p_plus^positive * p_minus^negative",
            "p_plus": complex_json(gauss_plus),
            "p_minus": complex_json(gauss_minus),
        },
        "observed": complex_json(observed),
        "expected": complex_json(expected),
        "difference": complex_json(difference),
        "tolerance": args.tolerance,
        "environment": {
            "hostname": platform.node(),
            "platform": platform.platform(),
            "cpu_count": os.cpu_count(),
            "sage": SAGE_VERSION,
            "python": sys.version,
        },
        "utc_start": started.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
    }
    atomic_write_json(args.output, payload)
    print(args.output.resolve())
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
