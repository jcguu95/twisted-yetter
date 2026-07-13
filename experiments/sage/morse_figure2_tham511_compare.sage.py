"""Compare a Figure 2 singleton aggregate with the standard CP2 presentation."""

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
    parser.add_argument("--standard-character", type=int, default=0)
    parser.add_argument("--three-handle-count", type=int, default=2)
    parser.add_argument("--tolerance", type=float, default=1e-7)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = datetime.now(UTC)
    clock = time.perf_counter()

    aggregate_payload = json.loads(args.aggregate.read_text())
    category, display_name, category_id = build_category(args.category, args.level)
    global_dimension_D = sum(
        float(category.dimension(label)) ** 2 for label in category.labels
    )
    normalization = global_dimension_D ** args.three_handle_count
    raw = complex_from_json(aggregate_payload["weighted_aggregate"])
    normalized = raw / normalization
    standard = sum(
        complex(category.dimension(label)) ** 2
        * complex(category.character(args.standard_character, label))
        * complex(category.twist(label))
        for label in category.labels
    )
    difference = normalized - standard
    payload = {
        "schema": "twisted-yetter.native-morse-figure2-tham511-comparison.v1",
        "status": "pass" if abs(difference) <= args.tolerance else "needs-review",
        "mathematical_status": "NUMERICAL_CONSISTENCY_CHECK_NOT_A_THEOREM",
        "generator_script": "experiments/sage/morse_figure2_tham511_compare.sage.py",
        "argv": sys.argv,
        "aggregate": str(args.aggregate),
        "aggregate_sha256": file_sha256(args.aggregate),
        "category": display_name,
        "category_id": category_id,
        "standard_character": args.standard_character,
        "three_handle_count": args.three_handle_count,
        "normalization_convention": {
            "D": "sum_i d_i^2",
            "D_value": global_dimension_D,
            "factor": f"D^(-{args.three_handle_count})",
            "divisor": normalization,
            "warning": "D is the global dimension sum_i d_i^2, not its square root",
        },
        "yasui_raw": complex_json(raw),
        "yasui_normalized": complex_json(normalized),
        "standard_cp2_plus_one_omega": complex_json(standard),
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
