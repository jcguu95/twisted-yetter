"""Compare native-Morse singleton checkpoints with a calibrated braid backend."""

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
from experiments.sage.morse_fusion_evaluator import analyze_topology
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
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--category", choices=CATEGORY_CHOICES, required=True)
    parser.add_argument("--level", type=int)
    parser.add_argument("--tolerance", type=float, default=1e-7)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("roots", nargs="+", type=Path)
    args = parser.parse_args()
    started = datetime.now(UTC)
    clock = time.perf_counter()

    source = json.loads(args.input.read_text())
    topology = analyze_topology(source["forms"])
    category, display_name, category_id = build_category(args.category, args.level)
    backend = category.backend
    mapping = {
        component: int(index)
        for component, index in source["morse_component_to_braid_component_index"].items()
    }
    if set(mapping) != set(topology.component_order):
        raise ValueError("Morse-to-braid component mapping does not match topology")

    by_index = {}
    duplicate_paths = []
    for root in args.roots:
        for path in sorted(root.rglob("sector-*.json")):
            payload = json.loads(path.read_text())
            index = int(payload["sector_index"])
            if index in by_index:
                duplicate_paths.append([by_index[index][0], str(path)])
                continue
            by_index[index] = (str(path), payload)

    rows = []
    for sector_index in sorted(by_index):
        path, singleton = by_index[sector_index]
        native_labels = dict(zip(topology.component_order, singleton["labels"], strict=True))
        braid_labels = [None] * len(topology.component_order)
        for component, label in native_labels.items():
            braid_labels[mapping[component]] = label
        expected_result = backend.fixed_label_value(
            int(source["n_strands"]),
            tuple(int(item) for item in source["braid_word"]),
            tuple(braid_labels),
            tuple(int(item) for item in source["framings_in_braid_order"]),
        )
        expected = complex(
            expected_result[0] if isinstance(expected_result, tuple) else expected_result
        )
        observed = complex_from_json(singleton["fixed_value"])
        difference = observed - expected
        rows.append(
            {
                "sector_index": sector_index,
                "labels_in_morse_component_order": singleton["labels"],
                "labels_in_braid_component_order": braid_labels,
                "singleton_path": path,
                "observed_native_morse": complex_json(observed),
                "expected_braid_backend": complex_json(expected),
                "absolute_difference": abs(difference),
                "pass": abs(difference) <= args.tolerance,
            }
        )

    failures = [row for row in rows if not row["pass"]]
    payload = {
        "schema": "twisted-yetter.native-morse-singleton-braid-bridge.v1",
        "status": "pass" if not failures and not duplicate_paths else "needs-review",
        "mathematical_status": "NUMERICAL_CROSS_BACKEND_CALIBRATION",
        "generator_script": "experiments/sage/morse_singleton_braid_compare.sage.py",
        "argv": sys.argv,
        "input": str(args.input),
        "input_sha256": file_sha256(args.input),
        "category": display_name,
        "category_id": category_id,
        "component_order_morse": list(topology.component_order),
        "component_order_braid": source["component_order_in_braid"],
        "morse_component_to_braid_component_index": mapping,
        "tolerance": args.tolerance,
        "row_count": len(rows),
        "failure_count": len(failures),
        "duplicate_paths": duplicate_paths,
        "max_absolute_difference": max(
            (row["absolute_difference"] for row in rows), default=0.0
        ),
        "roots": [str(root) for root in args.roots],
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
        "rows": rows,
    }
    atomic_write_json(args.output, payload)
    print(args.output.resolve())
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
