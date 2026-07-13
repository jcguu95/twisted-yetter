"""Compare Yasui Figure 2 a=1 braid and mechanically generated Morse closure."""

from __future__ import annotations

from datetime import UTC, datetime
from itertools import product
import json
from pathlib import Path
import time

from experiments.sage.braid_closure_morse import (
    braid_closure_morse_forms,
    trace_fundamental_forms,
)
from experiments.sage.morse_category_registry import build_category
from experiments.sage.morse_fusion_evaluator import MorseEvaluator


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT_OUTPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure2-cp2-a1-r1-braid-closure-morse-v1.json"
RESULT_OUTPUT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure2-cp2-a1-r1-su2-2-native-morse-bridge-v1.json"

N_STRANDS = 5
BRAID_WORD = (
    1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2, -4, 3, 2, 1, 2, 3, 3, 2, 3, 4, -3,
)
COMPONENT_ORDER_IN_BRAID = ("A", "C", "B")
FRAMINGS = (4, 4, 1)


def complex_json(value):
    value = complex(value)
    return {
        "real": repr(value.real),
        "imag": repr(value.imag),
        "abs": repr(abs(value)),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def main():
    started = time.perf_counter()
    category, _, _ = build_category("su2", 2)
    backend = category.backend
    native = MorseEvaluator(category)
    forms, component_index = braid_closure_morse_forms(
        N_STRANDS, BRAID_WORD, FRAMINGS
    )
    drawing_payload = trace_fundamental_forms(forms)
    input_payload = {
        "schema": "twisted-yetter.braid-closure-morse-input.v1",
        "status": "MECHANICALLY_DERIVED_FROM_RECORDED_BRAID",
        "source": "Yasui Figure 2 CP2(a=1) R1-normalized recorded braid payload",
        "n_strands": N_STRANDS,
        "braid_word": list(BRAID_WORD),
        "component_order_in_braid": list(COMPONENT_ORDER_IN_BRAID),
        "framings_in_braid_order": list(FRAMINGS),
        "morse_component_to_braid_component_index": component_index,
        **drawing_payload,
    }
    INPUT_OUTPUT.write_text(json.dumps(input_payload, indent=2, sort_keys=True) + "\n")

    rows = []
    native_omega = 0.0 + 0.0j
    max_difference = 0.0
    for labels in product(category.labels, repeat=3):
        morse_labels = {
            name: labels[index] for name, index in component_index.items()
        }
        observed, stats = native.fixed_label_value(forms, morse_labels)
        expected = complex(
            backend.fixed_label_value(N_STRANDS, BRAID_WORD, labels, FRAMINGS)
        )
        difference = observed - expected
        max_difference = max(max_difference, abs(difference))
        coefficient = 1.0
        for label in labels:
            coefficient *= float(category.dimension(label))
        native_omega += coefficient * observed
        rows.append(
            {
                "labels_in_braid_component_order": list(labels),
                "labels_by_morse_component": morse_labels,
                "native": complex_json(observed),
                "braid": complex_json(expected),
                "difference": complex_json(difference),
                "pass": abs(difference) <= 1e-9,
                "native_stats": stats,
            }
        )
    braid_omega = complex(
        backend.omega_value(N_STRANDS, BRAID_WORD, FRAMINGS, (0, 0, 0))
    )
    payload = {
        "schema": "twisted-yetter.yasui-figure2-a1-native-morse-bridge.v1",
        "status": "pass" if all(row["pass"] for row in rows) and abs(native_omega - braid_omega) <= 1e-8 else "needs-review",
        "mathematical_status": "NUMERICAL_BRAID_TO_MORSE_CALIBRATION",
        "generator_script": "experiments/sage/yasui_figure2_cp2_a1_native_morse_bridge.sage.py",
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python experiments/sage/yasui_figure2_cp2_a1_native_morse_bridge.sage.py",
        "source_input": str(INPUT_OUTPUT.relative_to(REPO_ROOT)),
        "category": "SU(2)_2",
        "fixed_sector_count": len(rows),
        "max_fixed_sector_abs_difference": repr(max_difference),
        "native_omega0": complex_json(native_omega),
        "braid_omega0": complex_json(braid_omega),
        "omega0_difference": complex_json(native_omega - braid_omega),
        "rows": rows,
        "elapsed_seconds": time.perf_counter() - started,
        "utc_finish": datetime.now(UTC).isoformat(),
    }
    RESULT_OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(RESULT_OUTPUT.resolve())
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
