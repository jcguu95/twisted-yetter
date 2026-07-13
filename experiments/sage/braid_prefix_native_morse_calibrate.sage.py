"""Calibrate native Morse evaluation on every prefix of a recorded braid."""

from __future__ import annotations

from datetime import UTC, datetime
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys
import time

from experiments.sage.braid_closure_morse import (
    braid_closure_morse_forms,
    braid_component_data,
)
from experiments.sage.morse_category_adapters import SU2KMorseAdapter
from experiments.sage.morse_fusion_evaluator import MorseEvaluator


REPO_ROOT = Path(__file__).resolve().parents[2]
SU2_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
OUTPUT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure2-cp2-a1-r1-su2-2-braid-prefix-calibration-v1.json"
N_STRANDS = 5
BRAID_WORD = (
    1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2, -4, 3, 2, 1, 2, 3, 3, 2, 3, 4, -3,
)


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def main():
    started = time.perf_counter()
    su2 = load_module(SU2_PATH, "su2k_for_braid_prefix_calibration")
    backend = su2.SU2KBraidEvaluator(2, exact=False)
    category = SU2KMorseAdapter(backend)
    native = MorseEvaluator(category)
    prefixes = []
    global_max = 0.0

    for length in range(len(BRAID_WORD) + 1):
        word = BRAID_WORD[:length]
        cycles, _, writhe = braid_component_data(N_STRANDS, word)
        forms, component_index = braid_closure_morse_forms(
            N_STRANDS, word, writhe
        )
        maximum = 0.0
        failing = 0
        sector_count = 0
        for labels in product(category.labels, repeat=len(cycles)):
            morse_labels = {
                name: labels[index] for name, index in component_index.items()
            }
            observed, _ = native.fixed_label_value(forms, morse_labels)
            expected = complex(
                backend.fixed_label_value(N_STRANDS, word, labels, writhe)
            )
            difference = abs(observed - expected)
            maximum = max(maximum, difference)
            failing += difference > 1e-9
            sector_count += 1
        global_max = max(global_max, maximum)
        prefixes.append(
            {
                "prefix_length": length,
                "last_generator": word[-1] if word else None,
                "component_cycles": [list(cycle) for cycle in cycles],
                "blackboard_framings": list(writhe),
                "sector_count": sector_count,
                "failing_sector_count": failing,
                "max_abs_difference": repr(maximum),
                "pass": failing == 0,
            }
        )

    payload = {
        "schema": "twisted-yetter.braid-prefix-native-morse-calibration.v1",
        "status": "pass" if all(row["pass"] for row in prefixes) else "needs-review",
        "mathematical_status": "NUMERICAL_IMPLEMENTATION_CALIBRATION",
        "source_braid": "Yasui Figure 2 CP2(a=1) R1-normalized recorded braid",
        "n_strands": N_STRANDS,
        "braid_word": list(BRAID_WORD),
        "prefix_count": len(prefixes),
        "global_max_abs_difference": repr(global_max),
        "first_failing_prefix": next(
            (row["prefix_length"] for row in prefixes if not row["pass"]), None
        ),
        "prefixes": prefixes,
        "generator_script": "experiments/sage/braid_prefix_native_morse_calibrate.sage.py",
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python experiments/sage/braid_prefix_native_morse_calibrate.sage.py",
        "elapsed_seconds": time.perf_counter() - started,
        "utc_finish": datetime.now(UTC).isoformat(),
    }
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(OUTPUT.resolve())
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
