"""Evaluate the standard CP2 # 9(-CP2) presentation with native Morse F/R."""

from __future__ import annotations

from datetime import UTC, datetime
import importlib.util
import json
from pathlib import Path
import sys
import time

from experiments.sage.morse_category_adapters import SU2KMorseAdapter
from experiments.sage.morse_fusion_evaluator import MorseEvaluator


REPO_ROOT = Path(__file__).resolve().parents[2]
SU2_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
INPUT_OUTPUT = REPO_ROOT / "experiments" / "inputs" / "standard" / "e1-cp2-sum-9barcp2-morse-v1.json"
RESULT_OUTPUT = REPO_ROOT / "experiments" / "results" / "standard" / "e1-cp2-sum-9barcp2-su2-2-native-morse-v1.json"
FRAMINGS = (1,) + (-1,) * 9


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def component_forms(name, framing):
    return (
        {"kind": "cup", "piece": name, "at": "far-left"},
        {
            "kind": "kink",
            "strand": f"{name}.left",
            "sign": "+" if framing > 0 else "-",
            "times": abs(framing),
        },
        {"kind": "cap", "strands": [f"{name}.left", f"{name}.right"]},
    )


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
    su2 = load_module(SU2_PATH, "su2k_for_standard_e1_native_morse")
    category = SU2KMorseAdapter(su2.SU2KBraidEvaluator(2, exact=False))
    evaluator = MorseEvaluator(category)
    names = tuple(f"U{index}" for index in range(10))
    forms = tuple(
        form
        for name, framing in zip(names, FRAMINGS, strict=True)
        for form in component_forms(name, framing)
    )

    INPUT_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    INPUT_OUTPUT.write_text(
        json.dumps(
            {
                "schema": "twisted-yetter.standard-e1-morse-input.v1",
                "status": "STANDARD_SPLIT_UNLINK_PRESENTATION",
                "manifold": "CP2 # 9(-CP2)",
                "component_count": 10,
                "framings": list(FRAMINGS),
                "linking_matrix_diagonal": list(FRAMINGS),
                "determinant": -1,
                "signature": -8,
                "forms": list(forms),
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )

    full_value, full_stats = evaluator.omega_value(forms)
    plus_value, plus_stats = evaluator.omega_value(component_forms("P", 1))
    minus_value, minus_stats = evaluator.omega_value(component_forms("M", -1))
    factorized_value = plus_value * minus_value**9
    difference = full_value - factorized_value
    payload = {
        "schema": "twisted-yetter.standard-e1-su2-2-native-morse.v1",
        "status": "pass" if abs(difference) <= 1e-8 else "needs-review",
        "mathematical_status": "NUMERICAL_IMPLEMENTATION_CONTROL",
        "category": "SU(2)_2",
        "presentation": "ten-component split unlink with framings (+1,-1^9)",
        "source_input": str(INPUT_OUTPUT.relative_to(REPO_ROOT)),
        "native_full_omega0": complex_json(full_value),
        "native_factorized_omega0": complex_json(factorized_value),
        "difference": complex_json(difference),
        "positive_unknot_factor": complex_json(plus_value),
        "negative_unknot_factor": complex_json(minus_value),
        "full_stats": full_stats,
        "positive_factor_stats": plus_stats,
        "negative_factor_stats": minus_stats,
        "generator_script": "experiments/sage/standard_e1_su2_2_native_morse.sage.py",
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python experiments/sage/standard_e1_su2_2_native_morse.sage.py",
        "elapsed_seconds": time.perf_counter() - started,
        "utc_finish": datetime.now(UTC).isoformat(),
    }
    RESULT_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    RESULT_OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(RESULT_OUTPUT.resolve())
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
