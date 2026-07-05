"""Sampled SU(2)_2 twisted sectors for Akbulut Figure 1 versus standard E(1)."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys
import time

from sage.all import ComplexField


REPO_ROOT = Path(__file__).resolve().parents[2]
BASE_SCRIPT = REPO_ROOT / "experiments" / "sage" / "akbulut_figure1_e1_su2_2_untwisted_comparison.sage.py"
SU2K_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "akbulut"
    / "figure1-e1-su2-2-sampled-twists-comparison-v1.json"
)

CF = ComplexField(120)
TOLERANCE = CF("1e-10")


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def complex_json(value):
    value = CF(value)
    return {
        "field": "ComplexField(120)",
        "display": str(value),
        "real": str(value.real()),
        "imag": str(value.imag()),
        "abs": str(abs(value)),
    }


def omega_many_from_cache(evaluator, cache, omega_label_rows):
    totals = [evaluator.zero() for _ in omega_label_rows]
    dimensions = {label: evaluator.dimension(label) for label in evaluator.labels}
    for fixed_labels, amplitude in cache.items():
        base_coefficient = evaluator.one()
        odd_positions = []
        for index, simple_label in enumerate(fixed_labels):
            base_coefficient *= dimensions[simple_label]
            if simple_label % 2:
                odd_positions.append(index)
        base_term = base_coefficient * amplitude
        for row_index, omega_labels in enumerate(omega_label_rows):
            parity = 0
            for index in odd_positions:
                parity ^= int(omega_labels[index])
            totals[row_index] += -base_term if parity else base_term
    return totals


def standard_labels_for_source_alpha(alpha_by_source, source_order):
    values = dict(zip(source_order, alpha_by_source, strict=True))
    h = values["Y"]
    e = [0] * 10
    e[8] = values["H"]
    e[7] = values["G"] ^ e[8]
    e[6] = values["F"] ^ e[7]
    e[5] = values["E"] ^ e[6]
    e[4] = values["D"] ^ e[5]
    e[3] = values["C"] ^ e[4]
    e[2] = values["B"] ^ e[3]
    e[1] = values["A"] ^ e[2]
    e[9] = values["X"] ^ h
    for index in range(1, 9):
        e[9] ^= e[index]
    return (h,) + tuple(e[index] for index in range(1, 10))


def sample_alphas(source_order):
    samples = []
    names = []

    def add(name, active):
        vector = tuple(1 if item in active else 0 for item in source_order)
        if vector not in samples:
            names.append(name)
            samples.append(vector)

    add("zero", [])
    for item in source_order:
        add(f"single-{item}", [item])
    for left, right in zip(source_order, source_order[1:], strict=False):
        add(f"adjacent-{left}-{right}", [left, right])
    add("H-X", ["H", "X"])
    add("X-Y", ["X", "Y"])
    add("H-X-Y", ["H", "X", "Y"])
    add("all", source_order)
    return list(zip(names, samples, strict=True))


def main():
    started = time.time()
    base = load_module(BASE_SCRIPT, "akbulut_base_for_sampled_twists")
    su2k = load_module(SU2K_PATH, "su2k_for_akbulut_sampled_twists")
    evaluator = su2k.SU2KBraidEvaluator(2, exact=False, precision=120)
    payload = json.loads(base.INPUT.read_text())
    component_words, crossing_signs, _ = base.source_oriented_gauss_code(payload)
    braid = base.Link([component_words, crossing_signs]).braid()
    n_strands = int(braid.parent().strands())
    braid_word = tuple(int(generator) for generator in braid.Tietze())
    braid_linking = [
        [int(entry) for entry in row]
        for row in base.braid_closure_linking_matrix(n_strands, braid_word)
    ]
    source_order = base.component_order(payload)
    source_target_matrix = base.target_matrix(payload)
    candidates = base.component_permutations(source_target_matrix, braid_linking)
    selected = base.choose_permutation(source_order, candidates)
    if selected is None:
        raise ValueError("could not match braid components to source components by linking matrix")
    source_order_in_braid = [source_order[source_index] for source_index in selected]
    framings_in_braid_order = [base.component_framings(payload)[source_index] for source_index in selected]
    print(
        json.dumps(
            {
                "phase": "braid-built",
                "n_strands": n_strands,
                "braid_word_length": len(braid_word),
                "elapsed_seconds": time.time() - started,
            },
            sort_keys=True,
        ),
        flush=True,
    )
    akbulut_cache = evaluator.sector_amplitudes(n_strands, braid_word, tuple(framings_in_braid_order))
    standard_framings = (1,) + (-1,) * 9
    standard_cache = evaluator.sector_amplitudes(10, (), standard_framings)
    print(
        json.dumps(
            {
                "phase": "caches-built",
                "akbulut_sector_count": len(akbulut_cache),
                "standard_sector_count": len(standard_cache),
                "elapsed_seconds": time.time() - started,
            },
            sort_keys=True,
        ),
        flush=True,
    )
    samples = sample_alphas(source_order)
    akbulut_label_rows = []
    standard_label_rows = []
    for _sample_id, alpha_source_order in samples:
        alpha_by_source = dict(zip(source_order, alpha_source_order, strict=True))
        akbulut_label_rows.append(tuple(alpha_by_source[name] for name in source_order_in_braid))
        standard_label_rows.append(standard_labels_for_source_alpha(alpha_source_order, source_order))
    akbulut_values = omega_many_from_cache(evaluator, akbulut_cache, akbulut_label_rows)
    standard_values = omega_many_from_cache(evaluator, standard_cache, standard_label_rows)

    rows = []
    mismatch_count = 0
    max_abs_difference = CF(0)
    for row_index, (sample_id, alpha_source_order) in enumerate(samples):
        alpha_by_source = dict(zip(source_order, alpha_source_order, strict=True))
        akbulut_labels = akbulut_label_rows[row_index]
        standard_labels = standard_label_rows[row_index]
        akbulut_value = akbulut_values[row_index]
        standard_value = standard_values[row_index]
        difference = CF(akbulut_value - standard_value)
        close = bool(abs(difference) < TOLERANCE)
        if not close:
            mismatch_count += 1
        max_abs_difference = max(max_abs_difference, abs(difference))
        rows.append(
            {
                "sample_id": sample_id,
                "alpha_source_order": source_order,
                "alpha_source": list(alpha_source_order),
                "akbulut_component_order": source_order_in_braid,
                "akbulut_omega_labels": list(akbulut_labels),
                "standard_order": ["h"] + [f"e{index}" for index in range(1, 10)],
                "standard_omega_labels": list(standard_labels),
                "akbulut_value": complex_json(akbulut_value),
                "standard_value": complex_json(standard_value),
                "abs_difference": str(abs(difference)),
                "close_under_tolerance": close,
            }
        )
    result = {
        "schema": "twisted-yetter.akbulut-figure1-e1-su2-2-sampled-twists-comparison.v1",
        "status": "pass" if mismatch_count == 0 else "mismatch",
        "category_id": "SU(2)_2",
        "source_input": str(base.INPUT.relative_to(REPO_ROOT)),
        "claim_level": "sampled mod-2 homological twist sectors for Akbulut Figure 1 versus standard CP2#9CPbar",
        "akbulut_complexity": {
            "n_strands": n_strands,
            "braid_word_length": len(braid_word),
            "component_order_in_braid": source_order_in_braid,
            "framings_in_braid_order": framings_in_braid_order,
            "fixed_sector_count": len(akbulut_cache),
        },
        "row_count": len(rows),
        "mismatch_count": mismatch_count,
        "max_abs_difference": str(max_abs_difference),
        "rows": rows,
        "elapsed_seconds": time.time() - started,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": result["status"],
                "artifact": str(OUTPUT.relative_to(REPO_ROOT)),
                "row_count": result["row_count"],
                "mismatch_count": result["mismatch_count"],
                "max_abs_difference": result["max_abs_difference"],
                "elapsed_seconds": result["elapsed_seconds"],
            },
            indent=2,
            sort_keys=True,
        ),
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
