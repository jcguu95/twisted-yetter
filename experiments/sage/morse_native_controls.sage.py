"""Cross-check the native Morse evaluator against calibrated category data."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import importlib.util
import json
from pathlib import Path
import sys

from experiments.sage.morse_category_adapters import LoadedFRMorseAdapter, SU2KMorseAdapter
from experiments.sage.morse_fusion_evaluator import MorseEvaluator, analyze_topology, canonical_component_name


REPO_ROOT = Path(__file__).resolve().parents[2]
SU2_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
SU3_PATH = REPO_ROOT / "experiments" / "sage" / "su3_2_anyonwiki_fr_braid_evaluator.py"
GENERIC_FR_PATH = REPO_ROOT / "experiments" / "sage" / "yasui_figure3_a3_da4_untwisted_chunked.sage.py"
DIC3_PAYLOAD = REPO_ROOT / "experiments" / "results" / "mtc-candidates" / "drinfeld-double-dic12-omega0-mtc-fr-data-v1.json"


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def unknot_forms(kinks: int = 0):
    forms = [{"kind": "cup", "piece": "A", "at": "far-left"}]
    if kinks:
        forms.append({"kind": "kink", "strand": "A.left", "sign": "+" if kinks > 0 else "-", "times": abs(kinks)})
    forms.append({"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]})
    return forms


def reidemeister_two_forms():
    return [
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cup", "piece": "B", "at": "far-right"},
        {"kind": "cross", "over": "A.right", "under": "B.left"},
        {"kind": "cross", "over": "A.right", "under": "B.left"},
        {"kind": "cap", "piece": "B", "strands": ["B.left", "B.right"]},
        {"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]},
    ]


def two_cup_unknot_forms():
    return [
        {"kind": "cup", "piece": "A1", "at": "far-left"},
        {"kind": "cup", "piece": "A2", "between": ["A1.left", "A1.right"]},
        {"kind": "cap", "strands": ["A2.right", "A1.right"]},
        {"kind": "cap", "strands": ["A1.left", "A2.left"]},
    ]


def block_reidemeister_two_forms():
    return [
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cup", "piece": "B", "at": "far-right"},
        {"kind": "cup", "piece": "C", "at": "far-right"},
        {"kind": "cross", "over": "A.right", "under": "B.left"},
        {"kind": "cross", "over": "A.right", "under": "B.right"},
        {"kind": "cross", "over": "A.right", "under": "B.right"},
        {"kind": "cross", "over": "A.right", "under": "B.left"},
        {"kind": "cap", "piece": "C", "strands": ["C.left", "C.right"]},
        {"kind": "cap", "piece": "B", "strands": ["B.left", "B.right"]},
        {"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]},
    ]


def braid_component_data(n_strands, braid_word):
    positions = list(range(n_strands))
    self_writhe_crossings = []
    for generator in braid_word:
        index = abs(generator) - 1
        self_writhe_crossings.append((positions[index], positions[index + 1], 1 if generator > 0 else -1))
        positions[index], positions[index + 1] = positions[index + 1], positions[index]
    successor = [None] * n_strands
    for top_position, original in enumerate(positions):
        successor[original] = top_position
    cycles = []
    seen = set()
    for start in range(n_strands):
        if start in seen:
            continue
        cycle = []
        current = start
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = successor[current]
        cycles.append(tuple(sorted(cycle)))
    cycles = tuple(sorted(cycles, key=lambda cycle: cycle[0]))
    strand_to_component = {}
    for component, cycle in enumerate(cycles):
        for strand in cycle:
            strand_to_component[strand] = component
    writhe = [0] * len(cycles)
    for left, right, sign in self_writhe_crossings:
        if strand_to_component[left] == strand_to_component[right]:
            writhe[strand_to_component[left]] += sign
    return cycles, strand_to_component, tuple(writhe)


def braid_closure_morse_forms(n_strands, braid_word, framings):
    """Present a braid quantum trace as nested cups, braid, and middle caps."""
    forms = []
    order = []
    for strand in range(n_strands):
        piece = f"S{strand}"
        if strand == 0:
            form = {"kind": "cup", "piece": piece, "at": "far-left"}
            gap = 0
        else:
            previous = f"S{strand - 1}"
            form = {"kind": "cup", "piece": piece, "between": [f"{previous}.left", f"{previous}.right"]}
            gap = order.index(f"{previous}.left") + 1
        forms.append(form)
        order[gap:gap] = [f"{piece}.left", f"{piece}.right"]
    cycles, strand_to_component, writhe = braid_component_data(n_strands, braid_word)
    for generator in braid_word:
        index = abs(generator) - 1
        left, right = order[index], order[index + 1]
        over, under = (left, right) if generator > 0 else (right, left)
        forms.append({"kind": "cross", "over": over, "under": under})
        order[index], order[index + 1] = order[index + 1], order[index]
    for component, (framing, blackboard) in enumerate(zip(framings, writhe, strict=True)):
        correction = int(framing) - int(blackboard)
        if correction:
            strand = next(
                active
                for active in order[:n_strands]
                if strand_to_component[int(active[1:].split(".", 1)[0])] == component
            )
            forms.append({
                "kind": "kink",
                "strand": strand,
                "sign": "+" if correction > 0 else "-",
                "times": abs(correction),
            })
    while order:
        left, right = order[n_strands - 1], order[n_strands]
        forms.append({"kind": "cap", "strands": [left, right]})
        order = [strand for strand in order if strand not in {left, right}]
        n_strands -= 1
    topology = analyze_topology(forms)
    component_index_by_name = {}
    for name in topology.component_order:
        pieces = name.split("+")
        source_strand = int(pieces[0][1:])
        component_index_by_name[name] = strand_to_component[source_strand]
    return forms, component_index_by_name


def run_su2_braid_bridge_controls(su2):
    rows = []
    cases = (
        ("positive_hopf", 2, (1, 1), (0, 0)),
        ("positive_trefoil_blackboard", 2, (1, 1, 1), (3,)),
        ("three_strand_mixed", 3, (1, -2, 1, 2, -1, 2), (0, 0, 0)),
    )
    for level in (2, 3, 4, 5):
        backend = su2.SU2KBraidEvaluator(level, exact=False)
        category = SU2KMorseAdapter(backend)
        native = MorseEvaluator(category)
        for case_name, n_strands, word, framings in cases:
            components, _, _ = braid_component_data(n_strands, word)
            forms, component_index = braid_closure_morse_forms(n_strands, word, framings)
            sample_labels = tuple(
                category.labels[min(index + 1, len(category.labels) - 1)]
                for index in range(len(components))
            )
            native_labels = {
                name: sample_labels[component]
                for name, component in component_index.items()
            }
            observed, stats = native.fixed_label_value(forms, native_labels)
            expected = complex(backend.fixed_label_value(n_strands, word, sample_labels, framings))
            rows.append({
                "category": f"SU(2)_{level}",
                "control": f"braid_bridge_{case_name}",
                "labels": list(sample_labels),
                "observed": [observed.real, observed.imag],
                "expected": [expected.real, expected.imag],
                "pass": close(observed, expected, 1e-8),
                "stats": stats,
            })
    return rows


def close(left, right, tolerance=1e-9):
    return abs(complex(left) - complex(right)) <= tolerance


def run_su2_controls():
    su2 = load_module(SU2_PATH, "su2k_for_native_morse_controls")
    rows = []
    for level in (2, 3, 4, 5):
        backend = su2.SU2KBraidEvaluator(level, exact=False)
        category = SU2KMorseAdapter(backend)
        evaluator = MorseEvaluator(category)
        for label in category.labels:
            value, stats = evaluator.fixed_label_value(unknot_forms(), {"A": label})
            expected = complex(backend.dimension(label))
            rows.append({
                "category": f"SU(2)_{level}",
                "control": "zero_framed_unknot",
                "labels": [label],
                "observed": [value.real, value.imag],
                "expected": [expected.real, expected.imag],
                "pass": close(value, expected),
                "stats": stats,
            })
            kinked, kink_stats = evaluator.fixed_label_value(unknot_forms(1), {"A": label})
            kink_expected = expected * complex(backend.twist(label))
            rows.append({
                "category": f"SU(2)_{level}",
                "control": "positive_framed_unknot",
                "labels": [label],
                "observed": [kinked.real, kinked.imag],
                "expected": [kink_expected.real, kink_expected.imag],
                "pass": close(kinked, kink_expected),
                "stats": kink_stats,
            })
            snake, snake_stats = evaluator.fixed_label_value(
                two_cup_unknot_forms(), {"A": label}
            )
            rows.append({
                "category": f"SU(2)_{level}",
                "control": "two_cup_snake_unknot",
                "labels": [label],
                "observed": [snake.real, snake.imag],
                "expected": [expected.real, expected.imag],
                "pass": close(snake, expected),
                "reverse_bend": [
                    complex(category.reverse_bend(label)).real,
                    complex(category.reverse_bend(label)).imag,
                ],
                "stats": snake_stats,
            })
        labels = tuple(label for label in category.labels if label != category.unit)[:2]
        for left in labels:
            for right in labels:
                value, stats = evaluator.fixed_label_value(
                    reidemeister_two_forms(), {"A": left, "B": right}
                )
                expected = complex(backend.dimension(left) * backend.dimension(right))
                rows.append({
                    "category": f"SU(2)_{level}",
                    "control": "reidemeister_two_split_unlink",
                    "labels": [left, right],
                    "observed": [value.real, value.imag],
                    "expected": [expected.real, expected.imag],
                    "pass": close(value, expected),
                    "stats": stats,
                })
        selected = labels[0]
        value, stats = evaluator.fixed_label_value(
            block_reidemeister_two_forms(),
            {"A": selected, "B": selected, "C": category.unit},
        )
        expected = complex(backend.dimension(selected) ** 2)
        rows.append({
            "category": f"SU(2)_{level}",
            "control": "block_reidemeister_two_split_unlink",
            "labels": [selected, selected, category.unit],
            "observed": [value.real, value.imag],
            "expected": [expected.real, expected.imag],
            "pass": close(value, expected) and stats["block_r"] == 2,
            "stats": stats,
        })
    return rows


def run_loaded_fr_controls():
    rows = []
    su3 = load_module(SU3_PATH, "su3_for_native_morse_controls")
    su3_backend = su3.SU32AnyonWikiFRBraidEvaluator()
    categories = [
        (
            "SU(3)_2",
            LoadedFRMorseAdapter(
                su3_backend,
                character=su3.character_value,
                adapter_name="SU(3)_2 AnyonWiki FR",
            ),
        )
    ]
    generic = load_module(GENERIC_FR_PATH, "generic_fr_for_native_morse_controls")
    dic3_backend = generic.DA4FRBraidEvaluator(json.loads(DIC3_PAYLOAD.read_text()))
    categories.append(
        (
            "D(Dic_3)=D(Dic_12-order-12)",
            LoadedFRMorseAdapter(dic3_backend, adapter_name="D(Dic_3) numeric FR"),
        )
    )
    for name, category in categories:
        evaluator = MorseEvaluator(category)
        for label in category.labels:
            value, stats = evaluator.fixed_label_value(unknot_forms(), {"A": label})
            expected = complex(category.dimension(label))
            rows.append({
                "category": name,
                "control": "zero_framed_unknot",
                "labels": [label],
                "observed": [value.real, value.imag],
                "expected": [expected.real, expected.imag],
                "pass": close(value, expected, 1e-8),
                "stats": stats,
            })
            snake, snake_stats = evaluator.fixed_label_value(
                two_cup_unknot_forms(), {"A": label}
            )
            rows.append({
                "category": name,
                "control": "two_cup_snake_unknot",
                "labels": [label],
                "observed": [snake.real, snake.imag],
                "expected": [expected.real, expected.imag],
                "pass": close(snake, expected, 1e-7),
                "reverse_bend": [
                    complex(category.reverse_bend(label)).real,
                    complex(category.reverse_bend(label)).imag,
                ],
                "stats": snake_stats,
            })
        nonunits = [label for label in category.labels if label != category.unit]
        multiplicity_pair = next(
            (
                (left, right)
                for left in nonunits
                for right in nonunits
                if max((mult for _, mult in category.fusion_outputs(left, right)), default=0) > 1
            ),
            (nonunits[0], nonunits[min(1, len(nonunits) - 1)]),
        )
        left, right = multiplicity_pair
        value, stats = evaluator.fixed_label_value(
            reidemeister_two_forms(), {"A": left, "B": right}
        )
        expected = complex(category.dimension(left) * category.dimension(right))
        rows.append({
            "category": name,
            "control": "multiplicity_aware_reidemeister_two",
            "labels": [left, right],
            "observed": [value.real, value.imag],
            "expected": [expected.real, expected.imag],
            "pass": close(value, expected, 1e-7),
            "stats": stats,
            "max_selected_fusion_multiplicity": max(
                mult for _, mult in category.fusion_outputs(left, right)
            ),
        })
        largest_key, largest_block = max(
            category.backend.f_blocks.items(),
            key=lambda item: item[1]["matrix"].shape[0] * item[1]["matrix"].shape[1],
        )
        external_labels = largest_key[:3]
        word = (1, -2, 1, 2, -1, 2)
        framings = (0, 0, 0)
        forms, component_index = braid_closure_morse_forms(3, word, framings)
        native_labels = {
            component_name: external_labels[component]
            for component_name, component in component_index.items()
        }
        observed, stats = evaluator.fixed_label_value(forms, native_labels)
        expected_result = category.backend.fixed_label_value(3, word, external_labels, framings)
        expected = complex(expected_result[0] if isinstance(expected_result, tuple) else expected_result)
        rows.append({
            "category": name,
            "control": "largest_f_block_three_strand_braid_bridge",
            "labels": list(external_labels),
            "largest_f_block_key": list(largest_key),
            "largest_f_block_shape": list(largest_block["matrix"].shape),
            "observed": [observed.real, observed.imag],
            "expected": [expected.real, expected.imag],
            "pass": close(observed, expected, 1e-7),
            "stats": stats,
        })
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    su2 = load_module(SU2_PATH, "su2k_for_native_morse_bridge_controls")
    rows = run_su2_controls() + run_loaded_fr_controls() + run_su2_braid_bridge_controls(su2)
    payload = {
        "schema": "twisted-yetter.native-morse-evaluator-controls.v1",
        "status": "pass" if all(row["pass"] for row in rows) else "needs-review",
        "mathematical_status": "NUMERICAL_LOCAL_AND_BRAID_BRIDGE_CALIBRATION",
        "generator_script": "experiments/sage/morse_native_controls.sage.py",
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python experiments/sage/morse_native_controls.sage.py --output experiments/results/gompf-stipsicz/native-morse-evaluator-category-controls-v1.json",
        "utc_finish": datetime.now(UTC).isoformat(),
        "rows": rows,
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(args.output.resolve())
    else:
        print(rendered, end="")
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
