"""Chunkable native Morse RT/Kirby-color evaluator.

The input is expanded Morse fundamental-form JSON, not PD/Gauss/braid data.
Supported category adapters are SU(2)_k, SU(3)_2, and the order-12 dicyclic
double recorded in this repository as D(Dic_12), also denoted D(Dic_3).
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import UTC, datetime
import importlib.util
from itertools import islice, product
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

from sage.env import SAGE_VERSION

from experiments.sage.morse_category_adapters import LoadedFRMorseAdapter, SU2KMorseAdapter
from experiments.sage.morse_fusion_evaluator import MorseEvaluator, analyze_topology


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


def build_category(category_name: str, level: int | None):
    if category_name == "su2":
        if level not in {2, 3, 4, 5}:
            raise ValueError("--category su2 currently requires --level 2, 3, 4, or 5")
        module = load_module(SU2_PATH, f"su2k_native_morse_level_{level}")
        backend = module.SU2KBraidEvaluator(level, exact=False)
        return SU2KMorseAdapter(backend), f"SU(2)_{level}"
    if category_name == "su3-2":
        module = load_module(SU3_PATH, "su3_2_native_morse")
        backend = module.SU32AnyonWikiFRBraidEvaluator()
        return (
            LoadedFRMorseAdapter(
                backend,
                character=module.character_value,
                adapter_name="SU(3)_2 AnyonWiki FR",
            ),
            "SU(3)_2",
        )
    if category_name == "dic3":
        module = load_module(GENERIC_FR_PATH, "dic3_native_morse_generic_fr")
        payload = json.loads(DIC3_PAYLOAD.read_text())
        backend = module.DA4FRBraidEvaluator(payload)
        return (
            LoadedFRMorseAdapter(backend, adapter_name="D(Dic_3) numeric FR"),
            "D(Dic_3)=D(Dic_12-order-12)",
        )
    raise ValueError(f"unknown category: {category_name!r}")


def command(argv):
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def complex_json(value):
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def parse_assignment(raw: str | None, components, default=0):
    if raw is None:
        return {component: default for component in components}
    path = Path(raw)
    payload = json.loads(path.read_text()) if path.exists() else json.loads(raw)
    if isinstance(payload, list):
        if len(payload) != len(components):
            raise ValueError("assignment list length does not match component count")
        return dict(zip(components, payload, strict=True))
    return payload


def labels_at_index(labels, component_count, sector_index):
    labels = tuple(labels)
    base = len(labels)
    if not (0 <= sector_index < base**component_count):
        raise ValueError(f"sector index out of range: {sector_index}")
    digits = [0] * component_count
    value = int(sector_index)
    for position in range(component_count - 1, -1, -1):
        value, digit = divmod(value, base)
        digits[position] = digit
    return tuple(labels[digit] for digit in digits)


def read_sector_indices(path):
    indices = []
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        payload = json.loads(line)
        indices.append(int(payload["sector_index"] if isinstance(payload, dict) else payload))
    if len(indices) != len(set(indices)):
        raise ValueError("sector index file contains duplicates")
    return tuple(indices)


def sector_rows(category, components, start, count, index_file=None):
    if index_file is not None:
        indices = read_sector_indices(index_file)
        return (
            (index, labels_at_index(category.labels, len(components), index))
            for index in indices
        ), indices
    iterator = product(category.labels, repeat=len(components))
    rows = enumerate(islice(iterator, start, None if count is None else start + count), start=start)
    return rows, None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--category", choices=("su2", "su3-2", "dic3"), required=True)
    parser.add_argument("--level", type=int)
    parser.add_argument("--mode", choices=("fixed", "omega", "chunk"), default="fixed")
    parser.add_argument("--labels", help="JSON object/list or path for fixed component labels")
    parser.add_argument("--characters", help="JSON object/list or path; default is untwisted zero")
    parser.add_argument("--sector-start", type=int, default=0)
    parser.add_argument("--sector-count", type=int)
    parser.add_argument("--sector-index-file", type=Path)
    parser.add_argument(
        "--planner-mode", choices=("hybrid", "sequential"), default="hybrid"
    )
    parser.add_argument(
        "--reverse-orientation", action="append", default=[], metavar="COMPONENT"
    )
    parser.add_argument(
        "--group-components",
        help="comma-separated component names for grouped partial sums",
    )
    parser.add_argument(
        "--record-sector-values",
        action="store_true",
        help="record each fixed-label raw and weighted value in chunk output",
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    started = datetime.now(UTC)
    wall_start = time.perf_counter()
    input_payload = json.loads(args.input.read_text())
    forms = tuple(input_payload["forms"])
    topology = analyze_topology(forms)
    category, display_name = build_category(args.category, args.level)
    evaluator = MorseEvaluator(
        category,
        planner_mode=args.planner_mode,
        reversed_orientation_components=args.reverse_orientation,
    )

    payload = {
        "schema": "twisted-yetter.native-morse-rt-evaluation.v1",
        "status": "running",
        "mathematical_status": "NUMERICAL_EVALUATION_OF_INPUT_WITH_INPUT_CAVEATS_INHERITED",
        "generator_script": "experiments/sage/morse_native_evaluate.sage.py",
        "argv": sys.argv,
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python " + " ".join(sys.argv),
        "input": str(args.input.resolve().relative_to(REPO_ROOT)),
        "input_status": input_payload.get("status"),
        "category": display_name,
        "component_order": list(topology.component_order),
        "mode": args.mode,
        "utc_start": started.isoformat(),
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "dirty": bool(command(["git", "status", "--short"])),
        },
        "tool_versions": {
            "sage": SAGE_VERSION,
            "python": sys.version,
            "platform": platform.platform(),
        },
    }

    if args.mode == "fixed":
        labels = parse_assignment(args.labels, topology.component_order)
        value, stats = evaluator.fixed_label_value(forms, labels)
        payload.update({"fixed_labels": labels, "value": complex_json(value), "evaluation_stats": stats})
    else:
        group_components = tuple(
            component.strip()
            for component in (args.group_components or "").split(",")
            if component.strip()
        )
        unknown_group_components = set(group_components) - set(topology.component_order)
        if unknown_group_components:
            raise ValueError(
                f"unknown group components: {sorted(unknown_group_components)!r}"
            )
        grouped_sums = defaultdict(complex)
        grouped_counts = defaultdict(int)
        sector_value_rows = []
        characters = parse_assignment(args.characters, topology.component_order)
        start = args.sector_start if args.mode == "chunk" else 0
        count = args.sector_count if args.mode == "chunk" else None
        total = 0.0 + 0.0j
        evaluated = 0
        max_support = 0
        planner_summary = None
        rows, explicit_indices = sector_rows(
            category, topology.component_order, start, count, args.sector_index_file
        )
        evaluated_indices = []
        for sector_index, labels_tuple in rows:
            labels = dict(zip(topology.component_order, labels_tuple, strict=True))
            coefficient = 1.0 + 0.0j
            for component, label in labels.items():
                coefficient *= complex(category.dimension(label))
                coefficient *= complex(category.character(characters[component], label))
            value, stats = evaluator.fixed_label_value(forms, labels)
            total += coefficient * value
            if args.record_sector_values:
                sector_value_rows.append(
                    {
                        "sector_index": sector_index,
                        "labels": list(labels_tuple),
                        "coefficient": complex_json(coefficient),
                        "fixed_value": complex_json(value),
                        "weighted_value": complex_json(coefficient * value),
                    }
                )
            if group_components:
                group_key = tuple(labels[component] for component in group_components)
                grouped_sums[group_key] += coefficient * value
                grouped_counts[group_key] += 1
            evaluated += 1
            evaluated_indices.append(sector_index)
            max_support = max(max_support, stats["max_state_support"])
            if planner_summary is None:
                planner_summary = {
                    "f_rotations": stats["f_rotations"],
                    "leaf_r": stats["leaf_r"],
                    "block_r": stats["block_r"],
                    "max_active_strands": stats["max_active_strands"],
                    "planner_weights": stats["planner_weights"],
                    "plans": stats["plans"],
                }
        payload.update(
            {
                "character_assignments": characters,
                "sector_range": None if explicit_indices is not None else {"start": start, "count": evaluated},
                "sector_indices": evaluated_indices if explicit_indices is not None else None,
                "sector_index_file": str(args.sector_index_file) if args.sector_index_file else None,
                "weighted_partial_sum": complex_json(total),
                "max_state_support": max_support,
                "planner_summary": planner_summary,
                "group_components": list(group_components),
                "grouped_weighted_partial_sums": [
                    {
                        "labels": list(key),
                        "sector_count": grouped_counts[key],
                        "weighted_partial_sum": complex_json(grouped_sums[key]),
                    }
                    for key in sorted(grouped_sums)
                ],
                "sector_values": sector_value_rows,
            }
        )

    finished = datetime.now(UTC)
    payload.update(
        {
            "status": "pass",
            "utc_finish": finished.isoformat(),
            "elapsed_seconds": time.perf_counter() - wall_start,
        }
    )
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(args.output.resolve())
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
