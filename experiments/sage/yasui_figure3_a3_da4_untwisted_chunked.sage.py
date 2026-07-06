"""Chunked Yasui Figure 3 (a=3) D(A4) untwisted timing run.

Run the first timing probe from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py --start 0 --count 20

This is a deliberately narrow numeric FR-symbol braid-closure evaluator for
fixed-label sectors.  It uses the established numeric untwisted D(A4) F/R data,
the existing Yasui a=3 braid construction, and the untwisted Kirby-color
coefficient prod_i d_i.  It is a timing/profiling artifact, not a theorem-level
link invariant certificate.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import UTC, datetime
import fcntl
import hashlib
import importlib.util
from itertools import islice, product
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import time

import numpy as np
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
A3_PATH = REPO_ROOT / "experiments" / "sage" / "yasui_figure3_a3_su2_2_untwisted_comparison.sage.py"
MTC_PATH = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "drinfeld-double-a4-omega0-mtc-fr-data-v1.json"
)
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "yasui"
CHUNK_DIR = RESULT_DIR / "figure3-a3-da4-omega0-untwisted-chunks-v1"
PROFILE_PATH = RESULT_DIR / "figure3-a3-da4-omega0-untwisted-profile-v1.json"
POOL_STATE_PATH = RESULT_DIR / "figure3-a3-da4-omega0-untwisted-singleton-pool-state-v1.json"


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def command(argv: list[str]) -> str:
    return subprocess.check_output(argv, cwd=REPO_ROOT, text=True).strip()


def optional_command(argv: list[str]) -> str | None:
    try:
        return command(argv)
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def read_json(path: Path):
    return json.loads(path.read_text())


def repo_metadata() -> dict:
    git_commit = optional_command(["git", "rev-parse", "HEAD"])
    status_short = optional_command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": git_commit,
        "dirty": (bool(status_short) if status_short is not None else None),
        "status_short": status_short,
        "metadata_status": "git-available" if git_commit is not None and status_short is not None else "git-unavailable",
    }


def tool_versions() -> dict:
    return {
        "sage": SAGE_VERSION,
        "python": sys.version,
        "numpy": np.__version__,
    }


def complex_from_json(value) -> complex:
    return complex(float(value["real"]), float(value["imag"]))


def complex_json(value: complex) -> dict[str, str]:
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def sparse_matrix(matrix_payload) -> np.ndarray:
    matrix = np.zeros((int(matrix_payload["rows"]), int(matrix_payload["columns"])), dtype=np.complex128)
    for entry in matrix_payload["entries"]:
        matrix[int(entry["row"]), int(entry["column"])] = complex_from_json(entry["value"])
    return matrix


class DA4FRBraidEvaluator:
    def __init__(self, payload: dict):
        self.payload = payload
        self.labels = tuple(payload["simple_labels"])
        self.unit = self.labels[0]
        self.label_index = {label: index for index, label in enumerate(self.labels)}
        self.dimensions = {
            item["label"]: float(item["quantum_dimension"])
            for item in payload["simple_objects"]
        }
        self.twists = {
            item["label"]: self.twist_value(item["twist"])
            for item in payload["simple_objects"]
        }
        self.fusion = self.fusion_dict(payload["fusion_rules"])
        self.fusion_outputs_cache: dict[tuple[str, str], tuple[tuple[str, int], ...]] = {}
        self.f_blocks = {}
        self.f_inv_blocks = {}
        self.r_positive = {}
        self.r_negative = {}
        self.paths_cache = {}
        self.crossing_cache = {}
        self._load_fr(payload["fr_symbols"])

    @staticmethod
    def twist_value(twist: dict) -> complex:
        root_order = int(twist["root_order"])
        exponent = int(twist["exponent"])
        return complex(np.exp(2j * np.pi * exponent / root_order))

    @staticmethod
    def fusion_dict(rules: list[dict]) -> dict[tuple[str, str, str], int]:
        fusion = {}
        for rule in rules:
            outputs = {item["target"]: int(item["multiplicity"]) for item in rule["outputs"]}
            for target in outputs:
                fusion[(rule["left"], rule["right"], target)] = outputs[target]
        return fusion

    def _load_fr(self, fr: dict) -> None:
        for block in fr["f_blocks"]:
            key = (block["a"], block["b"], block["c"], block["d"])
            left_basis = tuple(tuple(item) for item in block["left_basis_labels"])
            right_basis = tuple(tuple(item) for item in block["right_basis_labels"])
            matrix = sparse_matrix(block["right_to_left"])
            self.f_blocks[key] = {
                "matrix": matrix,
                "left_index": {basis: index for index, basis in enumerate(left_basis)},
                "right_index": {basis: index for index, basis in enumerate(right_basis)},
                "left_basis": left_basis,
                "right_basis": right_basis,
            }
            self.f_inv_blocks[key] = np.linalg.inv(matrix)

        for block in fr["r_blocks"]:
            a = block["a"]
            b = block["b"]
            c = block["c"]
            matrix = sparse_matrix(block["ba_to_ab"])
            self.r_positive[(b, a, c)] = matrix
            self.r_negative[(a, b, c)] = np.linalg.inv(matrix)

    def zero(self) -> complex:
        return 0.0 + 0.0j

    def one(self) -> complex:
        return 1.0 + 0.0j

    def dimension(self, label: str) -> float:
        return self.dimensions[label]

    def twist(self, label: str) -> complex:
        return self.twists[label]

    def fusion_outputs(self, left: str, right: str) -> tuple[tuple[str, int], ...]:
        key = (left, right)
        if key not in self.fusion_outputs_cache:
            outputs = []
            for target in self.labels:
                multiplicity = self.fusion.get((left, right, target), 0)
                if multiplicity:
                    outputs.append((target, multiplicity))
            self.fusion_outputs_cache[key] = tuple(outputs)
        return self.fusion_outputs_cache[key]

    def component_data(self, n_strands: int, braid_word: tuple[int, ...]):
        positions = list(range(n_strands))
        for generator in braid_word:
            index = abs(int(generator)) - 1
            positions[index], positions[index + 1] = positions[index + 1], positions[index]

        next_strand = [None] * n_strands
        for top_position, original_strand in enumerate(positions):
            next_strand[original_strand] = top_position

        seen = set()
        cycles = []
        for start in range(n_strands):
            if start in seen:
                continue
            cycle = []
            strand = start
            while strand not in seen:
                seen.add(strand)
                cycle.append(strand)
                strand = next_strand[strand]
            cycles.append(tuple(sorted(cycle)))

        cycles = tuple(sorted(cycles, key=lambda cycle: cycle[0]))
        strand_to_component = [None] * n_strands
        for component_index, cycle in enumerate(cycles):
            for strand in cycle:
                strand_to_component[strand] = component_index
        return cycles, tuple(strand_to_component)

    def blackboard_self_writhe(self, n_strands: int, braid_word: tuple[int, ...]) -> tuple[int, ...]:
        components, strand_to_component = self.component_data(n_strands, braid_word)
        writhe = [0 for _ in components]
        positions = list(range(n_strands))
        for generator in braid_word:
            sign = 1 if generator > 0 else -1
            index = abs(int(generator)) - 1
            left = positions[index]
            right = positions[index + 1]
            left_component = strand_to_component[left]
            right_component = strand_to_component[right]
            if left_component == right_component:
                writhe[left_component] += sign
            positions[index], positions[index + 1] = positions[index + 1], positions[index]
        return tuple(writhe)

    @staticmethod
    def selected_subbraid_word(n_strands: int, braid_word: tuple[int, ...], selected_strands: set[int]):
        positions = list(range(n_strands))
        subword = []
        for generator in braid_word:
            sign = 1 if generator > 0 else -1
            index = abs(int(generator)) - 1
            left = positions[index]
            right = positions[index + 1]
            if left in selected_strands and right in selected_strands:
                selected_positions_before = [
                    position for position, strand in enumerate(positions) if strand in selected_strands
                ]
                sub_index = selected_positions_before.index(index) + 1
                subword.append(sign * sub_index)
            positions[index], positions[index + 1] = positions[index + 1], positions[index]
        return tuple(subword), len(selected_strands)

    def fixed_label_value(
        self,
        n_strands: int,
        braid_word: tuple[int, ...],
        component_labels: tuple[str, ...],
        framings: tuple[int, ...],
    ) -> tuple[complex, dict]:
        components, strand_to_component = self.component_data(n_strands, braid_word)
        if len(component_labels) != len(components):
            raise ValueError("component label count does not match braid closure")
        if len(framings) != len(components):
            raise ValueError("framing count does not match braid closure")

        if any(label == self.unit for label in component_labels):
            nonunit_components = {
                index for index, label in enumerate(component_labels) if label != self.unit
            }
            if not nonunit_components:
                return self.one(), {
                    "unit_pruned": True,
                    "selected_component_count": 0,
                    "selected_strand_count": 0,
                    "subbraid_word_length": 0,
                }
            selected_strands = {
                strand
                for strand, component_index in enumerate(strand_to_component)
                if component_index in nonunit_components
            }
            selected_strand_list = tuple(sorted(selected_strands))
            subword, selected_strand_count = self.selected_subbraid_word(
                n_strands,
                braid_word,
                selected_strands,
            )
            sub_components, _ = self.component_data(selected_strand_count, subword)
            sub_original_components = []
            for sub_component in sub_components:
                original_components = {
                    strand_to_component[selected_strand_list[sub_strand]]
                    for sub_strand in sub_component
                }
                if len(original_components) != 1:
                    raise ValueError(f"selected subbraid mixes components: {sorted(original_components)}")
                sub_original_components.append(original_components.pop())
            sub_labels = tuple(component_labels[index] for index in sub_original_components)
            sub_framings = tuple(framings[index] for index in sub_original_components)
            value, stats = self.fixed_label_value(selected_strand_count, subword, sub_labels, sub_framings)
            stats = dict(stats)
            stats.update(
                {
                    "unit_pruned": True,
                    "selected_component_count": len(nonunit_components),
                    "selected_strand_count": selected_strand_count,
                    "subbraid_word_length": len(subword),
                }
            )
            return value, stats

        strand_labels = tuple(component_labels[strand_to_component[strand]] for strand in range(n_strands))
        trace_value, trace_stats = self.braid_quantum_trace(strand_labels, braid_word)
        framing_factor = self.one()
        for label, framing, writhe in zip(component_labels, framings, self.blackboard_self_writhe(n_strands, braid_word), strict=True):
            framing_factor *= self.twist(label) ** int(framing - writhe)
        stats = dict(trace_stats)
        stats.update(
            {
                "unit_pruned": False,
                "selected_component_count": len(component_labels),
                "selected_strand_count": n_strands,
                "subbraid_word_length": len(braid_word),
            }
        )
        return trace_value * framing_factor, stats

    def braid_quantum_trace(self, strand_labels: tuple[str, ...], braid_word: tuple[int, ...]):
        current_sequence_base = tuple(strand_labels)
        total = self.zero()
        total_stats = {
            "total_charge_count": 0,
            "max_basis_size": 0,
            "max_state_size": 0,
            "basis_sizes_by_total": {},
        }
        for total_charge in self.labels:
            current_sequence = current_sequence_base
            initial_basis = self.paths(current_sequence, total_charge)
            if not initial_basis:
                continue
            total_stats["total_charge_count"] += 1
            total_stats["max_basis_size"] = max(total_stats["max_basis_size"], len(initial_basis))
            total_stats["basis_sizes_by_total"][total_charge] = len(initial_basis)
            state = {(path, path): self.one() for path in initial_basis}
            current_basis = initial_basis
            for generator in braid_word:
                crossing, next_basis = self.crossing_entries(
                    current_sequence,
                    total_charge,
                    abs(int(generator)) - 1,
                    int(generator) > 0,
                )
                state = self.compose_sparse(crossing, state)
                total_stats["max_state_size"] = max(total_stats["max_state_size"], len(state))
                current_sequence = self.swapped_sequence(current_sequence, abs(int(generator)) - 1)
                current_basis = next_basis
            if current_sequence != current_sequence_base:
                raise ValueError("braid closure colors are not component-constant")
            if current_basis != initial_basis:
                raise ValueError("internal basis ordering changed unexpectedly")
            trace = sum(
                coefficient
                for (target_path, source_path), coefficient in state.items()
                if target_path == source_path
            )
            total += self.dimension(total_charge) * trace
        return total, total_stats

    @staticmethod
    def compose_sparse(left, right):
        by_source = defaultdict(list)
        for (target_path, source_path), coefficient in left.items():
            by_source[source_path].append((target_path, coefficient))
        output = {}
        for (middle_path, original_path), right_coefficient in right.items():
            for target_path, left_coefficient in by_source.get(middle_path, ()):
                key = (target_path, original_path)
                output[key] = output.get(key, 0.0 + 0.0j) + left_coefficient * right_coefficient
        return {key: value for key, value in output.items() if abs(value) > 1e-14}

    @staticmethod
    def swapped_sequence(sequence: tuple[str, ...], generator_index: int) -> tuple[str, ...]:
        items = list(sequence)
        items[generator_index], items[generator_index + 1] = items[generator_index + 1], items[generator_index]
        return tuple(items)

    def paths(self, sequence: tuple[str, ...], total_charge: str):
        key = (tuple(sequence), total_charge)
        if key in self.paths_cache:
            return self.paths_cache[key]
        sequence = tuple(sequence)
        if len(sequence) == 0:
            paths = ((),) if total_charge == self.unit else ()
        elif len(sequence) == 1:
            paths = ((),) if sequence[0] == total_charge else ()
        else:
            output = []

            def extend(index: int, previous: str, path: list[tuple[str, int]]):
                if index == len(sequence):
                    if previous == total_charge:
                        output.append(tuple(path))
                    return
                for next_label, multiplicity in self.fusion_outputs(previous, sequence[index]):
                    for multiplicity_index in range(multiplicity):
                        extend(index + 1, next_label, path + [(next_label, multiplicity_index)])

            for first, multiplicity in self.fusion_outputs(sequence[0], sequence[1]):
                for multiplicity_index in range(multiplicity):
                    extend(2, first, [(first, multiplicity_index)])
            paths = tuple(output)
        self.paths_cache[key] = paths
        return paths

    def crossing_entries(
        self,
        sequence: tuple[str, ...],
        total_charge: str,
        generator_index: int,
        positive: bool,
    ):
        key = (tuple(sequence), total_charge, int(generator_index), bool(positive))
        if key in self.crossing_cache:
            return self.crossing_cache[key]
        source_basis = self.paths(sequence, total_charge)
        target_sequence = self.swapped_sequence(sequence, generator_index)
        target_basis = self.paths(target_sequence, total_charge)
        entries = {}

        x = sequence[generator_index]
        y = sequence[generator_index + 1]
        if generator_index == 0:
            matrix_for = self.r_positive if positive else self.r_negative
            for path in source_basis:
                channel, source_mult = path[0]
                matrix = matrix_for[(x, y, channel)]
                for target_mult in range(matrix.shape[0]):
                    coefficient = matrix[target_mult, source_mult]
                    if abs(coefficient) <= 1e-14:
                        continue
                    target_path = list(path)
                    target_path[0] = (channel, target_mult)
                    entries[(tuple(target_path), path)] = entries.get((tuple(target_path), path), 0.0 + 0.0j) + coefficient
            value = (entries, target_basis)
            self.crossing_cache[key] = value
            return value

        prefix = sequence[0] if generator_index == 1 else source_basis[0][generator_index - 2][0]
        for path in source_basis:
            prefix = sequence[0] if generator_index == 1 else path[generator_index - 2][0]
            left_channel, left_mult = path[generator_index - 1]
            total_segment, total_mult = path[generator_index]
            f1_key = (prefix, x, y, total_segment)
            f1 = self.f_blocks[f1_key]
            f1_inv = self.f_inv_blocks[f1_key]
            source_left = (left_channel, left_mult, total_mult)
            source_left_index = f1["left_index"][source_left]
            right_coefficients = f1_inv[:, source_left_index]
            for right_index, left_to_right in enumerate(right_coefficients):
                if abs(left_to_right) <= 1e-14:
                    continue
                middle_channel, xy_mult, prefix_middle_mult = f1["right_basis"][right_index]
                matrix_for = self.r_positive if positive else self.r_negative
                r_matrix = matrix_for[(x, y, middle_channel)]
                for yx_mult in range(r_matrix.shape[0]):
                    r_value = r_matrix[yx_mult, xy_mult]
                    if abs(r_value) <= 1e-14:
                        continue
                    f2_key = (prefix, y, x, total_segment)
                    f2 = self.f_blocks[f2_key]
                    right_after = (middle_channel, yx_mult, prefix_middle_mult)
                    right_after_index = f2["right_index"][right_after]
                    for left_after_index, right_to_left in enumerate(f2["matrix"][:, right_after_index]):
                        if abs(right_to_left) <= 1e-14:
                            continue
                        target_left, prefix_y_mult, target_total_mult = f2["left_basis"][left_after_index]
                        target_path = list(path)
                        target_path[generator_index - 1] = (target_left, prefix_y_mult)
                        target_path[generator_index] = (total_segment, target_total_mult)
                        target_path = tuple(target_path)
                        coefficient = right_to_left * r_value * left_to_right
                        entries[(target_path, path)] = entries.get((target_path, path), 0.0 + 0.0j) + coefficient

        entries = {item: value for item, value in entries.items() if abs(value) > 1e-14}
        value = (entries, target_basis)
        self.crossing_cache[key] = value
        return value


def build_braid_payload() -> dict:
    a3 = load_module(A3_PATH, "yasui_a3_base_for_da4_chunked")
    payload = json.loads(a3.INPUT.read_text())
    component_words, crossing_signs, crossing_records = a3.source_oriented_gauss_code(payload)
    link = a3.Link([component_words, crossing_signs])
    braid = link.braid()
    n_strands = int(braid.parent().strands())
    braid_word = [int(generator) for generator in braid.Tietze()]
    braid_linking = [
        [int(entry) for entry in row]
        for row in a3.braid_closure_linking_matrix(n_strands, tuple(braid_word))
    ]
    candidates = a3.component_permutation(a3.source_matrix(payload), braid_linking)
    selected = min(candidates) if candidates else None
    if selected is None:
        raise ValueError("a=3 component order did not match target linking matrix")
    components = a3.source_order(payload)
    component_order_in_braid = [components[source_index] for source_index in selected]
    framings = a3.source_framings(payload)
    framings_in_braid_order = [framings[source_index] for source_index in selected]
    return {
        "source_input": str(a3.INPUT.relative_to(REPO_ROOT)),
        "n_strands": n_strands,
        "braid_word": braid_word,
        "braid_word_length": len(braid_word),
        "component_order_in_source": a3.source_order(payload),
        "component_order_in_braid": component_order_in_braid,
        "source_index_per_braid_component": selected,
        "framings_in_braid_order": framings_in_braid_order,
        "target_intersection_matrix": a3.source_matrix(payload),
        "source_ordered_braid_linking_matrix": a3.source_ordered_matrix(braid_linking, selected),
        "crossing_signs": crossing_signs,
        "crossing_record_count": len(crossing_records),
    }


def sector_label_triples(labels: tuple[str, ...], start: int, count: int):
    return list(islice(product(labels, repeat=3), start, start + count))


def chunk_path(start: int, end: int) -> Path:
    return CHUNK_DIR / f"chunk-{start:07d}-{end:07d}.json"


def chunk_exists(index: int) -> bool:
    return chunk_path(index, index + 1).exists()


def compute_sector_payload(
    evaluator: DA4FRBraidEvaluator,
    braid: dict,
    mtc: dict,
    index: int,
    fixed_labels: tuple[str, ...],
    run_context: dict | None = None,
) -> dict:
    utc_start = datetime.now(UTC).isoformat()
    started = time.monotonic()
    amplitude, stats = evaluator.fixed_label_value(
        int(braid["n_strands"]),
        tuple(int(item) for item in braid["braid_word"]),
        tuple(fixed_labels),
        tuple(int(item) for item in braid["framings_in_braid_order"]),
    )
    coefficient = math.prod(evaluator.dimension(label) for label in fixed_labels)
    weighted = coefficient * amplitude
    utc_finish = datetime.now(UTC).isoformat()
    payload = {
        "schema": "twisted-yetter.yasui-figure3-a3-da4-untwisted-sector-chunk.v1",
        "status": "computed-numeric",
        "generator_script": "experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py",
        "argv": sys.argv[1:],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py '
            f"--start {index} --count 1"
        ),
        "utc_start": utc_start,
        "utc_finish": utc_finish,
        "kind": "fixed-label-sector",
        "mtc_id": mtc["mtc_id"],
        "category_id": "omega0_untwisted_D_A4",
        "link_id": "yasui-figure3-a3",
        "yetter_twist": "none",
        "sector_index": index,
        "sector_total": len(evaluator.labels) ** 3,
        "component_order_in_braid": braid["component_order_in_braid"],
        "source": {
            "mtc_artifact": "experiments/results/mtc-candidates/drinfeld-double-a4-omega0-mtc-fr-data-v1.json",
            "mtc_id": mtc["mtc_id"],
            "yasui_input": braid["source_input"],
            "n_strands": braid["n_strands"],
            "braid_word_length": braid["braid_word_length"],
            "framings_in_braid_order": braid["framings_in_braid_order"],
            "component_order_in_braid": braid["component_order_in_braid"],
        },
        "fixed_component_labels": list(fixed_labels),
        "untwisted_coefficient": repr(float(coefficient)),
        "fixed_sector_amplitude": complex_json(amplitude),
        "weighted_untwisted_contribution": complex_json(weighted),
        "elapsed_seconds": time.monotonic() - started,
        "evaluator_stats": stats,
        "repo": (run_context or {}).get("repo") or repo_metadata(),
        "tool_versions": (run_context or {}).get("tool_versions") or tool_versions(),
    }
    if run_context:
        payload["run_context"] = run_context
    return payload


def run(args: argparse.Namespace) -> int:
    utc_start = datetime.now(UTC).isoformat()
    wall_start = time.monotonic()
    mtc = json.loads(args.mtc.read_text())
    evaluator = DA4FRBraidEvaluator(mtc)
    braid = build_braid_payload()
    braid_word = tuple(int(item) for item in braid["braid_word"])
    framings = tuple(int(item) for item in braid["framings_in_braid_order"])
    labels = sector_label_triples(evaluator.labels, args.start, args.count)
    sector_total = len(evaluator.labels) ** 3
    chunk_payloads = []
    run_context = {
        "mode": "range",
        "range_start": args.start,
        "range_count": args.count,
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
    }

    for offset, fixed_labels in enumerate(labels):
        index = args.start + offset
        payload = compute_sector_payload(evaluator, braid, mtc, index, tuple(fixed_labels), run_context)
        path = chunk_path(index, index + 1)
        write_json(path, payload)
        payload["artifact"] = rel(path)
        chunk_payloads.append(payload)
        if not args.quiet:
            print(
                json.dumps(
                    {
                        "phase": "chunk-complete",
                        "sector_index": index,
                        "fixed_component_labels": list(fixed_labels),
                        "elapsed_seconds": payload["elapsed_seconds"],
                        "artifact": rel(path),
                        "max_basis_size": payload["evaluator_stats"].get("max_basis_size"),
                        "max_state_size": payload["evaluator_stats"].get("max_state_size"),
                    },
                    sort_keys=True,
                ),
                flush=True,
            )

    utc_finish = datetime.now(UTC).isoformat()
    elapsed_total = time.monotonic() - wall_start
    per_chunk = [payload["elapsed_seconds"] for payload in chunk_payloads]
    estimated_full_seconds = (elapsed_total / len(chunk_payloads) * sector_total) if chunk_payloads else None
    summary = {
        "schema": "twisted-yetter.yasui-figure3-a3-da4-untwisted-range-profile.v1",
        "status": "profile-complete",
        "generator_script": "experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py",
        "argv": sys.argv[1:],
        "reproduce_command": (
            f'DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py '
            f"--start {args.start} --count {args.count}"
        ),
        "utc_start": utc_start,
        "utc_finish": utc_finish,
        "elapsed_seconds": elapsed_total,
        "sage_version": SAGE_VERSION,
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "dirty": bool(command(["git", "status", "--short"])),
            "status_short": command(["git", "status", "--short"]),
        },
        "source": {
            "mtc_artifact": rel(args.mtc),
            "mtc_sha256": file_sha256(args.mtc),
            "yasui_input": braid["source_input"],
            "component_order_in_braid": braid["component_order_in_braid"],
            "framings_in_braid_order": braid["framings_in_braid_order"],
            "n_strands": braid["n_strands"],
            "braid_word_length": braid["braid_word_length"],
        },
        "scope": "first timing probe for fixed-label sectors of Yasui Figure 3 a=3 with D(A4) untwisted FR data and no Yetter twist",
        "claim_boundary": "numeric timing/profile artifact only; not an exact certificate or exotic invariant conclusion",
        "sector_total": len(evaluator.labels) ** 3,
        "start": args.start,
        "count": len(chunk_payloads),
        "requested_count": args.count,
        "chunk_dir": rel(CHUNK_DIR),
        "chunk_artifacts": [payload["artifact"] for payload in chunk_payloads],
        "timing": {
            "total_wall_seconds": elapsed_total,
            "per_chunk_seconds": per_chunk,
            "min_chunk_seconds": min(per_chunk) if per_chunk else None,
            "max_chunk_seconds": max(per_chunk) if per_chunk else None,
            "mean_chunk_seconds": (sum(per_chunk) / len(per_chunk)) if per_chunk else None,
            "estimated_full_2744_sector_seconds_from_wall": estimated_full_seconds,
        },
        "stats": {
            "max_basis_size_seen": max((payload["evaluator_stats"].get("max_basis_size", 0) for payload in chunk_payloads), default=0),
            "max_state_size_seen": max((payload["evaluator_stats"].get("max_state_size", 0) for payload in chunk_payloads), default=0),
            "unit_pruned_count": sum(1 for payload in chunk_payloads if payload["evaluator_stats"].get("unit_pruned")),
        },
    }
    write_json(args.profile_output, summary)
    print(json.dumps({"phase": "profile-complete", "artifact": rel(args.profile_output), "elapsed_seconds": elapsed_total}, sort_keys=True))
    return 0


class PoolState:
    def __init__(self, path: Path, lock_path: Path):
        self.path = path
        self.lock_path = lock_path
        self.lock_path.parent.mkdir(parents=True, exist_ok=True)

    def locked(self):
        return _PoolLock(self)


class _PoolLock:
    def __init__(self, state: PoolState):
        self.state = state
        self.handle = None

    def __enter__(self):
        self.handle = self.state.lock_path.open("a+")
        fcntl.flock(self.handle.fileno(), fcntl.LOCK_EX)
        if self.state.path.exists():
            payload = read_json(self.state.path)
        else:
            payload = None
        return payload

    def write(self, payload) -> None:
        write_json(self.state.path, payload)

    def __exit__(self, exc_type, exc, tb):
        fcntl.flock(self.handle.fileno(), fcntl.LOCK_UN)
        self.handle.close()


def initialize_pool_state(args, evaluator: DA4FRBraidEvaluator, braid: dict, mtc: dict) -> None:
    state = PoolState(args.pool_state, args.pool_state.with_suffix(args.pool_state.suffix + ".lock"))
    with state.locked() as payload:
        if payload is not None:
            return
        all_indices = list(range(args.pool_start, args.pool_end))
        completed = [index for index in all_indices if chunk_exists(index)]
        pending = [index for index in all_indices if index not in set(completed)]
        payload = {
            "schema": "twisted-yetter.yasui-figure3-a3-da4-untwisted-singleton-pool-state.v1",
            "status": "running",
            "created_at": datetime.now(UTC).isoformat(),
            "updated_at": datetime.now(UTC).isoformat(),
            "generator_script": "experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py",
            "pool": {
                "pool_start": args.pool_start,
                "pool_end": args.pool_end,
                "singleton_count": len(all_indices),
                "chunk_dir": rel(CHUNK_DIR),
                "mtc_artifact": rel(args.mtc),
                "mtc_id": mtc["mtc_id"],
                "yasui_input": braid["source_input"],
                "n_strands": braid["n_strands"],
                "braid_word_length": braid["braid_word_length"],
                "component_order_in_braid": braid["component_order_in_braid"],
                "claim_boundary": "Operational singleton worker-pool state only; not a complete invariant artifact by itself.",
            },
            "pending": pending,
            "in_progress": {},
            "completed": {
                str(index): {
                    "status": "preexisting",
                    "artifact": rel(chunk_path(index, index + 1)),
                }
                for index in completed
            },
            "failures": {},
            "events": [],
        }
        _PoolLock.write(_PoolLock(state), payload)


def claim_next_index(state: PoolState, worker_id: str, lease_seconds: int):
    now = time.time()
    now_iso = datetime.now(UTC).isoformat()
    with state.locked() as payload:
        if payload is None:
            raise ValueError("pool state is not initialized")
        completed = payload["completed"]
        pending = [index for index in payload["pending"] if str(index) not in completed and not chunk_exists(index)]
        payload["pending"] = pending
        stale = []
        for key, item in list(payload["in_progress"].items()):
            if chunk_exists(int(key)):
                completed[key] = {
                    "status": "completed-observed",
                    "artifact": rel(chunk_path(int(key), int(key) + 1)),
                }
                del payload["in_progress"][key]
            elif now - float(item["claimed_at_epoch"]) > lease_seconds:
                stale.append(int(key))
                del payload["in_progress"][key]
        if stale:
            payload["pending"] = sorted(set(stale + payload["pending"]))
        if not payload["pending"]:
            payload["status"] = "complete" if not payload["in_progress"] else "draining"
            payload["updated_at"] = now_iso
            _PoolLock.write(_PoolLock(state), payload)
            return None
        index = int(payload["pending"].pop(0))
        payload["in_progress"][str(index)] = {
            "worker_id": worker_id,
            "claimed_at": now_iso,
            "claimed_at_epoch": now,
        }
        payload["updated_at"] = now_iso
        payload["events"].append({"event": "claimed", "worker_id": worker_id, "sector_index": index, "at": now_iso})
        payload["events"] = payload["events"][-500:]
        _PoolLock.write(_PoolLock(state), payload)
        return index


def complete_index(state: PoolState, worker_id: str, index: int, payload: dict, artifact: Path) -> None:
    now_iso = datetime.now(UTC).isoformat()
    with state.locked() as state_payload:
        key = str(index)
        state_payload["in_progress"].pop(key, None)
        state_payload["completed"][key] = {
            "status": "computed",
            "worker_id": worker_id,
            "completed_at": now_iso,
            "artifact": rel(artifact),
            "elapsed_seconds": payload["elapsed_seconds"],
            "max_basis_size": payload["evaluator_stats"].get("max_basis_size"),
            "max_state_size": payload["evaluator_stats"].get("max_state_size"),
        }
        state_payload["updated_at"] = now_iso
        state_payload["events"].append({"event": "completed", "worker_id": worker_id, "sector_index": index, "at": now_iso, "elapsed_seconds": payload["elapsed_seconds"]})
        state_payload["events"] = state_payload["events"][-500:]
        if not state_payload["pending"] and not state_payload["in_progress"]:
            state_payload["status"] = "complete"
        _PoolLock.write(_PoolLock(state), state_payload)


def fail_index(state: PoolState, worker_id: str, index: int, error: str) -> None:
    now_iso = datetime.now(UTC).isoformat()
    with state.locked() as state_payload:
        key = str(index)
        state_payload["in_progress"].pop(key, None)
        state_payload["failures"][key] = {
            "worker_id": worker_id,
            "failed_at": now_iso,
            "error": error[-4000:],
        }
        state_payload["updated_at"] = now_iso
        state_payload["events"].append({"event": "failed", "worker_id": worker_id, "sector_index": index, "at": now_iso})
        state_payload["events"] = state_payload["events"][-500:]
        _PoolLock.write(_PoolLock(state), state_payload)


def run_singleton_pool(args: argparse.Namespace) -> int:
    mtc = json.loads(args.mtc.read_text())
    evaluator = DA4FRBraidEvaluator(mtc)
    braid = build_braid_payload()
    initialize_pool_state(args, evaluator, braid, mtc)
    state = PoolState(args.pool_state, args.pool_state.with_suffix(args.pool_state.suffix + ".lock"))
    labels = tuple(evaluator.labels)
    processed = 0
    started = time.monotonic()
    run_context = {
        "mode": "singleton-pool",
        "worker_id": args.worker_id,
        "pool_state": rel(args.pool_state),
        "pool_start": args.pool_start,
        "pool_end": args.pool_end,
        "lease_seconds": args.lease_seconds,
        "max_sectors": args.max_sectors,
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
    }
    while args.max_sectors is None or processed < args.max_sectors:
        index = claim_next_index(state, args.worker_id, args.lease_seconds)
        if index is None:
            break
        fixed_labels = tuple(next(islice(product(labels, repeat=3), index, None)))
        artifact = chunk_path(index, index + 1)
        if artifact.exists():
            payload = read_json(artifact)
            complete_index(state, args.worker_id, index, payload, artifact)
            continue
        try:
            payload = compute_sector_payload(evaluator, braid, mtc, index, fixed_labels, run_context)
            write_json(artifact, payload)
            complete_index(state, args.worker_id, index, payload, artifact)
            processed += 1
            if not args.quiet:
                print(json.dumps({"phase": "singleton-complete", "worker_id": args.worker_id, "sector_index": index, "elapsed_seconds": payload["elapsed_seconds"]}, sort_keys=True), flush=True)
        except Exception as exc:
            fail_index(state, args.worker_id, index, repr(exc))
            raise
    worker_profile = {
        "schema": "twisted-yetter.yasui-figure3-a3-da4-untwisted-singleton-worker-profile.v1",
        "status": "complete",
        "worker_id": args.worker_id,
        "pool_state": rel(args.pool_state),
        "processed": processed,
        "elapsed_wall_seconds": time.monotonic() - started,
        "finished_at": datetime.now(UTC).isoformat(),
    }
    worker_profile_path = RESULT_DIR / f"figure3-a3-da4-omega0-untwisted-singleton-worker-{args.worker_id}-profile-v1.json"
    write_json(worker_profile_path, worker_profile)
    return 0


def run_index_file(args: argparse.Namespace) -> int:
    utc_start = datetime.now(UTC).isoformat()
    wall_start = time.monotonic()
    mtc = json.loads(args.mtc.read_text())
    evaluator = DA4FRBraidEvaluator(mtc)
    braid = build_braid_payload()
    labels = tuple(evaluator.labels)
    index_payload = read_json(args.index_file)
    indices = [int(index) for index in index_payload["indices"]]
    skip_indices = set()
    if args.skip_index_file is not None:
        skip_payload = read_json(args.skip_index_file)
        skip_indices = {int(index) for index in skip_payload["indices"]}
    processed = []
    skipped = []
    run_context = {
        "mode": "index-file",
        "worker_id": args.worker_id,
        "index_file": rel(args.index_file),
        "index_file_sha256": file_sha256(args.index_file),
        "skip_index_file": rel(args.skip_index_file) if args.skip_index_file is not None else None,
        "skip_index_count": len(skip_indices),
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
    }
    for index in indices:
        if index in skip_indices:
            skipped.append(
                {
                    "sector_index": index,
                    "reason": "listed-in-skip-index-file",
                }
            )
            continue
        artifact = chunk_path(index, index + 1)
        if artifact.exists():
            skipped.append(
                {
                    "sector_index": index,
                    "reason": "preexisting-artifact",
                    "artifact": rel(artifact),
                }
            )
            continue
        fixed_labels = tuple(next(islice(product(labels, repeat=3), index, None)))
        payload = compute_sector_payload(evaluator, braid, mtc, index, fixed_labels, run_context)
        write_json(artifact, payload)
        processed.append(
            {
                "sector_index": index,
                "artifact": rel(artifact),
                "elapsed_seconds": payload["elapsed_seconds"],
                "max_basis_size": payload["evaluator_stats"].get("max_basis_size"),
                "max_state_size": payload["evaluator_stats"].get("max_state_size"),
            }
        )
        if not args.quiet:
            print(
                json.dumps(
                    {
                        "phase": "index-file-sector-complete",
                        "worker_id": args.worker_id,
                        "sector_index": index,
                        "elapsed_seconds": payload["elapsed_seconds"],
                    },
                    sort_keys=True,
                ),
                flush=True,
            )

    utc_finish = datetime.now(UTC).isoformat()
    worker_profile = {
        "schema": "twisted-yetter.yasui-figure3-a3-da4-untwisted-index-file-worker-profile.v1",
        "status": "complete",
        "generator_script": "experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py",
        "argv": sys.argv[1:],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py '
            f"--index-file {rel(args.index_file)} --worker-id {args.worker_id}"
        ),
        "worker_id": args.worker_id,
        "index_file": rel(args.index_file),
        "index_file_sha256": file_sha256(args.index_file),
        "skip_index_file": rel(args.skip_index_file) if args.skip_index_file is not None else None,
        "skip_index_count": len(skip_indices),
        "utc_start": utc_start,
        "utc_finish": utc_finish,
        "elapsed_wall_seconds": time.monotonic() - wall_start,
        "requested_count": len(indices),
        "processed_count": len(processed),
        "skipped_count": len(skipped),
        "processed": processed,
        "skipped": skipped,
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
        "claim_boundary": "Operational remote worker profile only; complete invariant aggregation is separate.",
    }
    worker_profile_path = RESULT_DIR / f"figure3-a3-da4-omega0-untwisted-index-worker-{args.worker_id}-profile-v1.json"
    write_json(worker_profile_path, worker_profile)
    return 0


def parse_args(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, default=20)
    parser.add_argument("--mtc", type=Path, default=MTC_PATH)
    parser.add_argument("--profile-output", type=Path)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--index-file", type=Path)
    parser.add_argument("--skip-index-file", type=Path)
    parser.add_argument("--singleton-pool", action="store_true")
    parser.add_argument("--pool-state", type=Path, default=POOL_STATE_PATH)
    parser.add_argument("--pool-start", type=int, default=0)
    parser.add_argument("--pool-end", type=int, default=2700)
    parser.add_argument("--worker-id", default=f"worker-{os.getpid()}")
    parser.add_argument("--lease-seconds", type=int, default=7200)
    parser.add_argument("--max-sectors", type=int)
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    args.mtc = args.mtc.resolve()
    args.pool_state = args.pool_state.resolve()
    if args.index_file is not None:
        args.index_file = args.index_file.resolve()
        if args.skip_index_file is not None:
            args.skip_index_file = args.skip_index_file.resolve()
        return run_index_file(args)
    if args.singleton_pool:
        return run_singleton_pool(args)
    if args.profile_output is None:
        args.profile_output = (
            RESULT_DIR
            / f"figure3-a3-da4-omega0-untwisted-profile-{args.start:07d}-{args.start + args.count:07d}-v1.json"
        )
    args.profile_output = args.profile_output.resolve()
    return run(args)


if __name__ == "__main__":
    raise SystemExit(main())
