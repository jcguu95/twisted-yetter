"""Numeric SU(3)_2 braid evaluator backed by selected AnyonWiki F/R data.

The loader adapts the selected AnyonWiki ``FR_6_1_4_5`` tables into the same
fixed-label braid-closure evaluator shape used by the D(A4) Yasui runs.  The
fusion category is multiplicity-free, but F blocks are kept as matrices because
nontrivial recoupling spaces can have dimension greater than one.
"""

from __future__ import annotations

from collections import defaultdict
from datetime import UTC, datetime
import hashlib
import json
import math
from pathlib import Path
import platform
import subprocess
import sys
import time

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[2]
ANYONWIKI_ROOT = REPO_ROOT / "experiments" / "inputs" / "anyon-wiki-data" / "FR_6_1_4_5"
RESULT_ROOT = REPO_ROOT / "experiments" / "results" / "anyon-wiki-su3-2"

SU3_LEVEL = 2
SU3_LABELS = ("(0,0)", "(1,0)", "(0,1)", "(2,0)", "(1,1)", "(0,2)")
SU3_WEIGHTS = {
    "(0,0)": (0, 0),
    "(1,0)": (1, 0),
    "(0,1)": (0, 1),
    "(2,0)": (2, 0),
    "(1,1)": (1, 1),
    "(0,2)": (0, 2),
}

# One fusion-ring isomorphism admitted by the candidate check artifact.
SAGE_ORDER_TO_ANYONWIKI = (1, 5, 6, 2, 4, 3)
ANYONWIKI_TO_SU3 = {
    anyonwiki_label: SU3_LABELS[index]
    for index, anyonwiki_label in enumerate(SAGE_ORDER_TO_ANYONWIKI)
}

TOLERANCE = 1e-9


def read_json(path: Path):
    return json.loads(path.read_text())


def write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def rel(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(REPO_ROOT))
    except ValueError:
        return str(resolved)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def command(argv: list[str]) -> str | None:
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def repo_metadata() -> dict:
    status_short = command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(status_short),
        "status_short": status_short,
    }


def environment_metadata() -> dict:
    return {
        "hostname": platform.node(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python_executable": sys.executable,
        "python_version": sys.version,
        "numpy_version": np.__version__,
    }


def complex_from_row(row: dict) -> complex:
    return complex(float(row["real"]), float(row["imag"]))


def complex_json(value: complex) -> dict[str, str]:
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def qint(n: int) -> float:
    return math.sin(n * math.pi / (SU3_LEVEL + 3)) / math.sin(math.pi / (SU3_LEVEL + 3))


def dimension_for_weight(weight: tuple[int, int]) -> float:
    a, b = weight
    return qint(a + 1) * qint(b + 1) * qint(a + b + 2) / qint(2)


def casimir(weight: tuple[int, int]) -> float:
    a, b = weight
    return (a * a + b * b + a * b + 3 * a + 3 * b) / 3


def twist_for_weight(weight: tuple[int, int]) -> complex:
    return complex(np.exp(2j * np.pi * casimir(weight) / (SU3_LEVEL + 3)))


def triality(label: str) -> int:
    a, b = SU3_WEIGHTS[label]
    return (a + 2 * b) % 3


def character_value(power: int, label: str) -> complex:
    return complex(np.exp(2j * np.pi * (int(power) % 3) * triality(label) / 3))


def one_component_gauss(evaluator: "SU32AnyonWikiFRBraidEvaluator", framing: int, character_power: int) -> complex:
    return sum(
        evaluator.dimension(label) ** 2
        * character_value(character_power, label)
        * evaluator.twist(label) ** int(framing)
        for label in evaluator.labels
    )


def cp2_2cpbar_split_value(
    evaluator: "SU32AnyonWikiFRBraidEvaluator",
    alpha: tuple[int, int, int],
    framings: tuple[int, int, int] = (1, -1, -1),
) -> complex:
    factors = [
        one_component_gauss(evaluator, framing, character_power)
        for framing, character_power in zip(framings, alpha, strict=True)
    ]
    return factors[0] * factors[1] * factors[2]


class SU32AnyonWikiFRBraidEvaluator:
    """Multiplicity-free F/R-symbol braid evaluator for SU(3)_2."""

    def __init__(
        self,
        root: Path = ANYONWIKI_ROOT,
        category_parameter: str = "cat_1_3_1",
        *,
        braiding_convention: str = "anyonwiki_direct",
    ):
        self.root = root
        self.category_parameter = category_parameter
        self.braiding_convention = braiding_convention
        self.labels = SU3_LABELS
        self.unit = self.labels[0]
        self.dimensions = {
            label: dimension_for_weight(SU3_WEIGHTS[label])
            for label in self.labels
        }
        self.twists = {
            label: twist_for_weight(SU3_WEIGHTS[label])
            for label in self.labels
        }
        self.fusion = self._load_fusion(root / "structconst.json")
        cat_root = root / category_parameter
        self.hex = self._load_table(cat_root / "hexsol.json")
        self.pent = self._load_table(cat_root / "pentsol.json")
        self.source_files = [
            root / "structconst.json",
            cat_root / "hexsol.json",
            cat_root / "pentsol.json",
            cat_root / "pivsol.json",
        ]
        self.fusion_outputs_cache: dict[tuple[str, str], tuple[tuple[str, int], ...]] = {}
        self.f_blocks = {}
        self.f_inv_blocks = {}
        self.r_positive = {}
        self.r_negative = {}
        self.paths_cache = {}
        self.crossing_cache = {}
        self._load_f_blocks()
        self._load_r_blocks()

    @staticmethod
    def _aw_to_su3(label: int) -> str:
        return ANYONWIKI_TO_SU3[int(label)]

    def _load_fusion(self, path: Path) -> dict[tuple[str, str, str], int]:
        payload = read_json(path)
        fusion = {}
        for row in payload["rows"]:
            left = self._aw_to_su3(row["left"])
            right = self._aw_to_su3(row["right"])
            output = self._aw_to_su3(row["output"])
            fusion[(left, right, output)] = fusion.get((left, right, output), 0) + 1
        if max(fusion.values(), default=0) != 1:
            raise ValueError("SU(3)_2 AnyonWiki adapter expected multiplicity-free fusion")
        return fusion

    def _load_table(self, path: Path) -> dict[tuple[str, ...], complex]:
        payload = read_json(path)
        table = {}
        for row in payload["rows"]:
            table[tuple(self._aw_to_su3(label) for label in row["labels"])] = complex_from_row(row)
        return table

    def _load_f_blocks(self) -> None:
        grouped: dict[tuple[str, str, str, str], dict[tuple[str, str], complex]] = defaultdict(dict)
        for key, value in self.pent.items():
            a, b, c, d, x, y = key
            grouped[(a, b, c, d)][(x, y)] = value

        for key, entries in grouped.items():
            a, b, c, d = key
            left_basis = tuple(
                (x, 0, 0)
                for x in self.labels
                if self.fusion.get((a, b, x), 0) and self.fusion.get((x, c, d), 0)
            )
            right_basis = tuple(
                (y, 0, 0)
                for y in self.labels
                if self.fusion.get((b, c, y), 0) and self.fusion.get((a, y, d), 0)
            )
            if not left_basis or not right_basis:
                continue
            matrix = np.zeros((len(left_basis), len(right_basis)), dtype=np.complex128)
            left_index = {basis: index for index, basis in enumerate(left_basis)}
            right_index = {basis: index for index, basis in enumerate(right_basis)}
            for (x, y), value in entries.items():
                left = (x, 0, 0)
                right = (y, 0, 0)
                if left in left_index and right in right_index:
                    matrix[left_index[left], right_index[right]] = value
            self.f_blocks[key] = {
                "matrix": matrix,
                "left_index": left_index,
                "right_index": right_index,
                "left_basis": left_basis,
                "right_basis": right_basis,
            }
            self.f_inv_blocks[key] = np.linalg.inv(matrix)

    def _r_value(self, a: str, b: str, c: str) -> complex:
        if self.braiding_convention == "anyonwiki_direct":
            return self.hex[(a, b, c)]
        if self.braiding_convention == "orientation_reversed":
            return 1 / self.hex[(b, a, c)]
        raise ValueError(f"unknown braiding convention: {self.braiding_convention}")

    def _load_r_blocks(self) -> None:
        triples = list(self.fusion)
        for a, b, c in triples:
            self.r_positive[(a, b, c)] = np.array([[self._r_value(a, b, c)]], dtype=np.complex128)
        for a, b, c in triples:
            self.r_negative[(a, b, c)] = np.linalg.inv(self.r_positive[(b, a, c)])

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
        for label, framing, writhe in zip(
            component_labels,
            framings,
            self.blackboard_self_writhe(n_strands, braid_word),
            strict=True,
        ):
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
                    target_path = tuple(target_path)
                    entries[(target_path, path)] = entries.get((target_path, path), 0.0 + 0.0j) + coefficient
            value = (entries, target_basis)
            self.crossing_cache[key] = value
            return value

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


def hopf_expected(evaluator: SU32AnyonWikiFRBraidEvaluator, left: str, right: str, *, positive: bool) -> complex:
    total = 0.0 + 0.0j
    for target, multiplicity in evaluator.fusion_outputs(left, right):
        if positive:
            monodromy = evaluator.twist(target) / (evaluator.twist(left) * evaluator.twist(right))
        else:
            monodromy = (evaluator.twist(left) * evaluator.twist(right)) / evaluator.twist(target)
        total += multiplicity * evaluator.dimension(target) * monodromy
    return total


def global_dimension(evaluator: SU32AnyonWikiFRBraidEvaluator) -> float:
    return sum(evaluator.dimension(label) ** 2 for label in evaluator.labels)


def simple_current_targets(evaluator: SU32AnyonWikiFRBraidEvaluator) -> dict[int, str]:
    targets = {}
    for character in range(3):
        matches = []
        for candidate in evaluator.labels:
            if abs(evaluator.dimension(candidate) - 1.0) > TOLERANCE:
                continue
            row_matches = True
            for label in evaluator.labels:
                expected = character_value(character, label) * evaluator.dimension(label)
                observed = hopf_expected(evaluator, candidate, label, positive=True)
                if abs(observed - expected) > 1e-8:
                    row_matches = False
                    break
            if row_matches:
                matches.append(candidate)
        if len(matches) != 1:
            raise ValueError(f"expected one simple-current target for character {character}, got {matches}")
        targets[character] = matches[0]
    return targets


def evaluator_metadata(evaluator: SU32AnyonWikiFRBraidEvaluator) -> dict:
    return {
        "category_id": "SU(3)_2",
        "adapter": "experiments/sage/su3_2_anyonwiki_fr_braid_evaluator.py",
        "anyonwiki_fusion_ring": "FR_6_1_4_5",
        "anyonwiki_category_parameter": evaluator.category_parameter,
        "braiding_convention": evaluator.braiding_convention,
        "sage_order_to_anyonwiki_labels": list(SAGE_ORDER_TO_ANYONWIKI),
        "simple_labels": list(evaluator.labels),
        "weights": {label: list(SU3_WEIGHTS[label]) for label in evaluator.labels},
        "triality": {label: triality(label) for label in evaluator.labels},
        "quantum_dimensions": {
            label: repr(float(evaluator.dimension(label)))
            for label in evaluator.labels
        },
        "twists": {
            label: complex_json(evaluator.twist(label))
            for label in evaluator.labels
        },
        "global_dimension": repr(float(global_dimension(evaluator))),
        "source_files": [
            {
                "path": rel(path),
                "sha256": file_sha256(path),
            }
            for path in evaluator.source_files
        ],
    }


def timed_call(fn, *args, **kwargs):
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    value = fn(*args, **kwargs)
    return value, {
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
    }
