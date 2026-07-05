"""SU(2)_k mixed-color braid-closure evaluator.

Run quick controls from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2k_fusion_braid_evaluator.sage.py --self-test

This is a deliberately narrow evaluator.  It evaluates framed RT values for
braid closures whose components are colored by simple objects of SU(2)_k, then
expands the homologically twisted Kirby colors

    Omega_a = sum_j d_j (-1)^(a*j) X_j.

It is not a general planar tensor-graph parser and it does not handle dotted or
special Kirby components.  The implementation uses the multiplicity-free
SU(2)_k fusion-path basis, standard q-6j F-symbols, and R-symbols calibrated
against the Sage/SU(2)_2 braid oracle controls.
"""

from __future__ import annotations

import argparse
import json
from functools import lru_cache
from itertools import product
from pathlib import Path
import sys
import time

import numpy as np
from sage.all import AA, BraidGroup, ComplexField, CyclotomicField, Matrix, QQbar, ZZ
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]


class SU2KBraidEvaluator:
    """Fusion-path evaluator for SU(2)_k braid closures."""

    def __init__(self, level, *, exact=True, precision=160):
        self.level = int(level)
        self.root_order = 4 * (self.level + 2)
        self.exact = bool(exact)
        self.precision = int(precision)
        self.field = CyclotomicField(self.root_order) if self.exact else ComplexField(self.precision)
        self.A = self.field.gen() if self.exact else self.field.zeta(self.root_order)
        self.labels = tuple(range(self.level + 1))
        self._fixed_label_cache = {}
        self._numpy_crossing_cache = {}

    def coerce(self, value):
        return QQbar(value) if self.exact else self.field(value)

    def zero(self):
        return self.coerce(0)

    def one(self):
        return self.coerce(1)

    def sqrt(self, value):
        value = self.coerce(value)
        if self.exact:
            return positive_sqrt(value)
        return value.sqrt()

    def component_data(self, n_strands, braid_word):
        self._validate_braid(n_strands, braid_word)
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

    def fixed_label_value(self, n_strands, braid_word, component_labels, framings):
        """Return the framed RT value for fixed component labels."""

        n_strands = int(n_strands)
        braid_word = tuple(int(generator) for generator in braid_word)
        component_labels = tuple(int(label) for label in component_labels)
        framings = tuple(int(framing) for framing in framings)
        cache_key = (n_strands, braid_word, component_labels, framings)
        if cache_key in self._fixed_label_cache:
            return self._fixed_label_cache[cache_key]

        value = self._fixed_label_value_uncached(n_strands, braid_word, component_labels, framings)
        self._fixed_label_cache[cache_key] = value
        return value

    def _fixed_label_value_uncached(self, n_strands, braid_word, component_labels, framings):
        components, strand_to_component = self.component_data(n_strands, braid_word)
        if len(component_labels) != len(components):
            raise ValueError("component label count does not match braid closure")
        if len(framings) != len(components):
            raise ValueError("framing count does not match braid closure")
        for label in component_labels:
            if label not in self.labels:
                raise ValueError(f"unknown SU(2)_{self.level} label: {label!r}")
        if any(label == 0 for label in component_labels):
            nonunit_components = {
                index for index, label in enumerate(component_labels) if label != 0
            }
            if not nonunit_components:
                return self.one()
            selected_strands = {
                strand
                for strand, component_index in enumerate(strand_to_component)
                if component_index in nonunit_components
            }
            subword, selected_strand_count = self.selected_subbraid_word(
                n_strands,
                braid_word,
                selected_strands,
            )
            selected_strand_list = tuple(sorted(selected_strands))
            sub_components, _ = self.component_data(selected_strand_count, subword)
            sub_original_components = []
            for sub_component in sub_components:
                original_components = {
                    strand_to_component[selected_strand_list[sub_strand]]
                    for sub_strand in sub_component
                }
                if len(original_components) != 1:
                    raise ValueError(
                        "selected subbraid component mixes original components: "
                        f"{sorted(original_components)}"
                    )
                sub_original_components.append(original_components.pop())
            sub_labels = tuple(component_labels[index] for index in sub_original_components)
            sub_framings = tuple(framings[index] for index in sub_original_components)
            return self.fixed_label_value(
                selected_strand_count,
                subword,
                sub_labels,
                sub_framings,
            )

        strand_labels = tuple(component_labels[strand_to_component[strand]] for strand in range(n_strands))
        trace_value = self._braid_quantum_trace(strand_labels, braid_word)
        self_writhe = self.blackboard_self_writhe(n_strands, braid_word)
        framing_factor = self.one()
        for label, framing, writhe in zip(component_labels, framings, self_writhe, strict=True):
            framing_factor *= self.twist(label) ** (framing - writhe)
        return self.coerce(trace_value * framing_factor * self.degree_linking_phase(n_strands, braid_word, component_labels))

    def omega_value(self, n_strands, braid_word, framings, omega_labels):
        components, _ = self.component_data(n_strands, braid_word)
        omega_labels = tuple(int(label) for label in omega_labels)
        if len(omega_labels) != len(components):
            raise ValueError("Omega label count does not match braid closure")
        total = self.zero()
        for fixed_labels in product(self.labels, repeat=len(components)):
            coefficient = self.one()
            for omega_label, simple_label in zip(omega_labels, fixed_labels, strict=True):
                coefficient *= self.dimension(simple_label) * self.character(omega_label, simple_label)
            total += coefficient * self.fixed_label_value(n_strands, braid_word, fixed_labels, framings)
        return self.coerce(total)

    def sector_amplitudes(self, n_strands, braid_word, framings):
        components, _ = self.component_data(n_strands, braid_word)
        return {
            fixed_labels: self.fixed_label_value(n_strands, braid_word, fixed_labels, framings)
            for fixed_labels in product(self.labels, repeat=len(components))
        }

    def blackboard_self_writhe(self, n_strands, braid_word):
        components, strand_to_component = self.component_data(n_strands, braid_word)
        writhe = [ZZ(0) for _ in components]
        positions = list(range(n_strands))
        for generator in braid_word:
            sign = ZZ(1) if generator > 0 else ZZ(-1)
            index = abs(int(generator)) - 1
            left = positions[index]
            right = positions[index + 1]
            left_component = strand_to_component[left]
            right_component = strand_to_component[right]
            if left_component == right_component:
                writhe[left_component] += sign
            positions[index], positions[index + 1] = positions[index + 1], positions[index]
        return tuple(int(value) for value in writhe)

    def linking_matrix(self, n_strands, braid_word):
        components, strand_to_component = self.component_data(n_strands, braid_word)
        count = len(components)
        crossing_sums = [[ZZ(0) for _ in range(count)] for _ in range(count)]
        positions = list(range(n_strands))
        for generator in braid_word:
            sign = ZZ(1) if generator > 0 else ZZ(-1)
            index = abs(int(generator)) - 1
            left = positions[index]
            right = positions[index + 1]
            left_component = strand_to_component[left]
            right_component = strand_to_component[right]
            if left_component != right_component:
                crossing_sums[left_component][right_component] += sign
                crossing_sums[right_component][left_component] += sign
            positions[index], positions[index + 1] = positions[index + 1], positions[index]

        linkings = [[ZZ(0) for _ in range(count)] for _ in range(count)]
        for left in range(count):
            for right in range(left + 1, count):
                total = crossing_sums[left][right]
                if total % 2 != 0:
                    raise ValueError("nonintegral linking number from braid closure")
                linkings[left][right] = total // 2
                linkings[right][left] = total // 2
        return tuple(tuple(int(entry) for entry in row) for row in linkings)

    def degree_linking_phase(self, n_strands, braid_word, component_labels):
        # General SU(2)_k RT profile: no repo-local level-2 oracle phase.
        # Older SU(2)_2 Jones/oracle scripts used a separate convention; keep
        # that convention out of this shared evaluator so k=2 behaves like the
        # same RT profile as k>2.
        return self.one()

    @staticmethod
    def selected_subbraid_word(n_strands, braid_word, selected_strands):
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

    def _braid_quantum_trace(self, strand_labels, braid_word):
        if not self.exact:
            return self._braid_quantum_trace_numpy(strand_labels, braid_word)

        current_sequence = tuple(int(label) for label in strand_labels)
        initial_sequence = current_sequence
        total = self.zero()
        for total_charge in self.labels:
            initial_basis = self.paths(current_sequence, total_charge)
            if not initial_basis:
                continue
            state = {(path, path): self.one() for path in initial_basis}
            current_basis = initial_basis
            for generator in braid_word:
                crossing, next_basis = self.crossing_entries(
                    current_sequence,
                    total_charge,
                    abs(int(generator)) - 1,
                    int(generator) > 0,
                )
                state = self._compose_sparse(crossing, state)
                current_sequence = self.swapped_sequence(current_sequence, abs(int(generator)) - 1)
                current_basis = next_basis
            if current_sequence != initial_sequence:
                raise ValueError("braid closure colors are not component-constant")
            if current_basis != initial_basis:
                raise ValueError("internal basis ordering changed unexpectedly")
            trace = sum(
                coefficient
                for (target_path, source_path), coefficient in state.items()
                if target_path == source_path
            )
            total += self.dimension(total_charge) * trace
        return self.coerce(total)

    def _braid_quantum_trace_numpy(self, strand_labels, braid_word):
        current_sequence = tuple(int(label) for label in strand_labels)
        initial_sequence = current_sequence
        total = 0.0 + 0.0j
        for total_charge in self.labels:
            initial_basis = self.paths(current_sequence, total_charge)
            dimension = len(initial_basis)
            if dimension == 0:
                continue
            state = np.eye(dimension, dtype=np.complex128)
            current_basis = initial_basis
            for generator in braid_word:
                crossing, next_basis = self.numpy_crossing_matrix(
                    current_sequence,
                    total_charge,
                    abs(int(generator)) - 1,
                    int(generator) > 0,
                )
                state = crossing @ state
                current_sequence = self.swapped_sequence(current_sequence, abs(int(generator)) - 1)
                current_basis = next_basis
            if current_sequence != initial_sequence:
                raise ValueError("braid closure colors are not component-constant")
            if current_basis != initial_basis:
                raise ValueError("internal basis ordering changed unexpectedly")
            total += complex(self.dimension(total_charge)) * np.trace(state)
        return self.coerce(total)

    def numpy_crossing_matrix(self, sequence, total_charge, generator_index, positive):
        key = (tuple(sequence), int(total_charge), int(generator_index), bool(positive))
        if key in self._numpy_crossing_cache:
            return self._numpy_crossing_cache[key]
        crossing, target_basis = self.crossing_entries(*key)
        source_basis = self.paths(tuple(sequence), int(total_charge))
        target_index = {path: index for index, path in enumerate(target_basis)}
        source_index = {path: index for index, path in enumerate(source_basis)}
        matrix = np.zeros((len(target_basis), len(source_basis)), dtype=np.complex128)
        for (target_path, source_path), coefficient in crossing.items():
            matrix[target_index[target_path], source_index[source_path]] += complex(coefficient)
        value = (matrix, target_basis)
        self._numpy_crossing_cache[key] = value
        return value

    def crossing_matrix(self, sequence, total_charge, generator_index, positive):
        crossing, target_basis = self.crossing_entries(sequence, total_charge, generator_index, positive)
        source_basis = self.paths(sequence, total_charge)
        target_index = {path: index for index, path in enumerate(target_basis)}
        source_index = {path: index for index, path in enumerate(source_basis)}
        entries = [[self.zero() for _ in source_basis] for __ in target_basis]
        for (target_path, source_path), coefficient in crossing.items():
            entries[target_index[target_path]][source_index[source_path]] += coefficient
        return Matrix(QQbar if self.exact else self.field, entries)

    def _compose_sparse(self, left, right):
        by_source = {}
        for (target_path, source_path), coefficient in left.items():
            by_source.setdefault(source_path, []).append((target_path, coefficient))
        output = {}
        zero = self.zero()
        for (middle_path, original_path), right_coefficient in right.items():
            for target_path, left_coefficient in by_source.get(middle_path, ()):
                key = (target_path, original_path)
                output[key] = output.get(key, zero) + left_coefficient * right_coefficient
        return {key: value for key, value in output.items() if value != 0}

    @lru_cache(maxsize=None)
    def crossing_entries(self, sequence, total_charge, generator_index, positive):
        source_basis = self.paths(sequence, total_charge)
        target_sequence = self.swapped_sequence(sequence, generator_index)
        target_basis = self.paths(target_sequence, total_charge)
        entries = {}
        x = sequence[generator_index]
        y = sequence[generator_index + 1]

        def add_entry(target_path, source_path, coefficient):
            key = (target_path, source_path)
            entries[key] = entries.get(key, zero) + coefficient

        zero = self.zero()

        for path in source_basis:
            if generator_index == 0:
                channel = path[0]
                target_path = path
                scalar = self.r_symbol(x, y, channel, positive)
                add_entry(target_path, path, scalar)
                continue

            prefix = sequence[0] if generator_index == 1 else path[generator_index - 2]
            left_channel = path[generator_index - 1]
            total_segment = path[generator_index]
            for middle_channel in self.fusion_outputs(x, y):
                if not self.admissible(prefix, middle_channel, total_segment):
                    continue
                left_to_middle = self.f_symbol(prefix, x, y, total_segment, left_channel, middle_channel)
                r_value = self.r_symbol(x, y, middle_channel, positive)
                for target_left in self.fusion_outputs(prefix, y):
                    if not self.admissible(target_left, x, total_segment):
                        continue
                    middle_to_target = self.f_inverse_symbol(
                        prefix,
                        y,
                        x,
                        total_segment,
                        middle_channel,
                        target_left,
                    )
                    target_path = list(path)
                    target_path[generator_index - 1] = target_left
                    target_path = tuple(target_path)
                    add_entry(target_path, path, middle_to_target * r_value * left_to_middle)

        return ({key: value for key, value in entries.items() if value != 0}, target_basis)

    @lru_cache(maxsize=None)
    def paths(self, sequence, total_charge):
        sequence = tuple(int(label) for label in sequence)
        total_charge = int(total_charge)
        if len(sequence) == 0:
            return [()] if total_charge == 0 else []
        if len(sequence) == 1:
            return [()] if sequence[0] == total_charge else []

        output = []

        def extend(index, previous, path):
            if index == len(sequence):
                if previous == total_charge:
                    output.append(tuple(path))
                return
            for next_label in self.fusion_outputs(previous, sequence[index]):
                extend(index + 1, next_label, path + [next_label])

        for first in self.fusion_outputs(sequence[0], sequence[1]):
            extend(2, first, [first])
        return output

    @staticmethod
    def swapped_sequence(sequence, generator_index):
        sequence = list(sequence)
        sequence[generator_index], sequence[generator_index + 1] = sequence[generator_index + 1], sequence[generator_index]
        return tuple(sequence)

    def character(self, omega_label, simple_label):
        omega_label = int(omega_label)
        if omega_label not in (0, 1):
            raise ValueError("SU(2)_k universal character label must be 0 or 1")
        return self.coerce(-1) if omega_label == 1 and simple_label % 2 else self.one()

    @lru_cache(maxsize=None)
    def fusion_outputs(self, left, right):
        left = int(left)
        right = int(right)
        lower = abs(left - right)
        upper = min(left + right, 2 * self.level - left - right)
        return tuple(
            label
            for label in range(lower, upper + 1)
            if (left + right + label) % 2 == 0
        )

    @lru_cache(maxsize=None)
    def admissible(self, left, right, output):
        return int(output) in self.fusion_outputs(left, right)

    @lru_cache(maxsize=None)
    def q_int(self, number):
        number = int(number)
        if number == 0:
            return self.zero()
        value = (self.A ** (2 * number) - self.A ** (-2 * number)) / (self.A**2 - self.A**(-2))
        return self.coerce(value)

    @lru_cache(maxsize=None)
    def q_factorial(self, number):
        number = int(number)
        if number < 0:
            return self.zero()
        value = self.one()
        for index in range(1, number + 1):
            value *= self.q_int(index)
        return self.coerce(value)

    @lru_cache(maxsize=None)
    def dimension(self, label):
        return self.coerce(self.q_int(int(label) + 1))

    @lru_cache(maxsize=None)
    def twist(self, label):
        label = int(label)
        return self.coerce(self.A ** (label * (label + 2)))

    @lru_cache(maxsize=None)
    def delta(self, a, b, c):
        a = int(a)
        b = int(b)
        c = int(c)
        if not self.admissible(a, b, c):
            return self.zero()
        x = (a + b - c) // 2
        y = (a - b + c) // 2
        z = (-a + b + c) // 2
        w = (a + b + c) // 2 + 1
        squared = self.q_factorial(x) * self.q_factorial(y) * self.q_factorial(z) / self.q_factorial(w)
        return self.sqrt(squared)

    @lru_cache(maxsize=None)
    def quantum_6j(self, a, b, e, c, d, f):
        a = int(a)
        b = int(b)
        e = int(e)
        c = int(c)
        d = int(d)
        f = int(f)
        if not (
            self.admissible(a, b, e)
            and self.admissible(e, c, d)
            and self.admissible(b, c, f)
            and self.admissible(a, f, d)
        ):
            return self.zero()

        x_values = (
            (a + b + e) // 2,
            (e + c + d) // 2,
            (b + c + f) // 2,
            (a + f + d) // 2,
        )
        y_values = (
            (a + b + c + d) // 2,
            (a + c + e + f) // 2,
            (b + d + e + f) // 2,
        )
        lower = max(x_values)
        upper = min(y_values)
        summation = self.zero()
        for z_value in range(lower, upper + 1):
            denominator = self.one()
            for x_value in x_values:
                denominator *= self.q_factorial(z_value - x_value)
            for y_value in y_values:
                denominator *= self.q_factorial(y_value - z_value)
            summation += ((-1) ** z_value) * self.q_factorial(z_value + 1) / denominator

        return self.coerce(
            self.delta(a, b, e)
            * self.delta(e, c, d)
            * self.delta(b, c, f)
            * self.delta(a, f, d)
            * summation
        )

    @lru_cache(maxsize=None)
    def f_symbol(self, a, b, c, d, left_channel, right_channel):
        a = int(a)
        b = int(b)
        c = int(c)
        d = int(d)
        left_channel = int(left_channel)
        right_channel = int(right_channel)
        if a == 0:
            return self.one() if left_channel == b and right_channel == d else self.zero()
        if b == 0:
            return self.one() if left_channel == a and right_channel == c else self.zero()
        if c == 0:
            return self.one() if left_channel == d and right_channel == b else self.zero()
        sign = (-1) ** ((int(a) + int(b) + int(c) + int(d)) // 2)
        return self.coerce(
            sign
            * self.sqrt(self.dimension(left_channel) * self.dimension(right_channel))
            * self.quantum_6j(a, b, left_channel, c, d, right_channel)
        )

    @lru_cache(maxsize=None)
    def f_inverse_symbol(self, a, b, c, d, right_channel, left_channel):
        left_channels = tuple(
            label
            for label in self.fusion_outputs(a, b)
            if self.admissible(label, c, d)
        )
        right_channels = tuple(
            label
            for label in self.fusion_outputs(b, c)
            if self.admissible(a, label, d)
        )
        if left_channel not in left_channels or right_channel not in right_channels:
            return self.zero()
        base = QQbar if self.exact else self.field
        matrix = Matrix(
            base,
            [
                [
                    self.f_symbol(a, b, c, d, left, right)
                    for right in right_channels
                ]
                for left in left_channels
            ],
        )
        try:
            inverse = matrix.inverse()
        except ZeroDivisionError as exc:
            raise ZeroDivisionError(
                "singular F-matrix "
                f"args={(a, b, c, d)} "
                f"left_channels={left_channels} right_channels={right_channels} "
                f"matrix={matrix}"
            ) from exc
        return self.coerce(
            inverse[right_channels.index(right_channel), left_channels.index(left_channel)]
        )

    @lru_cache(maxsize=None)
    def r_symbol(self, left, right, output, positive=True):
        left = int(left)
        right = int(right)
        output = int(output)
        sign = (-1) ** ((left + right - output) // 2)
        if positive:
            exponent = -(left * (left + 2) + right * (right + 2) - output * (output + 2)) // 2
            return self.coerce(sign * self.A**exponent)
        exponent = -(right * (right + 2) + left * (left + 2) - output * (output + 2)) // 2
        return self.one() / self.coerce(sign * self.A**exponent)

    @staticmethod
    def _validate_braid(n_strands, braid_word):
        if int(n_strands) < 1:
            raise ValueError("n_strands must be positive")
        for generator in braid_word:
            if generator == 0 or abs(int(generator)) >= int(n_strands):
                raise ValueError(f"bad braid generator {generator!r} for {n_strands} strands")


def positive_sqrt(value):
    """Return the positive real algebraic square root when value is positive."""

    value = QQbar(value)
    real_value = AA(value.real())
    if real_value < 0:
        raise ValueError(f"expected nonnegative real value, got {value!r}")
    return QQbar(real_value.sqrt())


def algebraic_json(value):
    value = QQbar(value)
    return {
        "field": "QQbar",
        "display": str(value),
        "real": str(value.real()),
        "imag": str(value.imag()),
    }


def run_self_tests():
    evaluator = SU2KBraidEvaluator(2)
    tests = []
    tests.append(
        {
            "name": "sigma_unlink_two_components",
            "value": evaluator.fixed_label_value(2, (), (1, 1), (0, 0)),
            "expected": evaluator.dimension(1) ** 2,
        }
    )
    tests.append(
        {
            "name": "sigma_sigma_positive_hopf_is_zero",
            "value": evaluator.fixed_label_value(2, (1, 1), (1, 1), (0, 0)),
            "expected": QQbar(0),
        }
    )
    tests.append(
        {
            "name": "psi_sigma_positive_hopf_is_minus_sqrt2",
            "value": evaluator.fixed_label_value(2, (1, 1), (2, 1), (0, 0)),
            "expected": -evaluator.dimension(1),
        }
    )
    tests.append(
        {
            "name": "right_trefoil_sigma_matches_existing_oracle_value",
            "value": evaluator.fixed_label_value(2, (1, 1, 1), (1,), (0,)),
            "expected": -evaluator.dimension(1),
        }
    )
    rows = []
    for item in tests:
        equal = item["value"] == item["expected"]
        rows.append(
            {
                "name": item["name"],
                "value": algebraic_json(item["value"]),
                "expected": algebraic_json(item["expected"]),
                "difference": algebraic_json(item["value"] - item["expected"]),
                "status": "pass" if equal else "fail",
            }
        )
    return {
        "schema": "twisted-yetter.su2k-fusion-braid-self-test.v1",
        "status": "pass" if all(row["status"] == "pass" for row in rows) else "fail",
        "category_id": "SU(2)_2",
        "rows": rows,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        result = run_self_tests()
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0 if result["status"] == "pass" else 1
    parser.error("no action requested")


if __name__ == "__main__":
    raise SystemExit(main())
