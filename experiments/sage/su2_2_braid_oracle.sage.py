"""Exact SU(2)_2 braid-closure oracle for twisted Kirby stress tests.

Run from the repository root with:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_braid_oracle.sage.py --self-test

This is an experimental computation oracle, not the final local-piece
F/R-symbol evaluator.  It uses Alexander's theorem pragmatically: an oriented
link is entered as a braid closure, then Sage supplies the Jones polynomial of
the sigma-colored sublink.  The remaining SU(2)_2 labels are handled by the
transparent unit and the invertible psi object.

Conventions:

* simple labels are 0, 1, 2;
* label 1 is the sigma object, label 2 is the psi object;
* zeta = exp(2*pi*i/16);
* theta_0 = 1, theta_1 = zeta^3, theta_2 = zeta^8;
* Omega_a = sum_i d_i (-1)^(a deg(i)) i, with deg(1)=1 and deg(0)=deg(2)=0;
* a braid generator +k is Sage's positive sigma_k.

The core fixed-label formula is:

1. Delete all unit-labeled components.
2. Evaluate the sigma-labeled sublink through Sage's Jones polynomial at
   A=zeta in skein normalization, calibrated so the 0-framed sigma unknot has
   value sqrt(2).
3. Multiply by (-1)^lk for every psi/sigma linking.
4. Multiply by the framing factors theta_label^framing.
5. Expand Omega_a by summing d_label * character_a(label) times the fixed-label
   RT value over all simple labels on every component.

The script is intentionally small and auditable.  It is good enough for
stress tests where the input can be given as braid closures; it is not yet a
Kirby-diagram parser, a special-link handler, or a proof of the twisted formula.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from itertools import product
from pathlib import Path

from sage.all import BraidGroup, CyclotomicField, Integer, ZZ
from sage.knots.all import Link


K = CyclotomicField(16)
ZETA = K.gen()
SQRT2 = ZETA**2 + ZETA**(-2)

SIMPLE_LABELS = (0, 1, 2)
DEGREES = {0: 0, 1: 1, 2: 0}
DIMENSIONS = {0: K(1), 1: SQRT2, 2: K(1)}
TWISTS = {0: K(1), 1: ZETA**3, 2: ZETA**8}


@dataclass(frozen=True)
class ClosureData:
    components: tuple[tuple[int, ...], ...]
    strand_to_component: tuple[int, ...]


def component_data(n_strands, braid_word):
    """Return closure components and strand-to-component lookup.

    Components are ordered by their smallest original strand number.  Strand
    numbers are 0-based internally; braid generators remain 1-based.
    """

    _validate_braid(n_strands, braid_word)
    positions = list(range(n_strands))
    for generator in braid_word:
        index = abs(generator) - 1
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

    cycles = tuple(sorted(cycles, key=lambda c: c[0]))
    strand_to_component = [None] * n_strands
    for component_index, cycle in enumerate(cycles):
        for strand in cycle:
            strand_to_component[strand] = component_index
    return ClosureData(cycles, tuple(strand_to_component))


def linking_matrix(n_strands, braid_word):
    """Compute the oriented linking matrix of a braid closure."""

    data = component_data(n_strands, braid_word)
    component_count = len(data.components)
    crossing_sums = [[ZZ(0) for _ in range(component_count)] for _ in range(component_count)]
    positions = list(range(n_strands))

    for generator in braid_word:
        sign = ZZ(1) if generator > 0 else ZZ(-1)
        index = abs(generator) - 1
        left = positions[index]
        right = positions[index + 1]
        left_component = data.strand_to_component[left]
        right_component = data.strand_to_component[right]
        if left_component != right_component:
            crossing_sums[left_component][right_component] += sign
            crossing_sums[right_component][left_component] += sign
        positions[index], positions[index + 1] = positions[index + 1], positions[index]

    linkings = [[ZZ(0) for _ in range(component_count)] for _ in range(component_count)]
    for i in range(component_count):
        for j in range(i + 1, component_count):
            total = crossing_sums[i][j]
            if total % 2 != 0:
                raise ValueError("nonintegral linking number from braid closure")
            linkings[i][j] = total // 2
            linkings[j][i] = total // 2
    return tuple(tuple(row) for row in linkings)


def fixed_label_rt_value(n_strands, braid_word, labels, framings):
    """Evaluate a fixed simple-label SU(2)_2 framed RT link value."""

    data = component_data(n_strands, braid_word)
    if len(labels) != len(data.components):
        raise ValueError("label count must match closure component count")
    if len(framings) != len(data.components):
        raise ValueError("framing count must match closure component count")
    for label in labels:
        if label not in SIMPLE_LABELS:
            raise ValueError(f"unknown SU(2)_2 simple label: {label!r}")

    sigma_components = {index for index, label in enumerate(labels) if label == 1}
    sigma_strands = {
        strand
        for strand, component_index in enumerate(data.strand_to_component)
        if component_index in sigma_components
    }
    sigma_jones_value = _sigma_sublink_jones_at_zeta(
        n_strands,
        braid_word,
        sigma_strands,
        len(sigma_components),
    )
    if sigma_components:
        sigma_factor = ((-1) ** (len(sigma_components) - 1)) * SQRT2 * sigma_jones_value
    else:
        sigma_factor = K(1)

    linkings = linking_matrix(n_strands, braid_word)
    psi_sigma_exponent = ZZ(0)
    for left, left_label in enumerate(labels):
        if left_label != 2:
            continue
        for right, right_label in enumerate(labels):
            if right_label == 1:
                psi_sigma_exponent += linkings[left][right]
    psi_sigma_factor = K(-1) ** psi_sigma_exponent

    framing_factor = K(1)
    for label, framing in zip(labels, framings, strict=True):
        framing_factor *= TWISTS[label] ** ZZ(framing)

    return sigma_factor * psi_sigma_factor * framing_factor


def omega_value(n_strands, braid_word, framings, omega_labels):
    """Evaluate the link with every component colored by Omega_a."""

    data = component_data(n_strands, braid_word)
    component_count = len(data.components)
    if len(framings) != component_count:
        raise ValueError("framing count must match closure component count")
    if len(omega_labels) != component_count:
        raise ValueError("Omega label count must match closure component count")

    total = K(0)
    for labels in product(SIMPLE_LABELS, repeat=component_count):
        coefficient = K(1)
        for omega_label, simple_label in zip(omega_labels, labels, strict=True):
            coefficient *= DIMENSIONS[simple_label] * character(omega_label, simple_label)
        total += coefficient * fixed_label_rt_value(n_strands, braid_word, labels, framings)
    return total


def sector_amplitudes(n_strands, braid_word, framings):
    """Return fixed-label RT values keyed by simple-label sector."""

    data = component_data(n_strands, braid_word)
    component_count = len(data.components)
    if len(framings) != component_count:
        raise ValueError("framing count must match closure component count")
    return {
        labels: fixed_label_rt_value(n_strands, braid_word, labels, framings)
        for labels in product(SIMPLE_LABELS, repeat=component_count)
    }


def character(omega_label, simple_label):
    """The Z/2 universal-grading character used in Omega_a."""

    omega = ZZ(omega_label)
    if omega not in (0, 1):
        raise ValueError("SU(2)_2 Omega label must be 0 or 1")
    return K(-1) if omega == 1 and DEGREES[simple_label] == 1 else K(1)


def describe_braid(n_strands, braid_word):
    """Return JSON-ready braid-closure diagnostics."""

    data = component_data(n_strands, braid_word)
    return {
        "n_strands": int(n_strands),
        "braid_word": [int(g) for g in braid_word],
        "components_0_based_strands": [list(component) for component in data.components],
        "linking_matrix": [[int(x) for x in row] for row in linking_matrix(n_strands, braid_word)],
    }


def evaluate_payload(payload):
    """Evaluate a JSON-style payload.

    Required keys:
        n_strands, braid_word, framings, omega_labels
    Optional key:
        fixed_labels
    """

    n_strands = ZZ(payload["n_strands"])
    braid_word = tuple(ZZ(g) for g in payload["braid_word"])
    framings = tuple(ZZ(f) for f in payload["framings"])
    omega_labels = tuple(ZZ(a) for a in payload["omega_labels"])
    fixed_labels = payload.get("fixed_labels")

    output = {
        "schema": "twisted-yetter.su2_2-braid-oracle.v1",
        "status": "pass",
        "diagnostics": describe_braid(n_strands, braid_word),
        "framings": [int(f) for f in framings],
        "omega_labels": [int(a) for a in omega_labels],
        "omega_value": cyclotomic_json(omega_value(n_strands, braid_word, framings, omega_labels)),
    }
    if fixed_labels is not None:
        labels = tuple(ZZ(label) for label in fixed_labels)
        output["fixed_labels"] = [int(label) for label in labels]
        output["fixed_label_rt_value"] = cyclotomic_json(
            fixed_label_rt_value(n_strands, braid_word, labels, framings)
        )
    return output


def cyclotomic_json(value):
    """Return a compact exact representation of a Q(zeta_16) element."""

    value = K(value)
    return {
        "field": "CyclotomicField(16)",
        "zeta_symbol": "zeta16",
        "display": str(value),
        "coefficients": [str(coefficient) for coefficient in value.list()],
    }


def run_self_tests():
    """Regression checks against the hand-computed SU(2)_2 test bed."""

    _assert_equal(component_data(2, (1, 1)).components, ((0,), (1,)), "Hopf components")
    _assert_equal(component_data(2, (1, 1, 1)).components, ((0, 1),), "trefoil component")
    _assert_equal(linking_matrix(2, (1, 1)), ((ZZ(0), ZZ(1)), (ZZ(1), ZZ(0))), "Hopf linking")

    _assert_equal(
        fixed_label_rt_value(2, (1, 1), (1, 2), (0, 0)),
        -SQRT2,
        "Hopf fixed labels (1,2)",
    )
    _assert_equal(
        fixed_label_rt_value(2, (1, 1), (1, 1), (0, 0)),
        K(0),
        "Hopf fixed labels (1,1)",
    )
    _assert_equal(
        fixed_label_rt_value(2, (1, 1, 1), (1,), (0,)),
        -SQRT2,
        "right trefoil fixed label 1",
    )

    _assert_equal(omega_value(1, (), (1,), (0,)), 2 * ZETA**3, "CP2 Omega_0")
    _assert_equal(omega_value(1, (), (1,), (1,)), -2 * ZETA**3, "CP2 Omega_1")
    _assert_equal(omega_value(1, (), (-1,), (0,)), 2 * ZETA**13, "CPbar Omega_0")
    _assert_equal(omega_value(1, (), (-1,), (1,)), -2 * ZETA**13, "CPbar Omega_1")

    for a in (0, 1):
        for b in (0, 1):
            sign = (-1) ** (a + b)
            _assert_equal(
                omega_value(2, (1, 1), (1, 2), (a, (a + b) % 2)),
                sign * 4 * ZETA**6,
                f"CP2#CP2 slide a={a} b={b}",
            )
            _assert_equal(
                omega_value(2, (1, 1), (1, 0), (a, (a + b) % 2)),
                sign * 4,
                f"CP2#CPbar slide a={a} b={b}",
            )
            _assert_equal(
                omega_value(2, (1, 1), (0, 0), (a, (a + b) % 2)),
                4,
                f"S2xS2 slide a={a} b={b}",
            )

    _assert_equal(omega_value(2, (1, 1, 1), (0,), (0,)), K(0), "trefoil Omega_0")
    _assert_equal(omega_value(2, (1, 1, 1), (0,), (1,)), K(4), "trefoil Omega_1")


def _sigma_sublink_jones_at_zeta(n_strands, braid_word, selected_strands, sigma_component_count):
    if sigma_component_count == 0:
        return K(1)

    subword, selected_strand_count = _selected_subbraid_word(n_strands, braid_word, selected_strands)
    if not subword:
        return (-SQRT2) ** (sigma_component_count - 1)
    if selected_strand_count < 2:
        raise ValueError("nonempty selected subbraid needs at least two selected strands")

    braid_group = BraidGroup(Integer(selected_strand_count))
    link = Link(braid_group([Integer(g) for g in subword]))
    active_component_count = Integer(link.number_of_components())
    isolated_component_count = Integer(sigma_component_count) - active_component_count
    if isolated_component_count < 0:
        raise ValueError("sigma sublink has more active components than expected")

    polynomial = link.jones_polynomial(skein_normalization=True)
    return K(polynomial(ZETA)) * ((-SQRT2) ** isolated_component_count)


def _selected_subbraid_word(n_strands, braid_word, selected_strands):
    positions = list(range(n_strands))
    subword = []
    for generator in braid_word:
        sign = 1 if generator > 0 else -1
        index = abs(generator) - 1
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


def _validate_braid(n_strands, braid_word):
    if isinstance(n_strands, bool) or ZZ(n_strands) < 1:
        raise ValueError("n_strands must be a positive integer")
    for generator in braid_word:
        if isinstance(generator, bool) or ZZ(generator) == 0:
            raise ValueError("braid generators must be nonzero integers")
        if abs(ZZ(generator)) >= ZZ(n_strands):
            raise ValueError("braid generator index exceeds strand count")


def _assert_equal(actual, expected, name):
    if actual != expected:
        raise AssertionError(f"{name}: expected {expected!r}, got {actual!r}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="run exact regression tests")
    parser.add_argument("--input-json", type=Path, help="evaluate a JSON payload")
    parser.add_argument("--example", choices=("cp2", "trefoil", "hopf"), help="print an example payload")
    args = parser.parse_args(argv)

    if args.self_test:
        run_self_tests()
        print("self-test: pass")
        return

    if args.example:
        examples = {
            "cp2": {"n_strands": 1, "braid_word": [], "framings": [1], "omega_labels": [0]},
            "trefoil": {"n_strands": 2, "braid_word": [1, 1, 1], "framings": [0], "omega_labels": [1]},
            "hopf": {"n_strands": 2, "braid_word": [1, 1], "framings": [0, 0], "omega_labels": [0, 1]},
        }
        print(json.dumps(examples[args.example], indent=2, sort_keys=True))
        return

    if args.input_json:
        payload = json.loads(args.input_json.read_text())
        print(json.dumps(evaluate_payload(payload), indent=2, sort_keys=True))
        return

    parser.error("choose --self-test, --example, or --input-json")


if __name__ == "__main__":
    main()
