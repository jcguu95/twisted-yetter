"""SU(2)_6 modular-data controls and supported link-class evaluator.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_6_modular_supported.sage.py

This artifact covers only the first two steps of the SU(2)_6 plan:

1. exact modular-data controls;
2. an explicitly restricted modular-data-only link class.

It does not evaluate arbitrary braid closures, trefoils, Borromean rings,
Hopf-star encircling diagrams, or any diagram requiring explicit F/R-symbol
fusion-space traces.
"""

from __future__ import annotations

import argparse
from itertools import product
from pathlib import Path
import subprocess
import sys
import time

from sage.all import CyclotomicField, Matrix, ZZ
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "su2-6-modular-supported-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402


LEVEL = 6
ROOT_ORDER = 32
FIELD = CyclotomicField(ROOT_ORDER)
ZETA = FIELD.gen()
LABELS = tuple(str(label) for label in range(LEVEL + 1))


def run_suite():
    data = modular_data()
    modular_controls = modular_data_controls(data)
    supported = supported_link_class()
    evaluator_controls = supported_evaluator_controls(data)
    validations = modular_controls + evaluator_controls["validations"]
    status = "pass" if all(item["status"] == "pass" for item in validations) else "fail"
    return {
        "schema": "twisted-yetter.su2-6-modular-supported.v1",
        "status": status,
        "category_id": "SU(2)_6",
        "claim_level": "computed modular-data evidence / restricted supported evaluator",
        "scope": "SU(2)_6 modular data plus split-union of unknots/Hopf-pairs evaluator",
        "not_scope": (
            "arbitrary colored link evaluator, arbitrary linking-matrix evaluator, trefoil, "
            "Borromean rings, Hopf-star encircling diagrams, F/R-symbol traces, "
            "dotted/special links, closed 4-manifold normalization, or exotic-pair computation"
        ),
        "modular_data": data["json"],
        "modular_data_controls": modular_controls,
        "supported_link_class": supported,
        "supported_evaluator_controls": evaluator_controls,
    }


def modular_data():
    dimensions = {label: su2_dimension(int(label)) for label in LABELS}
    twists = {label: su2_twist(int(label)) for label in LABELS}
    s_matrix = {
        left: {
            right: su2_s_matrix_entry(int(left), int(right))
            for right in LABELS
        }
        for left in LABELS
    }
    hopf = {
        left: {
            right: FIELD(s_matrix[left][right] / s_matrix["0"]["0"])
            for right in LABELS
        }
        for left in LABELS
    }
    fusion_rules = {
        f"{left}*{right}": su2_fusion_outputs(int(left), int(right))
        for left in LABELS
        for right in LABELS
    }
    degrees = {label: int(label) % 2 for label in LABELS}
    omega_coefficients = {
        str(character): {
            label: dimensions[label] * ((-1) ** (character * degrees[label]))
            for label in LABELS
        }
        for character in (0, 1)
    }
    return {
        "dimensions": dimensions,
        "twists": twists,
        "s_matrix": s_matrix,
        "hopf": hopf,
        "fusion_rules": fusion_rules,
        "degrees": degrees,
        "omega_coefficients": omega_coefficients,
        "json": {
            "simple_labels": list(LABELS),
            "universal_group": {
                "name": "Z/2",
                "operation": "addition mod 2",
                "degree_formula": "deg(j)=j mod 2",
                "degrees": degrees,
            },
            "fusion_rules": fusion_rules,
            "quantum_dimensions": cyclotomic_map(dimensions),
            "global_dimension": cyclotomic_json(
                sum(value * value for value in dimensions.values())
            ),
            "twists": cyclotomic_map(twists),
            "s_matrix": cyclotomic_nested_map(s_matrix),
            "hopf_control_s_over_s00": cyclotomic_nested_map(hopf),
            "omega_coefficients": {
                character: cyclotomic_map(coefficients)
                for character, coefficients in omega_coefficients.items()
            },
        },
    }


def modular_data_controls(data):
    return [
        validation("s_matrix_symmetric", validate_symmetric_matrix(data["s_matrix"])),
        validation("s_square_is_identity", validate_s_square_identity(data["s_matrix"])),
        validation(
            "hopf_row_zero_is_dimension",
            all(data["hopf"]["0"][label] == data["dimensions"][label] for label in LABELS),
        ),
        validation(
            "fusion_dimension_algebra",
            validate_dimension_algebra(data["fusion_rules"], data["dimensions"]),
        ),
        validation(
            "universal_degree_respects_fusion",
            validate_degree_fusion(data["fusion_rules"], data["degrees"]),
        ),
        validation(
            "omega_coefficients_match_degree_characters",
            validate_omega_coefficients(data["omega_coefficients"], data["dimensions"], data["degrees"]),
        ),
        validation(
            "simple_current_character_matches_degree",
            validate_simple_current_character(data["s_matrix"], data["degrees"]),
        ),
        validation(
            "omega_hopf_projector_identity",
            validate_omega_hopf_projector(data),
        ),
        validation(
            "omega_hopf_pair_closed_form",
            validate_omega_hopf_pair_closed_form(data),
        ),
    ]


def supported_link_class():
    return {
        "supported_diagram_schema": "split_union_of_supported_blocks",
        "supported_blocks": [
            {
                "kind": "framed_unknot",
                "fixed_label_value": "d_i * theta_i^framing",
            },
            {
                "kind": "positive_hopf_pair",
                "fixed_label_value": "(S_ij/S_00) * theta_i^framing_i * theta_j^framing_j",
            },
        ],
        "composition_rule": "values multiply over split-union blocks",
        "component_rule": "each component must occur in exactly one supported block",
        "omega_rule": "Omega_a = sum_j d_j (-1)^(a*j) X_j, with a in Z/2",
        "explicitly_rejected": [
            "arbitrary linking matrix",
            "trefoil or other nontrivial knot component",
            "general braid closure",
            "Borromean rings",
            "Hopf-star / one component encircling multiple nontrivial components",
            "any diagram needing F-symbol or R-symbol fusion-space traces",
        ],
        "reason_for_rejecting_hopf_star": (
            "In non-pointed categories, a central loop around several components depends on "
            "fusion channels of the enclosed labels.  Pairwise linking data alone is not a "
            "safe evaluator."
        ),
    }


def supported_evaluator_controls(data):
    diagrams = [
        {
            "name": "single-framed-unknot-plus-one",
            "diagram": {
                "component_count": 1,
                "blocks": [{"kind": "framed_unknot", "component": 0, "framing": 1}],
            },
            "omega_labels": [(0,), (1,)],
        },
        {
            "name": "split-two-framed-unlinks",
            "diagram": {
                "component_count": 2,
                "blocks": [
                    {"kind": "framed_unknot", "component": 0, "framing": 1},
                    {"kind": "framed_unknot", "component": 1, "framing": -1},
                ],
            },
            "omega_labels": list(product((0, 1), repeat=2)),
        },
        {
            "name": "positive-hopf-zero-framed",
            "diagram": {
                "component_count": 2,
                "blocks": [
                    {
                        "kind": "positive_hopf_pair",
                        "components": [0, 1],
                        "framings": [0, 0],
                    }
                ],
            },
            "omega_labels": list(product((0, 1), repeat=2)),
        },
        {
            "name": "split-hopf-plus-unknot",
            "diagram": {
                "component_count": 3,
                "blocks": [
                    {
                        "kind": "positive_hopf_pair",
                        "components": [0, 1],
                        "framings": [1, 2],
                    },
                    {"kind": "framed_unknot", "component": 2, "framing": -1},
                ],
            },
            "omega_labels": list(product((0, 1), repeat=3)),
        },
    ]

    controls = []
    for item in diagrams:
        values = []
        for omega_labels in item["omega_labels"]:
            direct = omega_value(data, item["diagram"], omega_labels)
            sector_sum = omega_value_from_recorded_sectors(data, item["diagram"], omega_labels)
            values.append(
                {
                    "omega_labels": [int(label) for label in omega_labels],
                    "value": cyclotomic_json(direct),
                    "sector_sum_value": cyclotomic_json(sector_sum),
                    "status": "pass" if direct == sector_sum else "fail",
                }
            )
        controls.append(
            {
                "name": item["name"],
                "diagram": item["diagram"],
                "status": "pass" if all(value["status"] == "pass" for value in values) else "fail",
                "value_count": len(values),
                "values": values,
            }
        )

    validation_items = [
        validation("supported_diagram_controls", all(item["status"] == "pass" for item in controls)),
        validation("unsupported_diagrams_are_rejected", validate_unsupported_rejections(data)),
    ]
    return {
        "status": "pass" if all(item["status"] == "pass" for item in validation_items) else "fail",
        "control_count": len(controls),
        "controls": controls,
        "validations": validation_items,
    }


def fixed_label_value(data, diagram, simple_labels):
    validate_supported_diagram(diagram)
    value = FIELD(1)
    for block in diagram["blocks"]:
        if block["kind"] == "framed_unknot":
            label = str(simple_labels[block["component"]])
            value *= data["dimensions"][label] * data["twists"][label] ** block["framing"]
        elif block["kind"] == "positive_hopf_pair":
            left_component, right_component = block["components"]
            left_label = str(simple_labels[left_component])
            right_label = str(simple_labels[right_component])
            left_framing, right_framing = block["framings"]
            value *= (
                data["hopf"][left_label][right_label]
                * data["twists"][left_label] ** left_framing
                * data["twists"][right_label] ** right_framing
            )
        else:
            raise ValueError(f"unsupported block kind: {block['kind']}")
    return FIELD(value)


def omega_value(data, diagram, omega_labels):
    component_count = diagram["component_count"]
    if len(omega_labels) != component_count:
        raise ValueError("Omega label count must match component count")
    total = FIELD(0)
    for simple_labels in product(range(LEVEL + 1), repeat=component_count):
        coefficient = FIELD(1)
        for omega_label, simple_label in zip(omega_labels, simple_labels, strict=True):
            label = str(simple_label)
            coefficient *= (
                data["dimensions"][label]
                * ((-1) ** (omega_label * data["degrees"][label]))
            )
        total += coefficient * fixed_label_value(data, diagram, simple_labels)
    return FIELD(total)


def omega_value_from_recorded_sectors(data, diagram, omega_labels):
    component_count = diagram["component_count"]
    total = FIELD(0)
    for simple_labels in product(range(LEVEL + 1), repeat=component_count):
        coefficient = FIELD(1)
        for omega_label, simple_label in zip(omega_labels, simple_labels, strict=True):
            label = str(simple_label)
            coefficient *= data["omega_coefficients"][str(omega_label)][label]
        total += coefficient * fixed_label_value(data, diagram, simple_labels)
    return FIELD(total)


def validate_supported_diagram(diagram):
    if not isinstance(diagram, dict):
        raise ValueError("diagram must be an object")
    component_count = diagram.get("component_count")
    if isinstance(component_count, bool) or not isinstance(component_count, int) or component_count < 1:
        raise ValueError("component_count must be a positive integer")
    blocks = diagram.get("blocks")
    if not isinstance(blocks, list) or not blocks:
        raise ValueError("diagram blocks must be a non-empty list")

    seen = []
    for block in blocks:
        if not isinstance(block, dict):
            raise ValueError("diagram block must be an object")
        kind = block.get("kind")
        if kind == "framed_unknot":
            component = block.get("component")
            framing = block.get("framing")
            if component not in range(component_count):
                raise ValueError("framed_unknot component out of range")
            if isinstance(framing, bool) or not isinstance(framing, int):
                raise ValueError("framed_unknot framing must be an integer")
            seen.append(component)
        elif kind == "positive_hopf_pair":
            components = block.get("components")
            framings = block.get("framings")
            if (
                not isinstance(components, list)
                or len(components) != 2
                or components[0] == components[1]
                or any(component not in range(component_count) for component in components)
            ):
                raise ValueError("positive_hopf_pair components must be distinct in-range components")
            if (
                not isinstance(framings, list)
                or len(framings) != 2
                or any(isinstance(framing, bool) or not isinstance(framing, int) for framing in framings)
            ):
                raise ValueError("positive_hopf_pair framings must be two integers")
            seen.extend(components)
        else:
            raise ValueError(f"unsupported block kind: {kind}")

    if sorted(seen) != list(range(component_count)):
        raise ValueError("each component must occur in exactly one supported block")


def validate_unsupported_rejections(data):
    unsupported_diagrams = [
        {
            "component_count": 1,
            "blocks": [{"kind": "trefoil", "component": 0, "framing": 0}],
        },
        {
            "component_count": 3,
            "blocks": [
                {
                    "kind": "hopf_star",
                    "center": 0,
                    "leaves": [1, 2],
                    "framings": [0, 0, 0],
                }
            ],
        },
        {
            "component_count": 2,
            "blocks": [{"kind": "arbitrary_linking_matrix", "matrix": [[0, 2], [2, 0]]}],
        },
    ]
    for diagram in unsupported_diagrams:
        try:
            fixed_label_value(data, diagram, tuple(0 for _ in range(diagram["component_count"])))
        except ValueError:
            continue
        return False
    return True


def su2_sine(numerator_multiplier):
    numerator = ZETA ** (2 * numerator_multiplier) - ZETA ** (-2 * numerator_multiplier)
    denominator = ZETA ** 8 - ZETA ** (-8)
    return FIELD(numerator / denominator)


def su2_dimension(label):
    return FIELD(su2_sine(label + 1) / su2_sine(1))


def su2_s_matrix_entry(left, right):
    return FIELD(su2_sine((left + 1) * (right + 1)) / 2)


def su2_twist(label):
    return ZETA ** (label * (label + 2))


def su2_fusion_outputs(left, right):
    outputs = {}
    lower = abs(left - right)
    upper = min(left + right, 2 * LEVEL - left - right)
    for label in range(lower, upper + 1):
        if (left + right + label) % 2 == 0:
            outputs[str(label)] = 1
    return outputs


def validate_symmetric_matrix(matrix):
    for left in LABELS:
        for right in LABELS:
            if matrix[left][right] != matrix[right][left]:
                return False
    return True


def validate_s_square_identity(s_matrix):
    matrix = Matrix(FIELD, [[s_matrix[left][right] for right in LABELS] for left in LABELS])
    square = matrix * matrix
    identity = Matrix(FIELD, [[1 if row == column else 0 for column in range(len(LABELS))] for row in range(len(LABELS))])
    return square == identity


def validate_dimension_algebra(fusion_rules, dimensions):
    for left in LABELS:
        for right in LABELS:
            total = sum(
                multiplicity * dimensions[label]
                for label, multiplicity in fusion_rules[f"{left}*{right}"].items()
            )
            if dimensions[left] * dimensions[right] != total:
                return False
    return True


def validate_degree_fusion(fusion_rules, degrees):
    for left in LABELS:
        for right in LABELS:
            expected = (degrees[left] + degrees[right]) % 2
            for output, multiplicity in fusion_rules[f"{left}*{right}"].items():
                if multiplicity and degrees[output] != expected:
                    return False
    return True


def validate_omega_coefficients(omega_coefficients, dimensions, degrees):
    for character in (0, 1):
        for label in LABELS:
            expected = dimensions[label] * ((-1) ** (character * degrees[label]))
            if omega_coefficients[str(character)][label] != expected:
                return False
    return True


def validate_simple_current_character(s_matrix, degrees):
    simple_current = str(LEVEL)
    for label in LABELS:
        expected = ((-1) ** degrees[label]) * s_matrix["0"][label]
        if s_matrix[simple_current][label] != expected:
            return False
    return True


def validate_omega_hopf_projector(data):
    global_dimension = sum(value * value for value in data["dimensions"].values())
    for character in (0, 1):
        target_label = str(LEVEL if character else 0)
        for label in LABELS:
            total = FIELD(0)
            for summand_label in LABELS:
                total += (
                    data["omega_coefficients"][str(character)][summand_label]
                    * data["hopf"][summand_label][label]
                )
            expected = global_dimension if label == target_label else FIELD(0)
            if total != expected:
                return False
    return True


def validate_omega_hopf_pair_closed_form(data):
    hopf_diagram = {
        "component_count": 2,
        "blocks": [
            {
                "kind": "positive_hopf_pair",
                "components": [0, 1],
                "framings": [0, 0],
            }
        ],
    }
    global_dimension = sum(value * value for value in data["dimensions"].values())
    for left_character, right_character in product((0, 1), repeat=2):
        if omega_value(data, hopf_diagram, (left_character, right_character)) != global_dimension:
            return False
    return True


def validation(name, passed):
    return {"name": name, "status": "pass" if passed else "fail"}


def cyclotomic_map(values):
    return {key: cyclotomic_json(value) for key, value in values.items()}


def cyclotomic_nested_map(values):
    return {
        left: {
            right: cyclotomic_json(value)
            for right, value in row.items()
        }
        for left, row in values.items()
    }


def cyclotomic_json(value):
    value = FIELD(value)
    return {
        "field": f"CyclotomicField({ROOT_ORDER})",
        "zeta_symbol": f"zeta{ROOT_ORDER}",
        "display": str(value),
        "coefficients": [str(coefficient) for coefficient in value.list()],
    }


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "su2-6-modular-supported-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "category_id": exact_output["category_id"],
        "supported_schema": exact_output["supported_link_class"]["supported_diagram_schema"],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_6_modular_supported.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_6_modular_supported.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This artifact covers SU(2)_6 modular data and a restricted supported link class only.",
            "It deliberately rejects arbitrary linking matrices and diagrams requiring F/R-symbol traces.",
        ],
    )


def git_metadata():
    return {
        "commit": _run(["git", "rev-parse", "HEAD"]),
        "dirty": bool(_run(["git", "status", "--porcelain"])),
    }


def utc_now_iso():
    return _run(["date", "-u", "+%Y-%m-%dT%H:%M:%SZ"])


def _run(command):
    return subprocess.run(
        command,
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)

    output_path = args.output
    if not output_path.is_absolute():
        output_path = REPO_ROOT / output_path
    output_path.parent.mkdir(parents=True, exist_ok=True)

    started_at = utc_now_iso()
    start = time.time()
    exact_output = run_suite()
    certificate = build_certificate(exact_output, output_path, started_at, time.time() - start)
    output_path.write_text(dumps_certificate(certificate))

    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {exact_output['status']}")
    print(f"modular controls: {len(exact_output['modular_data_controls'])}")
    print(f"supported evaluator controls: {exact_output['supported_evaluator_controls']['control_count']}")

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
