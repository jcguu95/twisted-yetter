"""Generate exact category-side certificates for next MTC candidates.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/mtc_candidate_data.sage.py

This is a category-data and algebra-control certificate.  It deliberately does
not claim a general colored link evaluator for these categories.  The goal is
to pin down simple labels, fusion rules, dimensions, twists, Hopf controls,
universal grading, and Omega_a coefficients before building heavier F/R-symbol
or colored-Jones evaluators.
"""

from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
import subprocess
import sys
import time

from sage.all import CyclotomicField, Matrix, QQ, ZZ
from sage.algebras.fusion_rings.fusion_ring import FusionRing
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "mtc-candidate-data-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402


def run_suite():
    categories = [
        su2_level6_category(),
        vec_z3_pointed_category(),
        su3_level2_category(),
    ]
    status = "pass" if all(category["status"] == "pass" for category in categories) else "fail"
    return {
        "schema": "twisted-yetter.mtc-candidate-data-suite.v1",
        "status": status,
        "scope": (
            "category-side exact data, universal grading, Omega_a coefficients, "
            "Hopf controls, and small algebraic controls for the next MTC candidates"
        ),
        "not_scope": (
            "general colored link evaluator, F-symbol/R-symbol gauge certificate, "
            "arbitrary Kirby diagram evaluation, special-link handling, or exotic-pair computation"
        ),
        "category_count": len(categories),
        "categories": categories,
    }


def su2_level6_category():
    k = 6
    root_order = 32
    field = CyclotomicField(root_order)
    zeta = field.gen()
    labels = tuple(str(label) for label in range(k + 1))

    dimensions = {
        label: _su2_sine_ratio(field, zeta, int(label) + 1, k + 2)
        for label in labels
    }
    twists = {
        label: zeta ** (int(label) * (int(label) + 2))
        for label in labels
    }
    hopf = {
        left: {
            right: _su2_sine_ratio(
                field,
                zeta,
                (int(left) + 1) * (int(right) + 1),
                k + 2,
            )
            for right in labels
        }
        for left in labels
    }
    fusion_rules = {
        f"{left}*{right}": _su2_fusion_outputs(k, int(left), int(right))
        for left in labels
        for right in labels
    }
    degrees = {label: int(label) % 2 for label in labels}
    omega_coefficients = {
        str(character): {
            label: dimensions[label] * ((-1) ** (character * degrees[label]))
            for label in labels
        }
        for character in (0, 1)
    }

    validations = [
        _validation("fusion_dimension_algebra", _validate_dimension_algebra(labels, fusion_rules, dimensions)),
        _validation("hopf_row_zero_is_dimension", all(hopf["0"][label] == dimensions[label] for label in labels)),
        _validation("hopf_is_symmetric", _validate_symmetric_hopf(labels, hopf)),
        _validation("universal_degree_respects_fusion", _validate_degree_fusion(labels, fusion_rules, degrees, 2)),
    ]
    status = "pass" if all(item["status"] == "pass" for item in validations) else "fail"

    return {
        "category_id": "SU(2)_6",
        "status": status,
        "claim_level": "computed category-data evidence / no full link evaluator",
        "muger_center": "trivial (modular; checked here only through standard modular-data controls)",
        "universal_group": {
            "name": "Z/2",
            "operation": "addition mod 2",
            "degree_formula": "deg(j) = j mod 2",
            "degrees": degrees,
        },
        "simple_labels": list(labels),
        "fusion_rules": fusion_rules,
        "quantum_dimensions": _cyclotomic_map(dimensions, field, root_order),
        "global_dimension": cyclotomic_json(sum(value * value for value in dimensions.values()), field, root_order),
        "twists": _cyclotomic_map(twists, field, root_order),
        "hopf_control_s_over_s00": _cyclotomic_nested_map(hopf, field, root_order),
        "omega_coefficients": {
            character: _cyclotomic_map(coefficients, field, root_order)
            for character, coefficients in omega_coefficients.items()
        },
        "omega_unknot_controls": _omega_unknot_controls(labels, dimensions, twists, degrees, 2, field, root_order),
        "omega_hopf_controls": _omega_hopf_controls(labels, dimensions, hopf, degrees, 2, field, root_order),
        "validations": validations,
        "implementation_boundary": {
            "fixed_label_link_evaluator": "not implemented for SU(2)_6 in this artifact",
            "reason": "general colored Jones / fusion-space evaluator is needed beyond SU(2)_2 shortcuts",
        },
    }


def vec_z3_pointed_category():
    root_order = 3
    field = CyclotomicField(root_order)
    zeta = field.gen()
    labels = ("0", "1", "2")
    dimensions = {label: field(1) for label in labels}
    degrees = {label: int(label) for label in labels}
    twists = {label: zeta ** (int(label) * int(label)) for label in labels}
    bicharacter = {
        left: {
            right: zeta ** (2 * int(left) * int(right))
            for right in labels
        }
        for left in labels
    }
    fusion_rules = {
        f"{left}*{right}": {str((int(left) + int(right)) % 3): 1}
        for left in labels
        for right in labels
    }
    omega_coefficients = {
        str(character): {
            label: zeta ** (character * int(label))
            for label in labels
        }
        for character in (0, 1, 2)
    }
    slide_controls = _pointed_z3_slide_controls(field, zeta)

    validations = [
        _validation("fusion_dimension_algebra", _validate_dimension_algebra(labels, fusion_rules, dimensions)),
        _validation("bicharacter_is_symmetric", _validate_symmetric_hopf(labels, bicharacter)),
        _validation("universal_degree_respects_fusion", _validate_degree_fusion(labels, fusion_rules, degrees, 3)),
        _validation("pointed_slide_controls", all(item["status"] == "pass" for item in slide_controls)),
    ]
    status = "pass" if all(item["status"] == "pass" for item in validations) else "fail"

    return {
        "category_id": "Vec_Z3_q",
        "status": status,
        "claim_level": "computed pointed modular category evidence",
        "muger_center": "trivial because q(x)=zeta_3^(x^2) has nondegenerate bicharacter b(x,y)=zeta_3^(2xy)",
        "universal_group": {
            "name": "Z/3",
            "operation": "addition mod 3",
            "degree_formula": "deg(x) = x",
            "degrees": degrees,
        },
        "quadratic_form": "q(x)=zeta_3^(x^2)",
        "simple_labels": list(labels),
        "fusion_rules": fusion_rules,
        "quantum_dimensions": _cyclotomic_map(dimensions, field, root_order),
        "global_dimension": cyclotomic_json(field(3), field, root_order),
        "twists": _cyclotomic_map(twists, field, root_order),
        "hopf_control_bicharacter": _cyclotomic_nested_map(bicharacter, field, root_order),
        "omega_coefficients": {
            character: _cyclotomic_map(coefficients, field, root_order)
            for character, coefficients in omega_coefficients.items()
        },
        "omega_unknot_controls": _omega_unknot_controls(labels, dimensions, twists, degrees, 3, field, root_order),
        "omega_hopf_controls": _omega_hopf_controls(labels, dimensions, bicharacter, degrees, 3, field, root_order),
        "pointed_handle_slide_controls": slide_controls,
        "implementation_boundary": {
            "fixed_label_link_evaluator": "implemented here only for linking-matrix pointed controls",
            "reason": "pointed categories reduce fixed-label framed-link values to framings and pairwise linking numbers",
        },
        "validations": validations,
    }


def su3_level2_category():
    level = 2
    root_order = 30
    field = CyclotomicField(root_order)
    zeta = field.gen()
    labels = ("(0,0)", "(1,0)", "(0,1)", "(2,0)", "(1,1)", "(0,2)")
    weights = {
        "(0,0)": (0, 0),
        "(1,0)": (1, 0),
        "(0,1)": (0, 1),
        "(2,0)": (2, 0),
        "(1,1)": (1, 1),
        "(0,2)": (0, 2),
    }
    degrees = {
        label: (weight[0] + 2 * weight[1]) % 3
        for label, weight in weights.items()
    }
    dimensions = {
        label: _su3_q_dimension(field, zeta, weight, level)
        for label, weight in weights.items()
    }
    twists = {
        label: zeta ** (2 * _su3_twist_exponent(weight))
        for label, weight in weights.items()
    }
    hopf = {
        left: {
            right: _su3_hopf_control(field, zeta, weights[left], weights[right], level)
            for right in labels
        }
        for left in labels
    }
    fusion_rules = _su3_level2_fusion_rules_from_sage(labels)
    omega_coefficients = {
        str(character): {
            label: dimensions[label] * zeta ** (5 * character * degrees[label])
            for label in labels
        }
        for character in (0, 1, 2)
    }

    validations = [
        _validation("fusion_dimension_algebra", _validate_dimension_algebra(labels, fusion_rules, dimensions)),
        _validation("hopf_row_zero_is_dimension", all(hopf["(0,0)"][label] == dimensions[label] for label in labels)),
        _validation("hopf_is_symmetric", _validate_symmetric_hopf(labels, hopf)),
        _validation("universal_degree_respects_fusion", _validate_degree_fusion(labels, fusion_rules, degrees, 3)),
        _validation("sage_fusion_ring_basis_order", _su3_level2_sage_basis_order_ok(labels)),
    ]
    status = "pass" if all(item["status"] == "pass" for item in validations) else "fail"

    return {
        "category_id": "SU(3)_2",
        "status": status,
        "claim_level": "computed category-data evidence / no full link evaluator",
        "muger_center": "trivial (modular; checked here through standard modular-data controls)",
        "universal_group": {
            "name": "Z/3",
            "operation": "addition mod 3",
            "degree_formula": "deg(a,b) = a + 2b mod 3",
            "degrees": degrees,
        },
        "simple_labels": list(labels),
        "weights": {label: list(weight) for label, weight in weights.items()},
        "fusion_rules": fusion_rules,
        "fusion_source": "Sage FusionRing('A2', 2), validated against dimensions and universal grading",
        "quantum_dimensions": _cyclotomic_map(dimensions, field, root_order),
        "global_dimension": cyclotomic_json(sum(value * value for value in dimensions.values()), field, root_order),
        "twists": _cyclotomic_map(twists, field, root_order),
        "hopf_control_s_over_s00": _cyclotomic_nested_map(hopf, field, root_order),
        "omega_coefficients": {
            character: _cyclotomic_map(coefficients, field, root_order)
            for character, coefficients in omega_coefficients.items()
        },
        "omega_unknot_controls": _omega_unknot_controls(labels, dimensions, twists, degrees, 3, field, root_order),
        "omega_hopf_controls": _omega_hopf_controls(labels, dimensions, hopf, degrees, 3, field, root_order),
        "implementation_boundary": {
            "fixed_label_link_evaluator": "not implemented for SU(3)_2 in this artifact",
            "reason": "non-pointed non-SU(2) evaluation needs explicit F/R-symbol gauge and fusion-space traces",
        },
        "validations": validations,
    }


def _su2_sine_ratio(field, zeta, numerator_multiplier, denominator):
    root_power = 32 // (2 * denominator)
    numerator = zeta ** (root_power * numerator_multiplier) - zeta ** (-root_power * numerator_multiplier)
    denominator_value = zeta ** root_power - zeta ** (-root_power)
    return field(numerator / denominator_value)


def _su2_fusion_outputs(level, left, right):
    outputs = {}
    lower = abs(left - right)
    upper = min(left + right, 2 * level - left - right)
    for label in range(lower, upper + 1):
        if (left + right + label) % 2 == 0:
            outputs[str(label)] = 1
    return outputs


def _su3_q_number(field, zeta, n, level):
    denominator = level + 3
    numerator = zeta ** (3 * n) - zeta ** (-3 * n)
    denominator_value = zeta ** 3 - zeta ** (-3)
    return field(numerator / denominator_value)


def _su3_q_dimension(field, zeta, weight, level):
    a, b = weight
    return field(
        _su3_q_number(field, zeta, a + 1, level)
        * _su3_q_number(field, zeta, b + 1, level)
        * _su3_q_number(field, zeta, a + b + 2, level)
        / _su3_q_number(field, zeta, 2, level)
    )


def _su3_twist_exponent(weight):
    a, b = weight
    return a * a + b * b + a * b + 3 * a + 3 * b


def _su3_hopf_control(field, zeta, left_weight, right_weight, level):
    numerator = _su3_kac_peterson_sum(field, zeta, _add_weights(left_weight, (1, 1)), _add_weights(right_weight, (1, 1)), level)
    denominator = _su3_kac_peterson_sum(field, zeta, (1, 1), (1, 1), level)
    return field(numerator / denominator)


def _su3_kac_peterson_sum(field, zeta, shifted_left, shifted_right, level):
    total = field(0)
    for word in _su3_weyl_group_words():
        sign = -1 if len(word) % 2 else 1
        moved = _apply_su3_weyl_word(shifted_left, word)
        exponent = -_su3_inner_product_times_3(moved, shifted_right)
        total += sign * zeta ** (2 * exponent)
    return field(total)


def _su3_weyl_group_words():
    return ((), (1,), (2,), (1, 2), (2, 1), (1, 2, 1))


def _apply_su3_weyl_word(weight, word):
    output = weight
    for reflection in reversed(word):
        output = _su3_simple_reflection(output, reflection)
    return output


def _su3_simple_reflection(weight, reflection):
    a, b = weight
    if reflection == 1:
        return (-a, a + b)
    if reflection == 2:
        return (a + b, -b)
    raise ValueError("SU(3) simple reflection must be 1 or 2")


def _su3_inner_product_times_3(left, right):
    a, b = left
    c, d = right
    return 2 * a * c + a * d + b * c + 2 * b * d


def _add_weights(left, right):
    return (left[0] + right[0], left[1] + right[1])


def _su3_level2_fusion_rules_from_sage(labels):
    ring = FusionRing("A2", 2)
    basis = list(ring.basis())
    keys = list(ring.basis().keys())
    key_to_label = dict(zip(keys, labels))
    rules = {}
    for left_index, left_label in enumerate(labels):
        for right_index, right_label in enumerate(labels):
            product_element = basis[left_index] * basis[right_index]
            outputs = {
                key_to_label[key]: int(multiplicity)
                for key, multiplicity in sorted(
                    product_element.monomial_coefficients().items(),
                    key=lambda item: labels.index(key_to_label[item[0]]),
                )
            }
            rules[f"{left_label}*{right_label}"] = outputs
    return rules


def _su3_level2_sage_basis_order_ok(labels):
    ring = FusionRing("A2", 2)
    return tuple(str(item).replace("A22", "") for item in ring.basis()) == tuple(labels)


def _omega_unknot_controls(labels, dimensions, twists, degrees, group_order, field, root_order):
    controls = {}
    for character in range(group_order):
        values = {}
        for framing in (-1, 0, 1):
            total = field(0)
            for label in labels:
                total += dimensions[label] * dimensions[label] * _character_value(field, root_order, group_order, character, degrees[label]) * twists[label] ** framing
            values[str(framing)] = cyclotomic_json(total, field, root_order)
        controls[str(character)] = values
    return controls


def _omega_hopf_controls(labels, dimensions, hopf, degrees, group_order, field, root_order):
    controls = {}
    for left_character in range(group_order):
        for right_character in range(group_order):
            total = field(0)
            for left in labels:
                for right in labels:
                    total += (
                        dimensions[left]
                        * _character_value(field, root_order, group_order, left_character, degrees[left])
                        * dimensions[right]
                        * _character_value(field, root_order, group_order, right_character, degrees[right])
                        * hopf[left][right]
                    )
            controls[f"{left_character},{right_character}"] = cyclotomic_json(total, field, root_order)
    return controls


def _character_value(field, root_order, group_order, character, degree):
    if group_order == 2:
        return field((-1) ** (character * degree))
    if group_order == 3:
        zeta = field.gen()
        return zeta ** ((root_order // 3) * character * degree)
    raise ValueError(f"unsupported universal group order: {group_order}")


def _pointed_z3_slide_controls(field, zeta):
    cases = [
        {
            "name": "split-plus-minus",
            "before_matrix": ((1, 0), (0, -1)),
        },
        {
            "name": "hopf-zero",
            "before_matrix": ((0, 1), (1, 0)),
        },
        {
            "name": "linked-mixed",
            "before_matrix": ((2, -1), (-1, 1)),
        },
    ]
    controls = []
    basis = Matrix(ZZ, [[1, 0], [1, 1]])
    for case in cases:
        before_matrix = Matrix(ZZ, case["before_matrix"])
        after_matrix = basis.transpose() * before_matrix * basis
        for left_character, right_character in product(range(3), repeat=2):
            before_value = _pointed_z3_omega_link_value(field, zeta, before_matrix, (left_character, right_character))
            after_value = _pointed_z3_omega_link_value(
                field,
                zeta,
                after_matrix,
                ((left_character + right_character) % 3, right_character),
            )
            controls.append(
                {
                    "name": case["name"],
                    "labels_before": [left_character, right_character],
                    "labels_after": [(left_character + right_character) % 3, right_character],
                    "before_matrix": [[int(item) for item in row] for row in before_matrix.rows()],
                    "after_matrix": [[int(item) for item in row] for row in after_matrix.rows()],
                    "before_value": cyclotomic_json(before_value, field, 3),
                    "after_value": cyclotomic_json(after_value, field, 3),
                    "status": "pass" if before_value == after_value else "fail",
                }
            )
    return controls


def _pointed_z3_omega_link_value(field, zeta, linking_matrix, omega_labels):
    total = field(0)
    component_count = len(omega_labels)
    for simple_labels in product(range(3), repeat=component_count):
        term = field(1)
        for index, simple in enumerate(simple_labels):
            term *= zeta ** (omega_labels[index] * simple)
            term *= zeta ** (simple * simple * int(linking_matrix[index, index]))
        for left in range(component_count):
            for right in range(left + 1, component_count):
                term *= zeta ** (2 * simple_labels[left] * simple_labels[right] * int(linking_matrix[left, right]))
        total += term
    return field(total)


def _validate_dimension_algebra(labels, fusion_rules, dimensions):
    for left in labels:
        for right in labels:
            total = sum(
                multiplicity * dimensions[label]
                for label, multiplicity in fusion_rules[f"{left}*{right}"].items()
            )
            if dimensions[left] * dimensions[right] != total:
                return False
    return True


def _validate_symmetric_hopf(labels, hopf):
    for left in labels:
        for right in labels:
            if hopf[left][right] != hopf[right][left]:
                return False
    return True


def _validate_degree_fusion(labels, fusion_rules, degrees, group_order):
    for left in labels:
        for right in labels:
            expected = (degrees[left] + degrees[right]) % group_order
            for output, multiplicity in fusion_rules[f"{left}*{right}"].items():
                if multiplicity and degrees[output] != expected:
                    return False
    return True


def _validation(name, passed):
    return {"name": name, "status": "pass" if passed else "fail"}


def _cyclotomic_map(values, field, root_order):
    return {
        key: cyclotomic_json(value, field, root_order)
        for key, value in values.items()
    }


def _cyclotomic_nested_map(values, field, root_order):
    return {
        left: {
            right: cyclotomic_json(value, field, root_order)
            for right, value in row.items()
        }
        for left, row in values.items()
    }


def cyclotomic_json(value, field, root_order):
    value = field(value)
    return {
        "field": f"CyclotomicField({root_order})",
        "zeta_symbol": f"zeta{root_order}",
        "display": str(value),
        "coefficients": [str(coefficient) for coefficient in value.list()],
    }


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "mtc-candidate-data-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "categories": [category["category_id"] for category in exact_output["categories"]],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/mtc_candidate_data.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/mtc_candidate_data.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This artifact records category-side data and algebraic controls only.",
            "It is not a full F/R-symbol or arbitrary colored link evaluator certificate.",
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
    for category in exact_output["categories"]:
        print(f"{category['category_id']}: {category['status']}")

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
