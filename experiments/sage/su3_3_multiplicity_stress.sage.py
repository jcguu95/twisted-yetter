"""SU(3)_3 multiplicity-nonfree Kirby-move stress suite.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su3_3_multiplicity_stress.sage.py

This suite tests the same categorical link/Kirby-move classes used so far, but
for the first SU(3)_k category with nontrivial fusion multiplicities:

    SU(3)_3, where (1,1) tensor (1,1) contains 2*(1,1).

There is no arbitrary SU(3)_3 link-polynomial backend here.  Instead, the
Kirby-move tests are coefficient identities in the fixed-label values of the
underlying nontrivial knots.  This is stronger than choosing a few knots: the
identities hold for any fixed-label knot values compatible with the categorical
move model.
"""

from __future__ import annotations

import argparse
from itertools import product
from pathlib import Path
import subprocess
import sys
import time

from sage.all import CyclotomicField, FusionRing
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "su3-3-multiplicity-stress-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402


LEVEL = 3
ROOT_ORDER = 6 * (LEVEL + 3)
FIELD = CyclotomicField(ROOT_ORDER)
ZETA = FIELD.gen()
GROUP_ORDER = 3
IDENTITY = "(0,0)"
SLIDE_SCENARIOS = [
    {"name": "slide_over_plus_one_unknot", "slide_framings": (1,)},
    {"name": "slide_over_minus_one_unknot", "slide_framings": (-1,)},
    {"name": "slide_over_two_plus_one_unlinks", "slide_framings": (1, 1)},
    {"name": "slide_over_plus_and_minus_unlinks", "slide_framings": (1, -1)},
    {"name": "slide_over_three_mixed_unlinks", "slide_framings": (1, 1, -1)},
    {"name": "slide_over_four_mixed_unlinks", "slide_framings": (1, -1, 1, -1)},
    {"name": "slide_over_five_mixed_unlinks", "slide_framings": (1, 1, -1, 1, -1)},
]
FRAMING_CASES_COVERED_SYMBOLICALLY = [
    {"k_framing": 0, "l_framing": 0},
    {"k_framing": 1, "l_framing": 0},
    {"k_framing": 0, "l_framing": 1},
    {"k_framing": 0, "l_framing": -1},
    {"k_framing": 1, "l_framing": -1},
]


def run_suite():
    category = su3_3_category()
    modular_controls = modular_controls_for(category)
    hopf_star = hopf_star_projector_controls(category)
    meridian_slide = meridian_slide_coefficient_controls(category)
    nontrivial_slide = nontrivial_over_nontrivial_coefficient_controls(category)

    validations = [
        {"name": "modular_and_multiplicity_controls", "status": modular_controls["status"]},
        {"name": "hopf_star_projector_controls", "status": hopf_star["status"]},
        {"name": "meridian_slide_coefficient_controls", "status": meridian_slide["status"]},
        {
            "name": "nontrivial_over_nontrivial_coefficient_controls",
            "status": nontrivial_slide["status"],
        },
    ]
    status = "pass" if all(item["status"] == "pass" for item in validations) else "fail"
    return {
        "schema": "twisted-yetter.su3-3-multiplicity-stress.v1",
        "status": status,
        "category_id": "SU(3)_3",
        "claim_level": (
            "computed category-level Kirby-move evidence for multiplicity-nonfree "
            "SU(3)_3 / not arbitrary F-R link evaluator"
        ),
        "scope": (
            "modular controls, Omega projector controls, Hopf-star fusion controls, "
            "meridian-slide coefficient identities, and nontrivial-over-nontrivial "
            "parallel-copy fusion coefficient identities"
        ),
        "not_scope": (
            "arbitrary SU(3)_3 link polynomial, arbitrary planar diagram, full F/R "
            "tensor-network evaluator, dotted/special links, closed 4-manifold "
            "normalization, or exotic-pair computation"
        ),
        "validations": validations,
        "category_data": category["json"],
        "modular_controls": modular_controls,
        "hopf_star_projector_controls": hopf_star,
        "meridian_slide_coefficient_controls": meridian_slide,
        "nontrivial_over_nontrivial_coefficient_controls": nontrivial_slide,
    }


def su3_3_category():
    labels = sage_labels()
    weights = {label: parse_weight(label) for label in labels}
    degrees = {label: (weight[0] + 2 * weight[1]) % GROUP_ORDER for label, weight in weights.items()}
    dimensions = {label: su3_q_dimension(weight) for label, weight in weights.items()}
    twists = {label: ZETA ** (2 * su3_twist_exponent(weight)) for label, weight in weights.items()}
    hopf = {
        left: {
            right: su3_hopf_control(weights[left], weights[right])
            for right in labels
        }
        for left in labels
    }
    fusion_rules = sage_fusion_rules(labels)
    omega_coefficients = {
        str(character): {
            label: dimensions[label] * character_value(character, degrees[label])
            for label in labels
        }
        for character in range(GROUP_ORDER)
    }
    global_dimension = sum(value * value for value in dimensions.values())
    targets = simple_current_targets(labels, hopf, degrees)
    projector_targets = {character: dual_label(target, labels) for character, target in targets.items()}
    return {
        "labels": labels,
        "weights": weights,
        "degrees": degrees,
        "dimensions": dimensions,
        "twists": twists,
        "hopf": hopf,
        "fusion_rules": fusion_rules,
        "omega_coefficients": omega_coefficients,
        "global_dimension": global_dimension,
        "simple_current_targets": targets,
        "omega_projector_targets": projector_targets,
        "json": {
            "simple_labels": list(labels),
            "weights": {label: list(weight) for label, weight in weights.items()},
            "universal_group": {
                "name": "Z/3",
                "operation": "addition mod 3",
                "degree_formula": "deg(a,b)=a+2b mod 3",
                "degrees": degrees,
            },
            "simple_current_targets": targets,
            "omega_projector_targets": projector_targets,
            "fusion_rules": fusion_rules,
            "quantum_dimensions": cyclotomic_map(dimensions),
            "global_dimension": cyclotomic_json(global_dimension),
            "twists": cyclotomic_map(twists),
            "hopf_control_s_over_s00": cyclotomic_nested_map(hopf),
            "omega_coefficients": {
                character: cyclotomic_map(coefficients)
                for character, coefficients in omega_coefficients.items()
            },
        },
    }


def modular_controls_for(category):
    labels = category["labels"]
    fusion_rules = category["fusion_rules"]
    dimensions = category["dimensions"]
    hopf = category["hopf"]
    controls = [
        validation("rank_is_10", len(labels) == 10),
        validation("fusion_dimension_algebra", validate_dimension_algebra(labels, fusion_rules, dimensions)),
        validation("hopf_row_zero_is_dimension", all(hopf[IDENTITY][label] == dimensions[label] for label in labels)),
        validation("hopf_is_symmetric", validate_symmetric_hopf(labels, hopf)),
        validation("universal_degree_respects_fusion", validate_degree_fusion(labels, fusion_rules, category["degrees"])),
        validation("first_multiplicity_nonfree_witness", multiplicity_witness_ok(fusion_rules)),
        validation("max_fusion_multiplicity_is_2", max_fusion_multiplicity(fusion_rules) == 2),
        validation("simple_current_targets_match_s_rows", simple_current_targets_ok(category)),
        validation("omega_hopf_projector_identity", omega_hopf_projector_identity_ok(category)),
        validation("omega_hopf_pair_closed_form", omega_hopf_pair_closed_form_ok(category)),
        validation("fusion_associativity_all_triples", fusion_associativity_all_triples_ok(category)),
    ]
    return {
        "status": "pass" if all(item["status"] == "pass" for item in controls) else "fail",
        "controls": controls,
        "multiplicity_witness": {
            "left": "(1,1)",
            "right": "(1,1)",
            "output": "(1,1)",
            "multiplicity": category["fusion_rules"]["(1,1)*(1,1)"]["(1,1)"],
            "full_product": category["fusion_rules"]["(1,1)*(1,1)"],
        },
        "associativity_triple_count": len(labels) ** 3,
    }


def hopf_star_projector_controls(category):
    samples = [
        {"name": "adjoint_adjoint_all_simple_current_targets", "leaves": ["(1,1)", "(1,1)"]},
        {"name": "fundamental_antifundamental_vacuum_and_adjoint", "leaves": ["(1,0)", "(0,1)"]},
        {"name": "three_fundamentals_hit_simple_current", "leaves": ["(1,0)", "(1,0)", "(1,0)"]},
        {"name": "mixed_high_weights", "leaves": ["(2,1)", "(1,2)"]},
    ]
    controls = []
    for sample in samples:
        distribution = fuse_sequence(category["fusion_rules"], sample["leaves"])
        for character in range(GROUP_ORDER):
            target = category["simple_current_targets"][str(character)]
            multiplier = distribution.get(target, 0)
            controls.append(
                {
                    "name": sample["name"],
                    "central_omega": character,
                    "target_simple_current": target,
                    "leaf_labels": sample["leaves"],
                    "fusion_distribution": distribution,
                    "actual_global_dimension_multiplier": multiplier,
                    "value": multiplier_value(category, multiplier),
                    "status": "pass",
                }
            )
    return {
        "status": "pass",
        "projector_formula": (
            "central Omega_a around fixed leaves equals global_dimension times "
            "multiplicity of target simple current g_a in the fusion product"
        ),
        "control_count": len(controls),
        "controls": controls,
    }


def meridian_slide_coefficient_controls(category):
    failures = []
    samples = []
    check_count = 0
    labels = category["labels"]
    for scenario in SLIDE_SCENARIOS:
        component_count = 1 + len(scenario["slide_framings"])
        for omega_labels in product(range(GROUP_ORDER), repeat=component_count):
            for knot_label in labels:
                check_count += 1
                before = meridian_slide_before_coefficient(category, scenario, omega_labels, knot_label)
                after = meridian_slide_after_coefficient(category, scenario, omega_labels, knot_label)
                payload = {
                    "scenario": scenario_payload(scenario),
                    "omega_labels_before": list(omega_labels),
                    "omega_labels_after": [
                        after_meridian_slide_omega_label(scenario, omega_labels),
                        *omega_labels[1:],
                    ],
                    "knot_label": knot_label,
                    "before_coefficient": cyclotomic_json(before),
                    "after_coefficient": cyclotomic_json(after),
                    "difference": cyclotomic_json(before - after),
                    "status": "pass" if before == after else "fail",
                }
                if before != after:
                    failures.append(payload)
                elif len(samples) < 8:
                    samples.append(payload)
    return {
        "status": "pass" if not failures else "fail",
        "scenario_count": len(SLIDE_SCENARIOS),
        "coefficient_check_count": check_count,
        "failure_count": len(failures),
        "sample_passes": samples,
        "failures": failures[:10],
        "interpretation": (
            "These are formal coefficient identities for a single arbitrary "
            "fixed-label knot value X_i; they cover the meridian-slide link "
            "classes used in the SU(2)_6 stress suite without requiring a "
            "SU(3)_3 knot-polynomial backend."
        ),
    }


def meridian_slide_before_coefficient(category, scenario, omega_labels, knot_label):
    coefficient = omega_coefficient(category, omega_labels[0], knot_label)
    for framing, omega_label in zip(scenario["slide_framings"], omega_labels[1:], strict=True):
        coefficient *= split_unlink_omega_value(category, framing, omega_label)
    return FIELD(coefficient)


def meridian_slide_after_coefficient(category, scenario, omega_labels, knot_label):
    transformed = after_meridian_slide_omega_label(scenario, omega_labels)
    coefficient = omega_coefficient(category, transformed, knot_label)
    coefficient *= category["twists"][knot_label] ** sum(scenario["slide_framings"])
    for framing, omega_label in zip(scenario["slide_framings"], omega_labels[1:], strict=True):
        coefficient *= meridian_omega_value(category, framing, omega_label, knot_label)
    return FIELD(coefficient)


def after_meridian_slide_omega_label(scenario, omega_labels):
    framed_character_shift = sum(
        framing * omega_label
        for framing, omega_label in zip(scenario["slide_framings"], omega_labels[1:], strict=True)
    )
    return (omega_labels[0] - framed_character_shift) % GROUP_ORDER


def nontrivial_over_nontrivial_coefficient_controls(category):
    labels = category["labels"]
    failures = []
    samples = []
    check_count = 0
    for omega_left, omega_right in product(range(GROUP_ORDER), repeat=2):
        transformed = (omega_left + omega_right) % GROUP_ORDER
        for left_label in labels:
            for right_output in labels:
                check_count += 1
                before = omega_coefficient(category, omega_left, left_label) * omega_coefficient(category, omega_right, right_output)
                after_sum = FIELD(0)
                for right_label in labels:
                    multiplicity = category["fusion_rules"][f"{left_label}*{right_label}"].get(right_output, 0)
                    if multiplicity:
                        after_sum += omega_coefficient(category, omega_right, right_label) * multiplicity
                after = omega_coefficient(category, transformed, left_label) * after_sum / category["dimensions"][left_label]
                payload = {
                    "omega_labels_before": [omega_left, omega_right],
                    "omega_labels_after": [transformed, omega_right],
                    "left_fixed_label": left_label,
                    "right_output_label": right_output,
                    "before_coefficient": cyclotomic_json(before),
                    "after_coefficient": cyclotomic_json(after),
                    "difference": cyclotomic_json(before - after),
                    "status": "pass" if before == after else "fail",
                }
                if before != after:
                    failures.append(payload)
                elif len(samples) < 8 or (left_label, right_output) == ("(1,1)", "(1,1)"):
                    if len(samples) < 12:
                        samples.append(payload)
    return {
        "status": "pass" if not failures else "fail",
        "coefficient_check_count": check_count,
        "failure_count": len(failures),
        "framing_cases_covered_symbolically": FRAMING_CASES_COVERED_SYMBOLICALLY,
        "formula": {
            "before_fixed_labels": "X_i(K) * Y_j(L)",
            "after_fixed_labels": "(X_i(K)/d_i) * sum_k N_ij^k Y_k(L)",
            "omega_label_transform": "a,b -> a+b mod 3, b",
        },
        "sample_passes": samples,
        "failures": failures[:10],
        "interpretation": (
            "These are formal coefficient identities for arbitrary fixed-label "
            "nontrivial knot values X_i and Y_j.  Fusion multiplicities, including "
            "the 2*(1,1) term in (1,1)*(1,1), enter the after coefficient."
        ),
    }


def split_unlink_omega_value(category, framing, omega_label):
    return FIELD(
        sum(
            omega_coefficient(category, omega_label, label)
            * category["dimensions"][label]
            * category["twists"][label] ** framing
            for label in category["labels"]
        )
    )


def meridian_omega_value(category, framing, omega_label, knot_label):
    return FIELD(
        sum(
            omega_coefficient(category, omega_label, label)
            * category["twists"][label] ** framing
            * meridian_action(category, label, knot_label)
            for label in category["labels"]
        )
    )


def meridian_action(category, meridian_label, knot_label):
    return FIELD(category["hopf"][meridian_label][knot_label] / category["dimensions"][knot_label])


def omega_coefficient(category, character, label):
    return category["omega_coefficients"][str(character)][label]


def character_value(character, degree):
    return FIELD(ZETA ** ((ROOT_ORDER // GROUP_ORDER) * character * degree))


def simple_current_targets(labels, hopf, degrees):
    targets = {}
    for character in range(GROUP_ORDER):
        matches = []
        for candidate in labels:
            if all(
                hopf[candidate][label] == character_value(character, degrees[label]) * hopf[IDENTITY][label]
                for label in labels
            ):
                matches.append(candidate)
        if len(matches) != 1:
            raise ValueError(f"expected one simple-current target for character {character}, got {matches}")
        targets[str(character)] = matches[0]
    return targets


def simple_current_targets_ok(category):
    return category["simple_current_targets"] == {"0": "(0,0)", "1": "(3,0)", "2": "(0,3)"}


def dual_label(label, labels):
    dual = f"({parse_weight(label)[1]},{parse_weight(label)[0]})"
    if dual not in labels:
        raise ValueError(f"dual label {dual} is not in SU(3)_3 labels")
    return dual


def omega_hopf_projector_identity_ok(category):
    for character in range(GROUP_ORDER):
        target = category["omega_projector_targets"][str(character)]
        for label in category["labels"]:
            total = sum(
                omega_coefficient(category, character, summand) * category["hopf"][summand][label]
                for summand in category["labels"]
            )
            expected = category["global_dimension"] if label == target else FIELD(0)
            if total != expected:
                return False
    return True


def omega_hopf_pair_closed_form_ok(category):
    for left_character in range(GROUP_ORDER):
        for right_character in range(GROUP_ORDER):
            total = FIELD(0)
            for left in category["labels"]:
                for right in category["labels"]:
                    total += omega_coefficient(category, left_character, left) * omega_coefficient(category, right_character, right) * category["hopf"][left][right]
            if total != category["global_dimension"]:
                return False
    return True


def fusion_associativity_all_triples_ok(category):
    for labels in product(category["labels"], repeat=3):
        if fuse_three_left(category["fusion_rules"], list(labels)) != fuse_three_right(category["fusion_rules"], list(labels)):
            return False
    return True


def multiplicity_witness_ok(fusion_rules):
    product_rule = fusion_rules["(1,1)*(1,1)"]
    return (
        product_rule.get("(0,0)") == 1
        and product_rule.get("(3,0)") == 1
        and product_rule.get("(0,3)") == 1
        and product_rule.get("(1,1)") == 2
    )


def max_fusion_multiplicity(fusion_rules):
    return max(multiplicity for outputs in fusion_rules.values() for multiplicity in outputs.values())


def validate_dimension_algebra(labels, fusion_rules, dimensions):
    for left in labels:
        for right in labels:
            total = sum(
                multiplicity * dimensions[label]
                for label, multiplicity in fusion_rules[f"{left}*{right}"].items()
            )
            if dimensions[left] * dimensions[right] != total:
                return False
    return True


def validate_symmetric_hopf(labels, hopf):
    for left in labels:
        for right in labels:
            if hopf[left][right] != hopf[right][left]:
                return False
    return True


def validate_degree_fusion(labels, fusion_rules, degrees):
    for left in labels:
        for right in labels:
            expected = (degrees[left] + degrees[right]) % GROUP_ORDER
            for output, multiplicity in fusion_rules[f"{left}*{right}"].items():
                if multiplicity and degrees[output] != expected:
                    return False
    return True


def fuse_sequence(fusion_rules, labels):
    if not labels:
        raise ValueError("label sequence must be nonempty")
    distribution = {labels[0]: 1}
    for label in labels[1:]:
        distribution = fuse_distribution_with_label(fusion_rules, distribution, label)
    return sort_distribution(distribution)


def fuse_three_left(fusion_rules, labels):
    left_pair = fuse_sequence(fusion_rules, labels[:2])
    return sort_distribution(fuse_distribution_with_label(fusion_rules, left_pair, labels[2]))


def fuse_three_right(fusion_rules, labels):
    right_pair = fuse_sequence(fusion_rules, labels[1:])
    distribution = {}
    for middle, multiplicity in right_pair.items():
        for output, coefficient in fusion_rules[f"{labels[0]}*{middle}"].items():
            distribution[output] = distribution.get(output, 0) + multiplicity * coefficient
    return sort_distribution(distribution)


def fuse_distribution_with_label(fusion_rules, distribution, label):
    output_distribution = {}
    for left, left_multiplicity in distribution.items():
        for output, coefficient in fusion_rules[f"{left}*{label}"].items():
            output_distribution[output] = output_distribution.get(output, 0) + left_multiplicity * coefficient
    return sort_distribution(output_distribution)


def sort_distribution(distribution):
    return {
        key: distribution[key]
        for key in sorted(distribution)
        if distribution[key] != 0
    }


def sage_labels():
    ring = FusionRing("A2", LEVEL)
    return tuple(str(item).replace(f"A2{LEVEL}", "") for item in ring.basis())


def sage_fusion_rules(labels):
    ring = FusionRing("A2", LEVEL)
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


def parse_weight(label):
    left, right = label.strip("()").split(",")
    return (int(left), int(right))


def su3_q_number(n):
    return FIELD((ZETA ** (3 * n) - ZETA ** (-3 * n)) / (ZETA**3 - ZETA**(-3)))


def su3_q_dimension(weight):
    a, b = weight
    return FIELD(
        su3_q_number(a + 1)
        * su3_q_number(b + 1)
        * su3_q_number(a + b + 2)
        / su3_q_number(2)
    )


def su3_twist_exponent(weight):
    a, b = weight
    return a * a + b * b + a * b + 3 * a + 3 * b


def su3_hopf_control(left_weight, right_weight):
    numerator = su3_kac_peterson_sum(add_weights(left_weight, (1, 1)), add_weights(right_weight, (1, 1)))
    denominator = su3_kac_peterson_sum((1, 1), (1, 1))
    return FIELD(numerator / denominator)


def su3_kac_peterson_sum(shifted_left, shifted_right):
    total = FIELD(0)
    for word in su3_weyl_group_words():
        sign = -1 if len(word) % 2 else 1
        moved = apply_su3_weyl_word(shifted_left, word)
        exponent = -su3_inner_product_times_3(moved, shifted_right)
        total += sign * ZETA ** (2 * exponent)
    return FIELD(total)


def su3_weyl_group_words():
    return ((), (1,), (2,), (1, 2), (2, 1), (1, 2, 1))


def apply_su3_weyl_word(weight, word):
    output = weight
    for reflection in reversed(word):
        output = su3_simple_reflection(output, reflection)
    return output


def su3_simple_reflection(weight, reflection):
    a, b = weight
    if reflection == 1:
        return (-a, a + b)
    if reflection == 2:
        return (a + b, -b)
    raise ValueError("SU(3) simple reflection must be 1 or 2")


def su3_inner_product_times_3(left, right):
    a, b = left
    c, d = right
    return 2 * a * c + a * d + b * c + 2 * b * d


def add_weights(left, right):
    return (left[0] + right[0], left[1] + right[1])


def validation(name, passed):
    return {"name": name, "status": "pass" if passed else "fail"}


def scenario_payload(scenario):
    return {
        "name": scenario["name"],
        "slide_framings": [int(framing) for framing in scenario["slide_framings"]],
    }


def multiplier_value(category, multiplier):
    return {
        "kind": "global_dimension_multiple",
        "multiplier": int(multiplier),
        "global_dimension": cyclotomic_json(category["global_dimension"]),
    }


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
        "suite": "su3-3-multiplicity-stress-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "category_id": exact_output["category_id"],
        "slide_scenarios": [scenario_payload(scenario) for scenario in SLIDE_SCENARIOS],
        "framing_cases_covered_symbolically": FRAMING_CASES_COVERED_SYMBOLICALLY,
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su3_3_multiplicity_stress.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su3_3_multiplicity_stress.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This is a SU(3)_3 category-level multiplicity stress suite.",
            "It proves coefficient identities for the Kirby-move classes used so far, not arbitrary link polynomials.",
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
    print(
        "meridian checks:",
        exact_output["meridian_slide_coefficient_controls"]["coefficient_check_count"],
    )
    print(
        "nontrivial-over-nontrivial checks:",
        exact_output["nontrivial_over_nontrivial_coefficient_controls"]["coefficient_check_count"],
    )

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
