"""SU(2)_6 multi-component mixed-color braid stress gate.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_6_multicomponent_mixed_stress.sage.py

This is deliberately smaller than Yasui.  It assumes the SU(2)_6 evaluator may
still be wrong and tests two small multi-component links with genuinely mixed
fixed labels:

* a 3-component pure-braid commutator, Borromean-like, with pairwise linking 0;
* a 2-component zero-linking 3-braid candidate whose ordinary Jones polynomial
  is not the split unlink polynomial.

For each base link the script compares fixed-label values under pure
conjugation, component-transporting conjugation, and positive/negative Markov
stabilization.  This is still not an independent colored-link oracle; it is a
small topological invariance pressure test for the F/R backend.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import sys
import time

from sage.all import BraidGroup, ComplexField
from sage.env import SAGE_VERSION
from sage.knots.all import Link


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "sage-stress"
    / "su2-6-multicomponent-mixed-stress-v1.json"
)
SU2K_EVALUATOR = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402
from twisted_yetter.artifacts import git_metadata, utc_now_iso  # noqa: E402


CF = ComplexField(160)
TOLERANCE = CF("1e-10")


BASE_CASES = [
    {
        "case_id": "pure-commutator-borromean-like",
        "description": "closure of [sigma1^2, sigma2^2]; 3 components with pairwise linking 0",
        "n_strands": 3,
        "braid_word": (1, 1, 2, 2, -1, -1, -2, -2),
        "framings": (0, 0, 0),
        "labels": (
            (1, 2, 3),
            (1, 3, 5),
            (2, 3, 4),
            (3, 4, 5),
            (1, 1, 2),
            (2, 2, 3),
        ),
        "moves": (
            {"name": "pure-conjugation-A12", "kind": "conjugation", "conjugator": (1, 1)},
            {"name": "pure-conjugation-A23", "kind": "conjugation", "conjugator": (2, 2)},
            {"name": "component-transport-conjugation-sigma1", "kind": "conjugation", "conjugator": (1,)},
            {"name": "component-transport-conjugation-sigma2", "kind": "conjugation", "conjugator": (2,)},
            {"name": "positive-markov-stabilization", "kind": "markov", "sign": 1},
            {"name": "negative-markov-stabilization", "kind": "markov", "sign": -1},
        ),
    },
    {
        "case_id": "two-component-zero-linking-3braid",
        "description": "2-component zero-linking 3-braid candidate with nontrivial ordinary Jones polynomial",
        "n_strands": 3,
        "braid_word": (1, 1, -2, 1, -2),
        "framings": (0, 0),
        "labels": (
            (1, 2),
            (1, 3),
            (2, 3),
            (1, 5),
            (3, 4),
            (5, 6),
        ),
        "moves": (
            {"name": "pure-conjugation-A12", "kind": "conjugation", "conjugator": (1, 1)},
            {"name": "pure-conjugation-A23", "kind": "conjugation", "conjugator": (2, 2)},
            {"name": "component-transport-conjugation-sigma1", "kind": "conjugation", "conjugator": (1,)},
            {"name": "component-transport-conjugation-sigma2", "kind": "conjugation", "conjugator": (2,)},
            {"name": "positive-markov-stabilization", "kind": "markov", "sign": 1},
            {"name": "negative-markov-stabilization", "kind": "markov", "sign": -1},
        ),
    },
]


def load_evaluator_module():
    spec = importlib.util.spec_from_file_location("su2k_fusion_braid_evaluator_for_multicomponent_stress", SU2K_EVALUATOR)
    module = importlib.util.module_from_spec(spec)
    sys.modules["su2k_fusion_braid_evaluator_for_multicomponent_stress"] = module
    spec.loader.exec_module(module)
    return module


def run_suite():
    module = load_evaluator_module()
    evaluator = module.SU2KBraidEvaluator(6, exact=False, precision=160)
    case_outputs = [run_case(evaluator, case) for case in BASE_CASES]
    status = "pass" if all(case["status"] == "pass" for case in case_outputs) else "fail"
    max_abs_difference = max(CF(case["max_abs_difference"]) for case in case_outputs)
    return {
        "schema": "twisted-yetter.su2-6-multicomponent-mixed-stress.v1",
        "status": status,
        "category_id": "SU(2)_6",
        "claim_level": "multi-component mixed fixed-label invariance pressure test",
        "scope": (
            "two small braid-closure links; mixed fixed simple labels; pure and "
            "component-transporting conjugation; positive and negative Markov stabilization"
        ),
        "not_scope": (
            "independent colored-link oracle, Yasui diagram admission, arbitrary MTC evaluator, "
            "dotted/special links, or exotic-pair computation"
        ),
        "tolerance": str(TOLERANCE),
        "max_abs_difference": str(max_abs_difference),
        "case_outputs": case_outputs,
    }


def run_case(evaluator, case):
    n_strands = int(case["n_strands"])
    braid_word = tuple(int(generator) for generator in case["braid_word"])
    base_components = evaluator.component_data(n_strands, braid_word)[0]
    base_linking = evaluator.linking_matrix(n_strands, braid_word)
    base_self_writhe = evaluator.blackboard_self_writhe(n_strands, braid_word)
    ordinary_jones = str(Link(BraidGroup(n_strands)(list(braid_word))).jones_polynomial())
    rows = []
    for labels in case["labels"]:
        base_value = evaluator.fixed_label_value(n_strands, braid_word, labels, case["framings"])
        for move in case["moves"]:
            moved = moved_case(evaluator, case, move)
            moved_labels = transported_labels(
                base_components,
                labels,
                moved["components"],
                moved["component_map"],
            )
            moved_framings = transported_labels(
                base_components,
                case["framings"],
                moved["components"],
                moved["component_map"],
            )
            moved_value = evaluator.fixed_label_value(
                moved["n_strands"],
                moved["braid_word"],
                moved_labels,
                moved_framings,
            )
            rows.append(compare_row(case, move, labels, moved_labels, base_value, moved_value, moved))
    failures = [row for row in rows if row["status"] != "pass"]
    max_abs_difference = max(CF(row["abs_difference"]) for row in rows)
    return {
        "case_id": case["case_id"],
        "description": case["description"],
        "status": "pass" if not failures else "fail",
        "n_strands": n_strands,
        "braid_word": list(braid_word),
        "components": [list(component) for component in base_components],
        "linking_matrix": [list(row) for row in base_linking],
        "self_writhe": list(base_self_writhe),
        "ordinary_jones_polynomial": ordinary_jones,
        "label_count": len(case["labels"]),
        "move_count": len(case["moves"]),
        "comparison_count": len(rows),
        "max_abs_difference": str(max_abs_difference),
        "sample_rows": rows[:12],
        "sample_failures": failures[:10],
    }


def moved_case(evaluator, case, move):
    n_strands = int(case["n_strands"])
    braid_word = tuple(int(generator) for generator in case["braid_word"])
    base_components = evaluator.component_data(n_strands, braid_word)[0]
    if move["kind"] == "conjugation":
        conjugator = tuple(int(generator) for generator in move["conjugator"])
        moved_word = conjugator + braid_word + tuple(-generator for generator in reversed(conjugator))
        moved_components = evaluator.component_data(n_strands, moved_word)[0]
        component_map = conjugation_component_map(n_strands, conjugator, base_components, moved_components)
        return {
            "n_strands": n_strands,
            "braid_word": moved_word,
            "components": moved_components,
            "component_map": component_map,
        }

    if move["kind"] == "markov":
        sign = int(move["sign"])
        moved_word = braid_word + (sign * n_strands,)
        moved_n_strands = n_strands + 1
        moved_components = evaluator.component_data(moved_n_strands, moved_word)[0]
        component_map = overlap_component_map(base_components, moved_components)
        return {
            "n_strands": moved_n_strands,
            "braid_word": moved_word,
            "components": moved_components,
            "component_map": component_map,
        }

    raise ValueError(f"unknown move kind: {move['kind']!r}")


def conjugation_component_map(n_strands, conjugator, base_components, moved_components):
    image = strand_image_under_braid(n_strands, conjugator)
    moved_index = {frozenset(component): index for index, component in enumerate(moved_components)}
    mapping = {}
    for old_index, component in enumerate(base_components):
        moved_component = frozenset(image[strand] for strand in component)
        mapping[old_index] = moved_index[moved_component]
    return mapping


def strand_image_under_braid(n_strands, braid_word):
    positions = list(range(n_strands))
    for generator in braid_word:
        index = abs(int(generator)) - 1
        positions[index], positions[index + 1] = positions[index + 1], positions[index]
    image = [None] * n_strands
    for top_position, original_strand in enumerate(positions):
        image[original_strand] = top_position
    return tuple(image)


def overlap_component_map(base_components, moved_components):
    mapping = {}
    moved_sets = [set(component) for component in moved_components]
    for old_index, component in enumerate(base_components):
        hits = [
            moved_index
            for moved_index, moved_set in enumerate(moved_sets)
            if set(component).issubset(moved_set)
        ]
        if len(hits) != 1:
            raise ValueError(f"could not transport component {component!r} through Markov move")
        mapping[old_index] = hits[0]
    return mapping


def transported_labels(base_components, labels, moved_components, component_map):
    if len(labels) != len(base_components):
        raise ValueError("label/framing count does not match base component count")
    output = [None] * len(moved_components)
    for old_index, value in enumerate(labels):
        output[component_map[old_index]] = int(value)
    if any(value is None for value in output):
        raise ValueError(f"incomplete component transport: {component_map!r}")
    return tuple(output)


def compare_row(case, move, base_labels, moved_labels, base_value, moved_value, moved):
    difference = CF(base_value) - CF(moved_value)
    abs_difference = abs(difference)
    return {
        "case_id": case["case_id"],
        "move": move["name"],
        "base_labels": [int(label) for label in base_labels],
        "moved_labels": [int(label) for label in moved_labels],
        "moved_n_strands": int(moved["n_strands"]),
        "moved_braid_word": [int(generator) for generator in moved["braid_word"]],
        "moved_components": [list(component) for component in moved["components"]],
        "component_map_old_to_new": {str(key): int(value) for key, value in moved["component_map"].items()},
        "base_value": complex_json(base_value),
        "moved_value": complex_json(moved_value),
        "difference": complex_json(difference),
        "abs_difference": str(abs_difference),
        "status": "pass" if abs_difference < TOLERANCE else "fail",
    }


def complex_json(value):
    value = CF(value)
    return {
        "field": "ComplexField(160)",
        "display": str(value),
        "real": str(value.real()),
        "imag": str(value.imag()),
    }


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "su2-6-multicomponent-mixed-stress-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "evaluator": str(SU2K_EVALUATOR.relative_to(REPO_ROOT)),
        "base_cases": [
            {
                "case_id": case["case_id"],
                "n_strands": case["n_strands"],
                "braid_word": list(case["braid_word"]),
                "framings": list(case["framings"]),
                "labels": [list(labels) for labels in case["labels"]],
                "moves": list(case["moves"]),
            }
            for case in BASE_CASES
        ],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_6_multicomponent_mixed_stress.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(REPO_ROOT),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_6_multicomponent_mixed_stress.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    output_path = args.output if args.output.is_absolute() else REPO_ROOT / args.output

    started_at = utc_now_iso()
    start = time.time()
    exact_output = run_suite()
    certificate = build_certificate(exact_output, output_path, started_at, time.time() - start)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(dumps_certificate(certificate))
    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {certificate['status']}")
    print(f"cases: {len(exact_output['case_outputs'])}")
    print(f"max_abs_difference: {exact_output['max_abs_difference']}")
    return 0 if certificate["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
