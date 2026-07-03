"""SU(2)_6 fusion-braid evaluator calibration gate.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_6_fusion_braid_calibration.sage.py

This is a narrow admission test for the mixed-color SU(2)_k fusion-braid
evaluator at k=6.  It deliberately avoids Yasui inputs.  The goal is to check
that the new evaluator agrees with independent/simple controls first:

* framed unknots and split unlinks;
* positive Hopf links against the modular S-matrix formula;
* one-component braid knots against Sage colored Jones with the label-parity
  q-convention calibrated to the fusion-braid evaluator.

This artifact is not an exotic-pair computation and not an arbitrary MTC
evaluator certificate.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from itertools import product
from pathlib import Path
import sys
import time

from sage.all import ComplexField, CyclotomicField
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "sage-stress"
    / "su2-6-fusion-braid-calibration-v1.json"
)
SU2K_EVALUATOR = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
SU2_6_STRESS = REPO_ROOT / "experiments" / "sage" / "su2_6_kirby_slide_stress.sage.py"

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402
from twisted_yetter.artifacts import git_metadata, utc_now_iso  # noqa: E402


LEVEL = 6
ROOT_ORDER = 32
FIELD = CyclotomicField(ROOT_ORDER)
A_ROOT = FIELD.gen()
CF = ComplexField(160)
LABELS = tuple(range(LEVEL + 1))
TOLERANCE = CF("1e-10")


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def run_suite():
    su2k = load_module(SU2K_EVALUATOR, "su2k_fusion_braid_evaluator_for_su2_6_calibration")
    stress = load_module(SU2_6_STRESS, "su2_6_kirby_slide_stress_for_calibration")
    evaluator = su2k.SU2KBraidEvaluator(6, exact=False, precision=160)

    groups = [
        fixed_unknot_controls(evaluator),
        split_unlink_controls(evaluator),
        hopf_controls(evaluator),
        knot_colored_jones_controls(evaluator, stress),
        omega_controls(evaluator, stress),
    ]
    all_rows = [row for group in groups for row in group["sample_failures"]]
    status = "pass" if all(group["status"] == "pass" for group in groups) else "fail"
    max_abs_difference = max(CF(group["max_abs_difference"]) for group in groups)
    return {
        "schema": "twisted-yetter.su2-6-fusion-braid-calibration.v1",
        "status": status,
        "category_id": "SU(2)_6",
        "claim_level": "calibration evidence for repo-local SU(2)_6 fusion-braid evaluator",
        "scope": (
            "framed unknots, split unlinks, positive Hopf links, and "
            "one-component braid knots compared against modular-data or "
            "Sage-colored-Jones controls"
        ),
        "not_scope": (
            "Yasui diagram admission, exotic-pair computation, arbitrary MTC evaluator, "
            "dotted/special links, or closed 4-manifold normalization"
        ),
        "tolerance": str(TOLERANCE),
        "max_abs_difference": str(max_abs_difference),
        "control_groups": groups,
        "sample_failures": all_rows,
        "convention_notes": [
            "SU(2)_6 Hopf values are compared to S_ij/S_00 with ordinary RT normalization.",
            "Sage colored Jones uses q=A^4 for even simple labels and q=A^-4 for odd simple labels in this calibration.",
            "The SU(2)_2 degree-linking phase in su2k_fusion_braid_evaluator is a repo-local oracle convention and is not applied at level 6.",
        ],
    }


def fixed_unknot_controls(evaluator):
    rows = []
    for label, framing in product(LABELS, (-2, -1, 0, 1, 2)):
        expected = dimension(label) * twist(label) ** framing
        actual = evaluator.fixed_label_value(1, (), (label,), (framing,))
        rows.append(compare_row("fixed_unknot", [label], [framing], actual, expected))
    return group_summary("fixed_unknot", rows)


def split_unlink_controls(evaluator):
    rows = []
    for labels in product(LABELS, repeat=2):
        for framings in ((0, 0), (1, -1)):
            expected = (
                dimension(labels[0])
                * twist(labels[0]) ** framings[0]
                * dimension(labels[1])
                * twist(labels[1]) ** framings[1]
            )
            actual = evaluator.fixed_label_value(2, (), labels, framings)
            rows.append(compare_row("split_unlink", labels, framings, actual, expected))
    return group_summary("split_unlink", rows)


def hopf_controls(evaluator):
    rows = []
    for labels in product(LABELS, repeat=2):
        for framings in ((0, 0), (1, -1)):
            expected = (
                hopf_value(labels[0], labels[1])
                * twist(labels[0]) ** framings[0]
                * twist(labels[1]) ** framings[1]
            )
            actual = evaluator.fixed_label_value(2, (1, 1), labels, framings)
            rows.append(compare_row("positive_hopf", labels, framings, actual, expected))
    return group_summary("positive_hopf", rows)


def knot_colored_jones_controls(evaluator, stress):
    rows = []
    for knot in stress.KNOT_CASES:
        knot_values = stress.colored_jones_root_values(knot)
        for label in LABELS:
            expected = stress.framed_knot_value(knot, label, knot["knot_framing"], knot_values)
            actual = evaluator.fixed_label_value(
                knot["n_strands"],
                knot["braid_word"],
                (label,),
                (knot["knot_framing"],),
            )
            row = compare_row(
                f"knot:{knot['name']}",
                [label],
                [knot["knot_framing"]],
                actual,
                expected,
            )
            row["braid_word"] = [int(generator) for generator in knot["braid_word"]]
            row["n_strands"] = int(knot["n_strands"])
            row["jones_q_convention"] = "A^-4 for odd label, A^4 for even label"
            rows.append(row)
    return group_summary("one_component_braid_knot", rows)


def omega_controls(evaluator, stress):
    rows = []
    for omega_label in (0, 1):
        expected = sum(
            omega_coefficient(omega_label, label) * dimension(label) * twist(label)
            for label in LABELS
        )
        actual = evaluator.omega_value(1, (), (1,), (omega_label,))
        rows.append(compare_row("omega_framed_unknot_plus_one", [omega_label], [1], actual, expected))

    for omega_labels in product((0, 1), repeat=2):
        expected = sum(
            omega_coefficient(omega_labels[0], left)
            * omega_coefficient(omega_labels[1], right)
            * hopf_value(left, right)
            for left, right in product(LABELS, repeat=2)
        )
        actual = evaluator.omega_value(2, (1, 1), (0, 0), omega_labels)
        rows.append(compare_row("omega_positive_hopf_zero_framed", omega_labels, [0, 0], actual, expected))

    trefoil = stress.KNOT_CASES[0]
    knot_values = stress.colored_jones_root_values(trefoil)
    for omega_label in (0, 1):
        expected = sum(
            omega_coefficient(omega_label, label)
            * stress.framed_knot_value(trefoil, label, trefoil["knot_framing"], knot_values)
            for label in LABELS
        )
        actual = evaluator.omega_value(
            trefoil["n_strands"],
            trefoil["braid_word"],
            (trefoil["knot_framing"],),
            (omega_label,),
        )
        rows.append(compare_row("omega_right_trefoil", [omega_label], [trefoil["knot_framing"]], actual, expected))
    return group_summary("omega_expansion", rows)


def compare_row(kind, labels, framings, actual, expected):
    actual_cf = CF(actual)
    expected_cf = CF(expected)
    difference = actual_cf - expected_cf
    abs_difference = abs(difference)
    return {
        "kind": kind,
        "labels": [int(label) for label in labels],
        "framings": [int(framing) for framing in framings],
        "actual": complex_json(actual_cf),
        "expected": complex_json(expected_cf),
        "difference": complex_json(difference),
        "abs_difference": str(abs_difference),
        "status": "pass" if abs_difference < TOLERANCE else "fail",
    }


def group_summary(name, rows):
    failures = [row for row in rows if row["status"] != "pass"]
    max_abs_difference = max(CF(row["abs_difference"]) for row in rows) if rows else CF(0)
    return {
        "name": name,
        "status": "pass" if not failures else "fail",
        "control_count": len(rows),
        "max_abs_difference": str(max_abs_difference),
        "sample_failures": failures[:10],
    }


def dimension(label):
    return FIELD(q_sine(label + 1) / q_sine(1))


def twist(label):
    return FIELD(A_ROOT ** (label * (label + 2)))


def hopf_value(left, right):
    return FIELD(q_sine((left + 1) * (right + 1)) / q_sine(1))


def omega_coefficient(omega_label, simple_label):
    return FIELD(dimension(simple_label) * ((-1) ** (omega_label * (simple_label % 2))))


def q_sine(multiplier):
    return FIELD((A_ROOT ** (2 * multiplier) - A_ROOT ** (-2 * multiplier)) / (A_ROOT**2 - A_ROOT**(-2)))


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
        "suite": "su2-6-fusion-braid-calibration-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "evaluator": str(SU2K_EVALUATOR.relative_to(REPO_ROOT)),
        "colored_jones_source": str(SU2_6_STRESS.relative_to(REPO_ROOT)),
        "level": LEVEL,
        "root_order": ROOT_ORDER,
        "labels": list(LABELS),
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_6_fusion_braid_calibration.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(REPO_ROOT),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION, "numpy_backend": "enabled for exact=False"},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_6_fusion_braid_calibration.sage.py '
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
    print(f"max_abs_difference: {exact_output['max_abs_difference']}")
    return 0 if certificate["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
