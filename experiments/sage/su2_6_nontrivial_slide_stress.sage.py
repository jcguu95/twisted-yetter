"""SU(2)_6 nontrivial-over-nontrivial Kirby-slide stress suite.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_6_nontrivial_slide_stress.sage.py

This suite checks a more difficult bounded handle-slide class than the
meridian-link suite:

* before: two split nontrivial knot components K and L, colored by Omega_a and
  Omega_b;
* move: slide K over L;
* after: the part running along L is a parallel-copy cable with labels i and j,
  decomposed by SU(2)_6 fusion rules.

For fixed labels i,j, the after value used here is

    (RT_i(K) / d_i) * sum_k N_{ij}^k RT_k(L).

The division by d_i is the connected-sum normalization for the slid component.
This is not a general multi-component colored-link evaluator; it is a
parallel-copy / fusion-channel evaluator for split nontrivial-over-nontrivial
slides.
"""

from __future__ import annotations

import argparse
from itertools import product
from pathlib import Path
import subprocess
import sys
import time

from sage.all import BraidGroup, CyclotomicField, ZZ
from sage.env import SAGE_VERSION
from sage.knots.all import Link


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "sage-stress"
    / "su2-6-nontrivial-slide-stress-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402


LEVEL = 6
ROOT_ORDER = 32
FIELD = CyclotomicField(ROOT_ORDER)
A_ROOT = FIELD.gen()
JONES_Q = A_ROOT**4
LABELS = tuple(range(LEVEL + 1))


KNOT_CASES = [
    {"name": "right_trefoil", "n_strands": 2, "braid_word": (1, 1, 1)},
    {"name": "figure_eight", "n_strands": 3, "braid_word": (-1, 2, -1, 2)},
    {"name": "torus_2_5", "n_strands": 2, "braid_word": (1, 1, 1, 1, 1)},
]

FRAMING_CASES = [
    {"k_framing": 0, "l_framing": 0},
    {"k_framing": 1, "l_framing": 0},
    {"k_framing": 0, "l_framing": 1},
    {"k_framing": 0, "l_framing": -1},
    {"k_framing": 1, "l_framing": -1},
]


def run_suite():
    validate_knot_inputs()
    cache = {}
    comparisons = []
    for k_case in KNOT_CASES:
        k_values = cached_colored_jones_root_values(cache, k_case)
        for l_case in KNOT_CASES:
            l_values = cached_colored_jones_root_values(cache, l_case)
            for framing in FRAMING_CASES:
                comparisons.extend(
                    slide_pair_comparisons(k_case, l_case, framing, k_values, l_values)
                )

    status = "pass" if all(item["status"] == "pass" for item in comparisons) else "fail"
    return {
        "schema": "twisted-yetter.su2-6-nontrivial-slide-stress.v1",
        "status": status,
        "category_id": "SU(2)_6",
        "claim_level": (
            "computed nontrivial-over-nontrivial Kirby-slide evidence for "
            "parallel-copy fusion class / not arbitrary evaluator"
        ),
        "scope": (
            "split nontrivial knot K slid over split nontrivial knot L; after "
            "diagram evaluated by connected-sum normalization and SU(2)_6 "
            "fusion decomposition of the parallel copy along L"
        ),
        "not_scope": (
            "arbitrary linked starting diagrams, arbitrary band placement, arbitrary "
            "multi-component colored link evaluator, full F/R tensor-network evaluator, "
            "dotted/special links, closed 4-manifold normalization, or exotic-pair computation"
        ),
        "formula": {
            "before_fixed_labels": "RT_i(K,fK) * RT_j(L,fL)",
            "after_fixed_labels": "(RT_i(K,fK)/d_i) * sum_k N_ij^k RT_k(L,fL)",
            "omega_label_transform": "a,b -> a+b mod 2, b",
        },
        "knot_count": len(KNOT_CASES),
        "framing_case_count": len(FRAMING_CASES),
        "unique_colored_jones_braid_count": len(cache),
        "comparison_count": len(comparisons),
        "comparisons": comparisons,
    }


def slide_pair_comparisons(k_case, l_case, framing, k_values, l_values):
    comparisons = []
    for omega_k, omega_l in product((0, 1), repeat=2):
        before = before_pair_value(k_values, l_values, framing, omega_k, omega_l)
        after = after_pair_value(k_values, l_values, framing, omega_k, omega_l)
        comparisons.append(
            {
                "name": (
                    f"{k_case['name']}_over_{l_case['name']}"
                    f"::fK={framing['k_framing']},fL={framing['l_framing']}"
                    f"::omega={omega_k},{omega_l}"
                ),
                "knot_slid": knot_payload(k_case, framing["k_framing"]),
                "knot_slid_over": knot_payload(l_case, framing["l_framing"]),
                "omega_labels_before": [int(omega_k), int(omega_l)],
                "omega_labels_after": [int((omega_k + omega_l) % 2), int(omega_l)],
                "before_value": cyclotomic_json(before),
                "after_value": cyclotomic_json(after),
                "difference": cyclotomic_json(before - after),
                "status": "pass" if before == after else "fail",
            }
        )
    return comparisons


def before_pair_value(k_values, l_values, framing, omega_k, omega_l):
    return FIELD(
        sum(
            omega_coefficient(omega_k, i) * framed_knot_value(k_values, i, framing["k_framing"])
            for i in LABELS
        )
        * sum(
            omega_coefficient(omega_l, j) * framed_knot_value(l_values, j, framing["l_framing"])
            for j in LABELS
        )
    )


def after_pair_value(k_values, l_values, framing, omega_k, omega_l):
    transformed_omega_k = (omega_k + omega_l) % 2
    total = FIELD(0)
    for i in LABELS:
        k_factor = (
            omega_coefficient(transformed_omega_k, i)
            * framed_knot_value(k_values, i, framing["k_framing"])
            / dimension(i)
        )
        for j in LABELS:
            l_parallel = sum(
                framed_knot_value(l_values, k, framing["l_framing"])
                for k in fusion_outputs(i, j)
            )
            total += omega_coefficient(omega_l, j) * k_factor * l_parallel
    return FIELD(total)


def colored_jones_root_values(knot):
    braid_group = BraidGroup(knot["n_strands"])
    braid = braid_group(list(knot["braid_word"]))
    return {
        label: FIELD(braid.colored_jones_polynomial(label + 1)(JONES_Q))
        for label in LABELS
    }


def cached_colored_jones_root_values(cache, knot):
    key = (int(knot["n_strands"]), tuple(int(generator) for generator in knot["braid_word"]))
    if key not in cache:
        cache[key] = colored_jones_root_values(knot)
    return cache[key]


def framed_knot_value(knot_values, label, framing):
    return FIELD(dimension(label) * knot_values[label] * twist(label) ** framing)


def omega_coefficient(omega_label, simple_label):
    return FIELD(dimension(simple_label) * ((-1) ** (omega_label * degree(simple_label))))


def fusion_outputs(left, right):
    lower = abs(left - right)
    upper = min(left + right, 2 * LEVEL - left - right)
    return tuple(
        label
        for label in range(lower, upper + 1)
        if (left + right + label) % 2 == 0
    )


def validate_knot_inputs():
    for knot in KNOT_CASES:
        braid_group = BraidGroup(knot["n_strands"])
        braid = braid_group(list(knot["braid_word"]))
        component_count = Link(braid).number_of_components()
        if component_count != 1:
            raise ValueError(f"{knot['name']} closure must be a knot, got {component_count} components")


def knot_payload(knot, framing):
    return {
        "name": knot["name"],
        "n_strands": int(knot["n_strands"]),
        "braid_word": [int(generator) for generator in knot["braid_word"]],
        "framing": int(framing),
    }


def dimension(label):
    return FIELD(q_sine(label + 1) / q_sine(1))


def twist(label):
    return FIELD(A_ROOT ** (label * (label + 2)))


def degree(label):
    return label % 2


def q_sine(multiplier):
    return FIELD((A_ROOT ** (2 * multiplier) - A_ROOT ** (-2 * multiplier)) / (A_ROOT**2 - A_ROOT**(-2)))


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
        "suite": "su2-6-nontrivial-slide-stress-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "knot_cases": [knot_payload(knot, 0) for knot in KNOT_CASES],
        "framing_cases": FRAMING_CASES,
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_6_nontrivial_slide_stress.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_6_nontrivial_slide_stress.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This is a SU(2)_6 nontrivial-over-nontrivial slide suite for a parallel-copy fusion class.",
            "It is not an arbitrary colored-link or closed-four-manifold evaluator.",
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
    print(f"knots: {exact_output['knot_count']}")
    print(f"framing cases: {exact_output['framing_case_count']}")
    print(f"comparisons: {exact_output['comparison_count']}")

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
