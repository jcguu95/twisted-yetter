"""SU(2)_2 B2 explicit R/F backend with Omega expansion.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_rf_omega_backend.sage.py

This extends the B1' fixed all-sigma backend to the first usable Omega path.
For each fixed label assignment, it evaluates the sigma sublink by explicit
R/F contraction, handles the psi object as an invertible local sector, and then
sums the Omega_a expansion over all component labels.

The SU(2)_2 braid oracle is used only as an external comparison backend.
"""

from __future__ import annotations

import argparse
import importlib.util
from itertools import product
from pathlib import Path
import subprocess
import sys
import time

from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"
RF_BACKEND_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_rf_local_backend.sage.py"
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "local-piece"
    / "su2-2-rf-omega-backend-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402
from twisted_yetter.local_piece import braid_closure_linking_matrix, braid_program  # noqa: E402


LABEL_UNIT = 0
LABEL_SIGMA = 1
LABEL_PSI = 2
SIMPLE_LABELS = (LABEL_UNIT, LABEL_SIGMA, LABEL_PSI)
OMEGA_LABELS = (0, 1)
DEGREES = {LABEL_UNIT: 0, LABEL_SIGMA: 1, LABEL_PSI: 0}


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run_suite(oracle, rf):
    cases = example_cases()
    evaluations = [evaluate_case(oracle, rf, case) for case in cases]
    move_regressions = move_regression_cases(oracle, rf)
    status = "pass"
    if any(item["status"] != "pass" for item in evaluations):
        status = "fail"
    if any(item["status"] != "pass" for item in move_regressions):
        status = "fail"
    return {
        "schema": "twisted-yetter.su2_2-rf-omega-backend.v1",
        "status": status,
        "category_id": "SU(2)_2",
        "claim_level": "B2 explicit R/F backend with Omega expansion / supported braid closures",
        "scope": (
            "SU(2)_2 braid closures whose sigma sublink has at most three selected "
            "strands; fixed labels 0,sigma,psi; Omega_0/Omega_1 expansion; "
            "exact comparison against the braid oracle"
        ),
        "not_scope": (
            "arbitrary planar tensor graph, sigma sublinks needing more than three "
            "selected strands, generic mixed-label F/R path implementation, cup/cap "
            "programs, special/dotted links, closed 4-manifold normalization, or "
            "exotic-pair computation"
        ),
        "backend": {
            "rf_backend_script": str(RF_BACKEND_PATH.relative_to(REPO_ROOT)),
            "oracle_comparison_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
            "fixed_label_method": (
                "sigma sublink by explicit B1' R/F contraction; psi by invertible "
                "psi-sigma linking factor; component framings by twists"
            ),
            "omega_formula": "Omega_a = sum_i d_i (-1)^(a deg(i)) X_i",
        },
        "case_count": len(evaluations),
        "move_regression_count": len(move_regressions),
        "evaluations": evaluations,
        "move_regressions": move_regressions,
        "upstream_backend_artifacts": [
            "experiments/results/local-piece/su2-2-rf-local-backend-v1.json",
            "experiments/results/local-piece/su2-2-local-piece-evaluator-v1.json",
            "experiments/results/sage-stress/su2-2-braid-auto-stress-v1.json",
        ],
    }


def example_cases():
    return [
        {
            "case_id": "omega-cp2",
            "n_strands": 1,
            "braid_word": (),
            "framings": (1,),
            "omega_labels_to_check": [(0,), (1,)],
        },
        {
            "case_id": "omega-two-component-unlink",
            "n_strands": 2,
            "braid_word": (),
            "framings": (1, -1),
            "omega_labels_to_check": list(product(OMEGA_LABELS, repeat=2)),
        },
        {
            "case_id": "omega-positive-hopf",
            "n_strands": 2,
            "braid_word": (1, 1),
            "framings": (0, 0),
            "omega_labels_to_check": list(product(OMEGA_LABELS, repeat=2)),
        },
        {
            "case_id": "omega-right-trefoil",
            "n_strands": 2,
            "braid_word": (1, 1, 1),
            "framings": (0,),
            "omega_labels_to_check": [(0,), (1,)],
        },
        {
            "case_id": "omega-figure-eight",
            "n_strands": 3,
            "braid_word": (-1, 2, -1, 2),
            "framings": (0,),
            "omega_labels_to_check": [(0,), (1,)],
        },
        {
            "case_id": "omega-figure-eight-plus-one-framed",
            "n_strands": 3,
            "braid_word": (-1, 2, -1, 2),
            "framings": (1,),
            "omega_labels_to_check": [(0,), (1,)],
        },
    ]


def move_regression_cases(oracle, rf):
    return [
        compare_case_pair(
            oracle,
            rf,
            name="omega-r-r-inverse-cancellation",
            reason="local R followed by R^{-1} cancels for every Omega sector",
            left={"n_strands": 2, "braid_word": (), "framings": (0, 0)},
            right={"n_strands": 2, "braid_word": (1, -1), "framings": (0, 0)},
            omega_labels_to_check=list(product(OMEGA_LABELS, repeat=2)),
        ),
        compare_case_pair(
            oracle,
            rf,
            name="omega-trefoil-positive-markov",
            reason="closure(beta) equals closure(beta sigma_n)",
            left={"n_strands": 2, "braid_word": (1, 1, 1), "framings": (0,)},
            right={"n_strands": 3, "braid_word": (1, 1, 1, 2), "framings": (0,)},
            omega_labels_to_check=[(0,), (1,)],
        ),
        compare_case_pair(
            oracle,
            rf,
            name="omega-trefoil-negative-markov",
            reason="closure(beta) equals closure(beta sigma_n^-1)",
            left={"n_strands": 2, "braid_word": (1, 1, 1), "framings": (0,)},
            right={"n_strands": 3, "braid_word": (1, 1, 1, -2), "framings": (0,)},
            omega_labels_to_check=[(0,), (1,)],
        ),
        compare_case_pair(
            oracle,
            rf,
            name="omega-figure-eight-conjugation",
            reason="closure(beta) equals closure(alpha beta alpha^-1)",
            left={"n_strands": 3, "braid_word": (-1, 2, -1, 2), "framings": (0,)},
            right={"n_strands": 3, "braid_word": (1, -1, 2, -1, 2, -1), "framings": (0,)},
            omega_labels_to_check=[(0,), (1,)],
        ),
    ]


def evaluate_case(oracle, rf, case):
    fixed_label_checks = fixed_label_comparisons(oracle, rf, case)
    omega_checks = [
        omega_comparison(oracle, rf, case, omega_labels)
        for omega_labels in case["omega_labels_to_check"]
    ]
    return {
        "case_id": case["case_id"],
        "status": "pass"
        if all(item["status"] == "pass" for item in fixed_label_checks + omega_checks)
        else "fail",
        "local_piece_program": program_payload(case),
        "component_count": component_count(rf, case),
        "fixed_label_check_count": len(fixed_label_checks),
        "omega_check_count": len(omega_checks),
        "fixed_label_checks": fixed_label_checks,
        "omega_checks": omega_checks,
    }


def fixed_label_comparisons(oracle, rf, case):
    checks = []
    for labels in product(SIMPLE_LABELS, repeat=component_count(rf, case)):
        rf_value = explicit_fixed_value(rf, case["n_strands"], case["braid_word"], labels, case["framings"])
        oracle_value = oracle.fixed_label_rt_value(
            case["n_strands"],
            case["braid_word"],
            labels,
            case["framings"],
        )
        checks.append(
            {
                "labels": [int(label) for label in labels],
                "rf_value": rf.cyclotomic_json(rf_value),
                "oracle_value": oracle.cyclotomic_json(oracle_value),
                "difference": rf.cyclotomic_json(rf_value - oracle_value),
                "status": "pass" if rf_value == oracle_value else "fail",
            }
        )
    return checks


def omega_comparison(oracle, rf, case, omega_labels):
    rf_value = explicit_omega_value(
        rf,
        case["n_strands"],
        case["braid_word"],
        case["framings"],
        omega_labels,
    )
    oracle_value = oracle.omega_value(
        case["n_strands"],
        case["braid_word"],
        case["framings"],
        omega_labels,
    )
    return {
        "omega_labels": [int(label) for label in omega_labels],
        "rf_value": rf.cyclotomic_json(rf_value),
        "oracle_value": oracle.cyclotomic_json(oracle_value),
        "difference": rf.cyclotomic_json(rf_value - oracle_value),
        "status": "pass" if rf_value == oracle_value else "fail",
    }


def compare_case_pair(oracle, rf, *, name, reason, left, right, omega_labels_to_check):
    comparisons = []
    for omega_labels in omega_labels_to_check:
        left_rf = explicit_omega_value(rf, left["n_strands"], left["braid_word"], left["framings"], omega_labels)
        right_rf = explicit_omega_value(rf, right["n_strands"], right["braid_word"], right["framings"], omega_labels)
        left_oracle = oracle.omega_value(left["n_strands"], left["braid_word"], left["framings"], omega_labels)
        right_oracle = oracle.omega_value(right["n_strands"], right["braid_word"], right["framings"], omega_labels)
        comparisons.append(
            {
                "omega_labels": [int(label) for label in omega_labels],
                "left_rf_value": rf.cyclotomic_json(left_rf),
                "right_rf_value": rf.cyclotomic_json(right_rf),
                "left_oracle_value": oracle.cyclotomic_json(left_oracle),
                "right_oracle_value": oracle.cyclotomic_json(right_oracle),
                "rf_difference": rf.cyclotomic_json(left_rf - right_rf),
                "oracle_difference": oracle.cyclotomic_json(left_oracle - right_oracle),
                "status": "pass" if left_rf == right_rf == left_oracle == right_oracle else "fail",
            }
        )
    return {
        "name": name,
        "reason": reason,
        "status": "pass" if all(item["status"] == "pass" for item in comparisons) else "fail",
        "left": program_payload(left),
        "right": program_payload(right),
        "comparison_count": len(comparisons),
        "comparisons": comparisons,
    }


def explicit_omega_value(rf, n_strands, braid_word, framings, omega_labels):
    count = len(rf.closure_components(n_strands, braid_word))
    if len(omega_labels) != count:
        raise ValueError("Omega label count must match component count")
    total = rf.K(0)
    for labels in product(SIMPLE_LABELS, repeat=count):
        coefficient = rf.K(1)
        for omega_label, simple_label in zip(omega_labels, labels, strict=True):
            coefficient *= quantum_dimension(rf, simple_label) * character(rf, omega_label, simple_label)
        total += coefficient * explicit_fixed_value(rf, n_strands, braid_word, labels, framings)
    return rf.K(total)


def explicit_fixed_value(rf, n_strands, braid_word, labels, framings):
    components = rf.closure_components(n_strands, braid_word)
    if len(labels) != len(components):
        raise ValueError("label count must match component count")
    if len(framings) != len(components):
        raise ValueError("framing count must match component count")

    sigma_components = {index for index, label in enumerate(labels) if label == LABEL_SIGMA}
    sigma_strands = {
        strand
        for strand, component_index in enumerate(strand_to_component(components, n_strands))
        if component_index in sigma_components
    }
    sigma_value = sigma_sublink_value(rf, n_strands, braid_word, sigma_strands)
    psi_sigma_factor = psi_sigma_linking_factor(rf, n_strands, braid_word, labels)
    framing_factor = rf.K(1)
    for label, framing in zip(labels, framings, strict=True):
        framing_factor *= twist(rf, label) ** framing
    return rf.K(sigma_value * psi_sigma_factor * framing_factor)


def sigma_sublink_value(rf, n_strands, braid_word, sigma_strands):
    if not sigma_strands:
        return rf.K(1)
    subword, selected_count = selected_subbraid_word(n_strands, braid_word, sigma_strands)
    if selected_count > 3:
        raise ValueError("B2 backend supports sigma sublinks with at most three selected strands")
    return rf.rf_unframed_value(selected_count, subword)


def psi_sigma_linking_factor(rf, n_strands, braid_word, labels):
    linking = braid_closure_linking_matrix(n_strands, braid_word)
    exponent = 0
    for left, left_label in enumerate(labels):
        if left_label != LABEL_PSI:
            continue
        for right, right_label in enumerate(labels):
            if right_label == LABEL_SIGMA:
                exponent += linking[left][right]
    return rf.K(-1) ** exponent


def selected_subbraid_word(n_strands, braid_word, selected_strands):
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


def strand_to_component(components, n_strands):
    lookup = [0] * n_strands
    for component_index, component in enumerate(components):
        for strand in component:
            lookup[strand] = component_index
    return tuple(lookup)


def component_count(rf, case):
    return len(rf.closure_components(case["n_strands"], case["braid_word"]))


def quantum_dimension(rf, label):
    if label == LABEL_SIGMA:
        return rf.SQRT2
    if label in (LABEL_UNIT, LABEL_PSI):
        return rf.K(1)
    raise ValueError(f"unknown SU(2)_2 label: {label!r}")


def twist(rf, label):
    if label == LABEL_UNIT:
        return rf.K(1)
    if label == LABEL_SIGMA:
        return rf.SIGMA_TWIST
    if label == LABEL_PSI:
        return rf.ZETA**8
    raise ValueError(f"unknown SU(2)_2 label: {label!r}")


def character(rf, omega_label, simple_label):
    if omega_label not in OMEGA_LABELS:
        raise ValueError("SU(2)_2 Omega label must be 0 or 1")
    return rf.K(-1) if omega_label == 1 and DEGREES[simple_label] == 1 else rf.K(1)


def program_payload(case):
    count = len(load_rf_for_payload().closure_components(case["n_strands"], case["braid_word"]))
    program = braid_program(
        program_id=case.get("case_id", "rf-omega-case"),
        category_id="SU(2)_2",
        strand_count=case["n_strands"],
        braid_word=case["braid_word"],
        framings=case["framings"],
        omega_labels=(0,) * count,
    )
    return {
        "program": program.to_json(),
        "diagnostics": program.diagnostics(),
    }


_RF_PAYLOAD_CACHE = None


def load_rf_for_payload():
    global _RF_PAYLOAD_CACHE
    if _RF_PAYLOAD_CACHE is None:
        _RF_PAYLOAD_CACHE = load_module(RF_BACKEND_PATH, "su2_2_rf_backend_for_payload")
    return _RF_PAYLOAD_CACHE


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "su2-2-rf-omega-backend-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "rf_backend_script": str(RF_BACKEND_PATH.relative_to(REPO_ROOT)),
        "case_count": exact_output["case_count"],
        "move_regression_count": exact_output["move_regression_count"],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_2_rf_omega_backend.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_rf_omega_backend.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This is B2: explicit RF-backed fixed-label and Omega expansion for supported SU(2)_2 braid closures.",
            "The braid oracle is used only as an independent exact comparison backend.",
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
    oracle = load_module(ORACLE_PATH, "su2_2_braid_oracle_for_rf_omega")
    rf = load_module(RF_BACKEND_PATH, "su2_2_rf_backend_for_rf_omega")
    exact_output = run_suite(oracle, rf)
    certificate = build_certificate(exact_output, output_path, started_at, time.time() - start)
    output_path.write_text(dumps_certificate(certificate))

    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {exact_output['status']}")
    print(f"cases: {exact_output['case_count']}")
    print(f"move regressions: {exact_output['move_regression_count']}")

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
