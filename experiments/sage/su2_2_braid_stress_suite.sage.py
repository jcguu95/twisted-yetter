"""Generate the first SU(2)_2 braid-oracle stress-test certificate.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_braid_stress_suite.sage.py

The suite checks presentation-level behavior of the experimental braid oracle:

* positive Markov stabilization of the right trefoil;
* negative Markov stabilization of the right trefoil;
* braid conjugation for a figure-eight braid representative;
* braid conjugation for the same representative with explicit +1 framing;
* split-union multiplicativity for trefoil union unknot.

This still does not prove the twisted Kirby formula.  It is a reproducible
stress-test layer between hand calculations and future arbitrary-link batches.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from itertools import product
from pathlib import Path
import subprocess
import sys
import time

from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"
DEFAULT_OUTPUT = REPO_ROOT / "experiments" / "results" / "sage-stress" / "su2-2-braid-stress-v1.json"

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402


def load_oracle():
    """Load the sibling oracle module from its file path."""

    spec = importlib.util.spec_from_file_location("su2_2_braid_oracle_runtime", ORACLE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run_suite(oracle):
    checks = [
        comparison_check(
            oracle,
            name="right-trefoil-positive-markov-stabilization",
            reason="closure(beta) equals closure(beta sigma_n)",
            left={"n_strands": 2, "braid_word": (1, 1, 1), "framings": (0,)},
            right={"n_strands": 3, "braid_word": (1, 1, 1, 2), "framings": (0,)},
        ),
        comparison_check(
            oracle,
            name="right-trefoil-negative-markov-stabilization",
            reason="closure(beta) equals closure(beta sigma_n^-1)",
            left={"n_strands": 2, "braid_word": (1, 1, 1), "framings": (0,)},
            right={"n_strands": 3, "braid_word": (1, 1, 1, -2), "framings": (0,)},
        ),
        comparison_check(
            oracle,
            name="figure-eight-braid-conjugation-zero-framing",
            reason="closure(beta) equals closure(alpha beta alpha^-1)",
            left={"n_strands": 3, "braid_word": (1, -2, 1, -2), "framings": (0,)},
            right={"n_strands": 3, "braid_word": (2, 1, -2, 1, -2, -2), "framings": (0,)},
        ),
        comparison_check(
            oracle,
            name="figure-eight-braid-conjugation-plus-one-framing",
            reason="same conjugation check with an explicit +1 component framing",
            left={"n_strands": 3, "braid_word": (1, -2, 1, -2), "framings": (1,)},
            right={"n_strands": 3, "braid_word": (2, 1, -2, 1, -2, -2), "framings": (1,)},
        ),
        split_union_multiplicativity_check(oracle),
    ]
    suite_status = "pass" if all(check["status"] == "pass" for check in checks) else "fail"
    return {
        "schema": "twisted-yetter.su2_2-braid-stress-suite.v1",
        "status": suite_status,
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "claim_boundary": (
            "experimental braid-closure oracle stress tests; not a full Kirby diagram "
            "parser, not a local ev/coev/R/F evaluator, and not a proof of the twisted formula"
        ),
        "check_count": len(checks),
        "checks": checks,
    }


def comparison_check(oracle, *, name, reason, left, right):
    left_component_count = len(oracle.component_data(left["n_strands"], left["braid_word"]).components)
    right_component_count = len(oracle.component_data(right["n_strands"], right["braid_word"]).components)
    if left_component_count != right_component_count:
        raise ValueError(f"{name}: compared braids have different component counts")

    comparisons = []
    for omega_labels in product((0, 1), repeat=left_component_count):
        left_value = oracle.omega_value(
            left["n_strands"],
            left["braid_word"],
            left["framings"],
            omega_labels,
        )
        right_value = oracle.omega_value(
            right["n_strands"],
            right["braid_word"],
            right["framings"],
            omega_labels,
        )
        comparisons.append(
            {
                "omega_labels": [int(label) for label in omega_labels],
                "left_value": oracle.cyclotomic_json(left_value),
                "right_value": oracle.cyclotomic_json(right_value),
                "status": "pass" if left_value == right_value else "fail",
            }
        )

    return {
        "name": name,
        "kind": "presentation-comparison",
        "reason": reason,
        "status": "pass" if all(item["status"] == "pass" for item in comparisons) else "fail",
        "left": _braid_payload(oracle, left),
        "right": _braid_payload(oracle, right),
        "comparisons": comparisons,
    }


def split_union_multiplicativity_check(oracle):
    trefoil = {"n_strands": 2, "braid_word": (1, 1, 1), "framings": (0,)}
    unknot = {"n_strands": 1, "braid_word": (), "framings": (0,)}
    split_union = {"n_strands": 3, "braid_word": (1, 1, 1), "framings": (0, 0)}

    comparisons = []
    for omega_labels in product((0, 1), repeat=2):
        trefoil_value = oracle.omega_value(
            trefoil["n_strands"],
            trefoil["braid_word"],
            trefoil["framings"],
            (omega_labels[0],),
        )
        unknot_value = oracle.omega_value(
            unknot["n_strands"],
            unknot["braid_word"],
            unknot["framings"],
            (omega_labels[1],),
        )
        split_value = oracle.omega_value(
            split_union["n_strands"],
            split_union["braid_word"],
            split_union["framings"],
            omega_labels,
        )
        product_value = trefoil_value * unknot_value
        comparisons.append(
            {
                "omega_labels": [int(label) for label in omega_labels],
                "trefoil_value": oracle.cyclotomic_json(trefoil_value),
                "unknot_value": oracle.cyclotomic_json(unknot_value),
                "product_value": oracle.cyclotomic_json(product_value),
                "split_union_value": oracle.cyclotomic_json(split_value),
                "status": "pass" if split_value == product_value else "fail",
            }
        )

    return {
        "name": "split-trefoil-unknot-multiplicativity",
        "kind": "split-union-multiplicativity",
        "reason": "RT link evaluation is multiplicative under split union",
        "status": "pass" if all(item["status"] == "pass" for item in comparisons) else "fail",
        "trefoil": _braid_payload(oracle, trefoil),
        "unknot": _braid_payload(oracle, unknot),
        "split_union": _braid_payload(oracle, split_union),
        "comparisons": comparisons,
    }


def _braid_payload(oracle, payload):
    diagnostics = oracle.describe_braid(payload["n_strands"], payload["braid_word"])
    diagnostics["framings"] = [int(framing) for framing in payload["framings"]]
    return diagnostics


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "su2-2-braid-stress-v1",
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "checks": [
            {
                "name": check["name"],
                "kind": check["kind"],
                "reason": check["reason"],
            }
            for check in exact_output["checks"]
        ],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_2_braid_stress_suite.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_braid_stress_suite.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "All displayed values are exact CyclotomicField(16) elements serialized without floats.",
            "Checks cover braid-presentation behavior and split multiplicativity, not Kirby moves.",
        ],
    )


def git_metadata():
    return {
        "commit": _run(["git", "rev-parse", "HEAD"]),
        "dirty": bool(_run(["git", "status", "--porcelain"])),
    }


def utc_now_iso():
    return _run(["date", "-u", "+%Y-%m-%dT%H:%M:%SZ"])


def _run(argv):
    return subprocess.run(
        argv,
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)

    started_at = utc_now_iso()
    start = time.monotonic()
    oracle = load_oracle()
    exact_output = run_suite(oracle)
    output_path = args.output if args.output.is_absolute() else REPO_ROOT / args.output
    certificate = build_certificate(exact_output, output_path, started_at, time.monotonic() - start)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(dumps_certificate(certificate))
    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {certificate['status']}")
    print(f"checks: {exact_output['check_count']}")


if __name__ == "__main__":
    main()
