"""SU(2)_2 B0 local-piece evaluator backend.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_local_piece_evaluator.sage.py

This is the first executable local-piece evaluator slice.  It supports local
braid-crossing pieces, composes them into a braid word, closes the braid, and
dispatches to the already-tested SU(2)_2 braid oracle for exact values.

It is not yet a full planar F/R/eval/coeval tensor-network evaluator.  The
point of this script is to create a stable API and regression artifact for the
braided local-piece layer that later cup/cap and F/R evaluators can extend.
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
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "local-piece"
    / "su2-2-local-piece-evaluator-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402
from twisted_yetter.local_piece import braid_program  # noqa: E402


def load_oracle():
    spec = importlib.util.spec_from_file_location("su2_2_braid_oracle_runtime", ORACLE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run_suite(oracle):
    programs = example_programs()
    evaluations = [evaluate_program(oracle, program) for program in programs]
    move_regressions = local_move_regressions(oracle)
    status = "pass"
    if any(item["status"] != "pass" for item in evaluations):
        status = "fail"
    if any(item["status"] != "pass" for item in move_regressions):
        status = "fail"
    return {
        "schema": "twisted-yetter.su2_2-local-piece-evaluator.v1",
        "status": status,
        "category_id": "SU(2)_2",
        "claim_level": "B0 executable local-piece evaluator / braid-closure slice",
        "scope": (
            "local braid-crossing pieces, braid-word composition, braid closure, "
            "exact SU(2)_2 fixed-label and Omega evaluation through the existing "
            "braid oracle"
        ),
        "not_scope": (
            "arbitrary planar tensor graph, cup/cap evaluator, trivalent vertices, "
            "general F/R recoupling backend, special/dotted links, closed "
            "4-manifold normalization, or exotic-pair computation"
        ),
        "backend": {
            "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
            "oracle_schema": "twisted-yetter.su2_2-braid-oracle.v1",
            "local_piece_schema": "twisted-yetter.local-piece-program.v1",
        },
        "supported_piece_kinds": ["braid_crossing"],
        "next_piece_kinds": ["cup", "cap", "trivalent_split", "trivalent_merge"],
        "program_count": len(evaluations),
        "move_regression_count": len(move_regressions),
        "evaluations": evaluations,
        "move_regressions": move_regressions,
        "upstream_regression_artifacts": [
            "experiments/results/sage-stress/su2-2-braid-stress-v1.json",
            "experiments/results/sage-stress/su2-2-braid-auto-stress-v1.json",
            "experiments/results/sage-stress/su2-6-kirby-slide-stress-v1.json",
            "experiments/results/sage-stress/su2-6-nontrivial-slide-stress-v1.json",
            "experiments/results/mtc-candidates/su3-3-multiplicity-stress-v1.json",
        ],
    }


def example_programs():
    return [
        braid_program(
            program_id="lp-cp2-omega0-fixed-psi",
            category_id="SU(2)_2",
            strand_count=1,
            braid_word=(),
            framings=(1,),
            omega_labels=(0,),
            fixed_labels=(2,),
            description="One +1 framed unknot, represented as empty one-strand braid closure.",
        ),
        braid_program(
            program_id="lp-unlink-two-components",
            category_id="SU(2)_2",
            strand_count=2,
            braid_word=(),
            framings=(1, -1),
            omega_labels=(0, 1),
            fixed_labels=(0, 2),
            description="Two-component split unlink as empty two-strand braid closure.",
        ),
        braid_program(
            program_id="lp-positive-hopf",
            category_id="SU(2)_2",
            strand_count=2,
            braid_word=(1, 1),
            framings=(0, 0),
            omega_labels=(0, 1),
            fixed_labels=(1, 2),
            description="Positive Hopf link as two positive local crossing pieces.",
        ),
        braid_program(
            program_id="lp-right-trefoil",
            category_id="SU(2)_2",
            strand_count=2,
            braid_word=(1, 1, 1),
            framings=(0,),
            omega_labels=(1,),
            fixed_labels=(1,),
            description="Right trefoil as closure of sigma_1^3.",
        ),
        braid_program(
            program_id="lp-figure-eight",
            category_id="SU(2)_2",
            strand_count=3,
            braid_word=(-1, 2, -1, 2),
            framings=(0,),
            omega_labels=(0,),
            fixed_labels=(1,),
            description="Figure-eight knot as a three-strand braid closure.",
        ),
    ]


def evaluate_program(oracle, program):
    oracle_payload = program.to_oracle_payload()
    oracle_output = oracle.evaluate_payload(oracle_payload)
    return {
        "status": oracle_output["status"],
        "program": program.to_json(),
        "diagnostics": program.diagnostics(),
        "oracle_payload": oracle_payload,
        "oracle_output": oracle_output,
        "evaluation_path": [
            "validate local-piece program",
            "compose braid_crossing pieces into braid word",
            "close braid and compute component ordering",
            "dispatch to SU(2)_2 exact braid oracle",
        ],
    }


def local_move_regressions(oracle):
    return [
        compare_programs(
            oracle,
            name="r-r-inverse-cancellation-two-strand-unlink",
            reason="local R followed by R^{-1} cancels before braid closure",
            left=braid_program(
                program_id="lp-r-rinv-left",
                category_id="SU(2)_2",
                strand_count=2,
                braid_word=(),
                framings=(0, 0),
                omega_labels=(0, 1),
                fixed_labels=(1, 2),
            ),
            right=braid_program(
                program_id="lp-r-rinv-right",
                category_id="SU(2)_2",
                strand_count=2,
                braid_word=(1, -1),
                framings=(0, 0),
                omega_labels=(0, 1),
                fixed_labels=(1, 2),
            ),
        ),
        compare_one_component_all_sectors(
            oracle,
            name="trefoil-positive-markov-stabilization",
            reason="closure(beta) equals closure(beta sigma_n)",
            left_word=(1, 1, 1),
            right_strand_count=3,
            right_word=(1, 1, 1, 2),
        ),
        compare_one_component_all_sectors(
            oracle,
            name="trefoil-negative-markov-stabilization",
            reason="closure(beta) equals closure(beta sigma_n^-1)",
            left_word=(1, 1, 1),
            right_strand_count=3,
            right_word=(1, 1, 1, -2),
        ),
        compare_one_component_all_sectors(
            oracle,
            name="trefoil-braid-conjugation",
            reason="closure(beta) equals closure(alpha beta alpha^-1)",
            left_word=(1, 1, 1),
            right_strand_count=2,
            right_word=(1, 1, 1, 1, -1),
        ),
    ]


def compare_programs(oracle, name, reason, left, right):
    left_eval = evaluate_program(oracle, left)
    right_eval = evaluate_program(oracle, right)
    fixed_ok = (
        left_eval["oracle_output"].get("fixed_label_rt_value")
        == right_eval["oracle_output"].get("fixed_label_rt_value")
    )
    omega_ok = left_eval["oracle_output"]["omega_value"] == right_eval["oracle_output"]["omega_value"]
    return {
        "name": name,
        "reason": reason,
        "kind": "local-piece-program-equivalence",
        "left": left_eval,
        "right": right_eval,
        "checks": {
            "fixed_label_rt_value": "pass" if fixed_ok else "fail",
            "omega_value": "pass" if omega_ok else "fail",
        },
        "status": "pass" if fixed_ok and omega_ok else "fail",
    }


def compare_one_component_all_sectors(
    oracle,
    *,
    name,
    reason,
    left_word,
    right_strand_count,
    right_word,
):
    sector_checks = []
    for framing, omega_label in product((0, 1), (0, 1)):
        left = braid_program(
            program_id=f"{name}-left-f{framing}-a{omega_label}",
            category_id="SU(2)_2",
            strand_count=2,
            braid_word=left_word,
            framings=(framing,),
            omega_labels=(omega_label,),
            fixed_labels=(1,),
        )
        right = braid_program(
            program_id=f"{name}-right-f{framing}-a{omega_label}",
            category_id="SU(2)_2",
            strand_count=right_strand_count,
            braid_word=right_word,
            framings=(framing,),
            omega_labels=(omega_label,),
            fixed_labels=(1,),
        )
        comparison = compare_programs(oracle, f"{name}-f{framing}-a{omega_label}", reason, left, right)
        sector_checks.append(
            {
                "framing": int(framing),
                "omega_label": int(omega_label),
                "fixed_label": 1,
                "status": comparison["status"],
                "checks": comparison["checks"],
                "left_value": comparison["left"]["oracle_output"]["omega_value"],
                "right_value": comparison["right"]["oracle_output"]["omega_value"],
                "left_fixed_label_value": comparison["left"]["oracle_output"]["fixed_label_rt_value"],
                "right_fixed_label_value": comparison["right"]["oracle_output"]["fixed_label_rt_value"],
            }
        )
    return {
        "name": name,
        "reason": reason,
        "kind": "one-component-all-sector-local-piece-equivalence",
        "sector_check_count": len(sector_checks),
        "sector_checks": sector_checks,
        "status": "pass" if all(item["status"] == "pass" for item in sector_checks) else "fail",
    }


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "su2-2-local-piece-evaluator-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "program_count": exact_output["program_count"],
        "move_regression_count": exact_output["move_regression_count"],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_2_local_piece_evaluator.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_local_piece_evaluator.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This is B0: executable braid-closure local-piece evaluator plumbing.",
            "It uses the SU(2)_2 braid oracle as exact backend and does not claim full planar F/R support.",
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
    oracle = load_oracle()
    exact_output = run_suite(oracle)
    certificate = build_certificate(exact_output, output_path, started_at, time.time() - start)
    output_path.write_text(dumps_certificate(certificate))

    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {exact_output['status']}")
    print(f"programs: {exact_output['program_count']}")
    print(f"move regressions: {exact_output['move_regression_count']}")

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
