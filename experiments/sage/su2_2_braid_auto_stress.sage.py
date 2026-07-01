"""Automatic small-braid stress tests for the SU(2)_2 braid oracle.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_braid_auto_stress.sage.py

This script broadens the hand-picked stress suite by generating a deterministic
set of small one-component braid closures and checking exact Omega_a values
under:

* positive Markov stabilization;
* negative Markov stabilization;
* braid conjugation by each elementary generator.

Scope boundary: only one-component closures are tested here.  This avoids
component-ordering ambiguities for Omega labels; multi-component label
permutation checks should be a separate suite.
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
DEFAULT_OUTPUT = REPO_ROOT / "experiments" / "results" / "sage-stress" / "su2-2-braid-auto-stress-v1.json"

MAX_WORD_LENGTH_BY_STRANDS = {2: 5, 3: 4}
MAX_CASES = 48
FRAMINGS = (0, 1)
OMEGA_LABELS = (0, 1)
SIMPLE_LABELS = (0, 1, 2)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402


def load_oracle():
    spec = importlib.util.spec_from_file_location("su2_2_braid_oracle_runtime", ORACLE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def generated_base_cases(oracle):
    """Return deterministic one-component braid closures."""

    cases = []
    for n_strands, max_length in MAX_WORD_LENGTH_BY_STRANDS.items():
        alphabet = tuple(range(1, n_strands)) + tuple(range(-1, -n_strands, -1))
        for length in range(1, max_length + 1):
            for word in product(alphabet, repeat=length):
                if _has_immediate_cancellation(word):
                    continue
                data = oracle.component_data(n_strands, word)
                if len(data.components) != 1:
                    continue
                cases.append(
                    {
                        "case_id": f"B{n_strands}-L{length}-" + ".".join(_generator_token(g) for g in word),
                        "n_strands": n_strands,
                        "braid_word": tuple(word),
                    }
                )
    return cases[:MAX_CASES]


def run_suite(oracle):
    cases = []
    total_move_checks = 0
    total_sector_checks = 0

    for base in generated_base_cases(oracle):
        case_moves = []
        for framing in FRAMINGS:
            moves = move_payloads(base)
            for move in moves:
                result = compare_move(oracle, base, move, framing)
                case_moves.append(result)
                total_move_checks += 1
                total_sector_checks += (
                    len(result["omega_sectors"]) + len(result["fixed_label_sectors"])
                )
        cases.append(
            {
                "case_id": base["case_id"],
                "base": _braid_payload(oracle, base["n_strands"], base["braid_word"]),
                "moves": case_moves,
                "status": "pass" if all(move["status"] == "pass" for move in case_moves) else "fail",
            }
        )

    status = "pass" if all(case["status"] == "pass" for case in cases) else "fail"
    return {
        "schema": "twisted-yetter.su2_2-braid-auto-stress-suite.v1",
        "status": status,
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "scope": (
            "deterministic small one-component braid closures; exact fixed-label "
            "and Omega_0/Omega_1 checks under Markov stabilization and braid conjugation"
        ),
        "not_scope": (
            "multi-component Omega-label permutation, arbitrary planar local-piece evaluator, "
            "Kirby handle-slide proof, special-link/dotted-component evaluation"
        ),
        "generation": {
            "max_word_length_by_strands": {
                str(key): value for key, value in MAX_WORD_LENGTH_BY_STRANDS.items()
            },
            "max_cases": MAX_CASES,
            "framings": list(FRAMINGS),
            "omega_labels": list(OMEGA_LABELS),
            "simple_labels": list(SIMPLE_LABELS),
            "filters": [
                "no immediate generator cancellation",
                "closure has exactly one component",
            ],
        },
        "case_count": len(cases),
        "move_check_count": total_move_checks,
        "sector_check_count": total_sector_checks,
        "cases": cases,
    }


def move_payloads(base):
    n_strands = base["n_strands"]
    word = base["braid_word"]
    moves = [
        {
            "name": "markov-positive",
            "kind": "markov-stabilization",
            "reason": "closure(beta) equals closure(beta sigma_n)",
            "n_strands": n_strands + 1,
            "braid_word": word + (n_strands,),
        },
        {
            "name": "markov-negative",
            "kind": "markov-stabilization",
            "reason": "closure(beta) equals closure(beta sigma_n^-1)",
            "n_strands": n_strands + 1,
            "braid_word": word + (-n_strands,),
        },
    ]
    for generator in range(1, n_strands):
        for sign in (1, -1):
            conjugator = sign * generator
            moves.append(
                {
                    "name": f"conjugation-{_generator_token(conjugator)}",
                    "kind": "braid-conjugation",
                    "reason": "closure(beta) equals closure(alpha beta alpha^-1)",
                    "n_strands": n_strands,
                    "braid_word": (conjugator,) + word + (-conjugator,),
                }
            )
    return moves


def compare_move(oracle, base, move, framing):
    base_components = oracle.component_data(base["n_strands"], base["braid_word"]).components
    moved_components = oracle.component_data(move["n_strands"], move["braid_word"]).components
    if len(base_components) != 1 or len(moved_components) != 1:
        raise ValueError("auto stress suite expects one-component closures before and after moves")

    omega_sectors = []
    for omega_label in OMEGA_LABELS:
        left_value = oracle.omega_value(
            base["n_strands"],
            base["braid_word"],
            (framing,),
            (omega_label,),
        )
        right_value = oracle.omega_value(
            move["n_strands"],
            move["braid_word"],
            (framing,),
            (omega_label,),
        )
        omega_sectors.append(
            {
                "omega_label": int(omega_label),
                "left_value": oracle.cyclotomic_json(left_value),
                "right_value": oracle.cyclotomic_json(right_value),
                "status": "pass" if left_value == right_value else "fail",
            }
        )

    fixed_label_sectors = []
    for simple_label in SIMPLE_LABELS:
        left_value = oracle.fixed_label_rt_value(
            base["n_strands"],
            base["braid_word"],
            (simple_label,),
            (framing,),
        )
        right_value = oracle.fixed_label_rt_value(
            move["n_strands"],
            move["braid_word"],
            (simple_label,),
            (framing,),
        )
        fixed_label_sectors.append(
            {
                "simple_label": int(simple_label),
                "left_value": oracle.cyclotomic_json(left_value),
                "right_value": oracle.cyclotomic_json(right_value),
                "status": "pass" if left_value == right_value else "fail",
            }
        )

    all_sector_statuses = [
        sector["status"] for sector in omega_sectors + fixed_label_sectors
    ]
    return {
        "name": move["name"],
        "kind": move["kind"],
        "reason": move["reason"],
        "framing": int(framing),
        "moved": _braid_payload(oracle, move["n_strands"], move["braid_word"]),
        "omega_sectors": omega_sectors,
        "fixed_label_sectors": fixed_label_sectors,
        "status": "pass" if all(status == "pass" for status in all_sector_statuses) else "fail",
    }


def _braid_payload(oracle, n_strands, braid_word):
    return oracle.describe_braid(n_strands, braid_word)


def _has_immediate_cancellation(word):
    return any(left + right == 0 for left, right in zip(word, word[1:]))


def _generator_token(generator):
    return f"p{generator}" if generator > 0 else f"m{abs(generator)}"


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "su2-2-braid-auto-stress-v1",
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "generation": exact_output["generation"],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_2_braid_auto_stress.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_braid_auto_stress.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This is an automated one-component braid-closure presentation test.",
            "Values are exact CyclotomicField(16) JSON; no floating-point comparison is used.",
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
    print(f"cases: {exact_output['case_count']}")
    print(f"move checks: {exact_output['move_check_count']}")
    print(f"sector checks: {exact_output['sector_check_count']}")


if __name__ == "__main__":
    main()
