"""Mechanize the first SU(2)_2 handle-slide toy checks.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_handle_slide_toys.sage.py

This suite intentionally covers only the two handle-slide examples that were
already checked by hand/natural-language scratch work:

1. two-component unknotted framed-link slides, including the CP2#CP2,
   CP2#CPbar, and S2xS2 toy cases;
2. a 0-framed right trefoil slid over a split +1-framed unknot.

Each comparison checks:

* the before-slide braid-closure evaluation;
* the after-slide braid-closure evaluation;
* the previously recorded expected value from
  wiki/lab-notes/2026-07-01-su2-2-twisted-kirby-tests.org.

If any value differs, the certificate status becomes fail and the script exits
with a nonzero status.
"""

from __future__ import annotations

import argparse
import importlib.util
import sys
from itertools import product
from pathlib import Path
import subprocess
import time

from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"
DEFAULT_OUTPUT = REPO_ROOT / "experiments" / "results" / "sage-stress" / "su2-2-handle-slide-toys-v1.json"

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402


def load_oracle():
    spec = importlib.util.spec_from_file_location("su2_2_braid_oracle_runtime", ORACLE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run_suite(oracle):
    examples = [
        unknot_slide_family(oracle),
        trefoil_over_plus_one_unknot(oracle),
    ]
    status = "pass" if all(example["status"] == "pass" for example in examples) else "fail"
    return {
        "schema": "twisted-yetter.su2_2-handle-slide-toys.v1",
        "status": status,
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "source_note": "wiki/lab-notes/2026-07-01-su2-2-twisted-kirby-tests.org",
        "scope": (
            "mechanized SU(2)_2 checks for the first two handle-slide toy examples: "
            "unknotted two-component slides and a trefoil slid over a +1 unknot"
        ),
        "not_scope": (
            "general Kirby diagram evaluator, arbitrary band-sum constructor, "
            "special-link/dotted-component evaluation, or closed 4-manifold normalization"
        ),
        "example_count": len(examples),
        "comparison_count": sum(len(example["comparisons"]) for example in examples),
        "examples": examples,
    }


def unknot_slide_family(oracle):
    cases = [
        {
            "name": "cp2-sum-cp2-second-over-first",
            "source_test": "Test 4",
            "before": {"n_strands": 2, "braid_word": (), "framings": (1, 1)},
            "after": {"n_strands": 2, "braid_word": (1, 1), "framings": (1, 2)},
            "after_labels": lambda a, b: (a, (a + b) % 2),
            "expected": lambda z, sqrt2, a, b: ((-1) ** (a + b)) * 4 * z**6,
        },
        {
            "name": "cp2-sum-cpbar-second-over-first",
            "source_test": "Test 5",
            "before": {"n_strands": 2, "braid_word": (), "framings": (1, -1)},
            "after": {"n_strands": 2, "braid_word": (1, 1), "framings": (1, 0)},
            "after_labels": lambda a, b: (a, (a + b) % 2),
            "expected": lambda z, sqrt2, a, b: ((-1) ** (a + b)) * 4,
        },
        {
            "name": "s2x-s2-second-over-first",
            "source_test": "Test 6",
            "before": {"n_strands": 2, "braid_word": (1, 1), "framings": (0, 0)},
            "after": {"n_strands": 2, "braid_word": (1, 1), "framings": (0, 2)},
            "after_labels": lambda a, b: (a, (a + b) % 2),
            "expected": lambda z, sqrt2, a, b: 4,
        },
    ]

    comparisons = []
    for case in cases:
        for a, b in product((0, 1), repeat=2):
            before_value = oracle.omega_value(
                case["before"]["n_strands"],
                case["before"]["braid_word"],
                case["before"]["framings"],
                (a, b),
            )
            after_value = oracle.omega_value(
                case["after"]["n_strands"],
                case["after"]["braid_word"],
                case["after"]["framings"],
                case["after_labels"](a, b),
            )
            expected_value = oracle.K(case["expected"](oracle.ZETA, oracle.SQRT2, a, b))
            comparisons.append(
                comparison_payload(
                    oracle,
                    case_name=case["name"],
                    source_test=case["source_test"],
                    labels={"before": [a, b], "after": list(case["after_labels"](a, b))},
                    before=case["before"],
                    after=case["after"],
                    before_value=before_value,
                    after_value=after_value,
                    expected_value=expected_value,
                )
            )

    return {
        "name": "unknotted-framed-link-slides",
        "status": "pass" if all(item["status"] == "pass" for item in comparisons) else "fail",
        "comparisons": comparisons,
    }


def trefoil_over_plus_one_unknot(oracle):
    before = {
        "n_strands": 3,
        "braid_word": (1, 1, 1),
        "framings": (0, 1),
    }
    after = {
        "n_strands": 3,
        "braid_word": (1, 1, 1, 2, 2),
        "framings": (1, 1),
    }

    comparisons = []
    for a, b in product((0, 1), repeat=2):
        after_labels = ((a + b) % 2, b)
        before_value = oracle.omega_value(
            before["n_strands"],
            before["braid_word"],
            before["framings"],
            (a, b),
        )
        after_value = oracle.omega_value(
            after["n_strands"],
            after["braid_word"],
            after["framings"],
            after_labels,
        )
        expected_value = trefoil_slide_expected(oracle, a, b)
        comparisons.append(
            comparison_payload(
                oracle,
                case_name="right-trefoil-over-plus-one-unknot",
                source_test="Test 8",
                labels={"before": [a, b], "after": list(after_labels)},
                before=before,
                after=after,
                before_value=before_value,
                after_value=after_value,
                expected_value=expected_value,
            )
        )

    return {
        "name": "right-trefoil-over-plus-one-unknot",
        "status": "pass" if all(item["status"] == "pass" for item in comparisons) else "fail",
        "after_braid_note": (
            "after picture encoded as closure of sigma_1^3 sigma_2^2, "
            "with components [[0,1],[2]] and linking number +1"
        ),
        "comparisons": comparisons,
    }


def trefoil_slide_expected(oracle, a, b):
    z = oracle.ZETA
    sqrt2 = oracle.SQRT2
    if (a, b) == (0, 0):
        return -2 * sqrt2 * z + 4 * z**3 - 2 * sqrt2 * z**5
    if (a, b) == (0, 1):
        return 2 * sqrt2 * z - 4 * z**3 + 2 * sqrt2 * z**5
    if (a, b) == (1, 0):
        return 2 * sqrt2 * z + 4 * z**3 + 2 * sqrt2 * z**5
    if (a, b) == (1, 1):
        return -2 * sqrt2 * z - 4 * z**3 - 2 * sqrt2 * z**5
    raise ValueError("Z/2 labels expected")


def comparison_payload(
    oracle,
    *,
    case_name,
    source_test,
    labels,
    before,
    after,
    before_value,
    after_value,
    expected_value,
):
    status = "pass" if before_value == after_value == expected_value else "fail"
    return {
        "case_name": case_name,
        "source_test": source_test,
        "labels": labels,
        "status": status,
        "before": diagram_payload(oracle, before),
        "after": diagram_payload(oracle, after),
        "before_value": oracle.cyclotomic_json(before_value),
        "after_value": oracle.cyclotomic_json(after_value),
        "expected_from_prior_note": oracle.cyclotomic_json(expected_value),
    }


def diagram_payload(oracle, payload):
    output = oracle.describe_braid(payload["n_strands"], payload["braid_word"])
    output["framings"] = [int(framing) for framing in payload["framings"]]
    return output


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "su2-2-handle-slide-toys-v1",
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "source_note": exact_output["source_note"],
        "examples": [example["name"] for example in exact_output["examples"]],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_2_handle_slide_toys.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_handle_slide_toys.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This suite stops with nonzero exit if any mechanized value differs from the prior note.",
            "The trefoil after-slide picture is encoded as a braid closure, not as a hand-only S-matrix formula.",
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
    print(f"examples: {exact_output['example_count']}")
    print(f"comparisons: {exact_output['comparison_count']}")
    if certificate["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
