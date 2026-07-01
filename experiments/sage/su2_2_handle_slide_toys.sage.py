"""Mechanize the first SU(2)_2 handle-slide toy checks.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_handle_slide_toys.sage.py

This suite covers the handle-slide examples that were already checked by
hand/natural-language scratch work, then adds a small generated family:

1. two-component unknotted framed-link slides, including the CP2#CP2,
   CP2#CPbar, and S2xS2 toy cases;
2. a 0-framed right trefoil slid over a split +1-framed unknot;
3. the same trefoil slid over two split +1-framed unknots;
4. generated 2-strand knot examples slid over 1, 2, or 3 split +1-framed
   unknots.

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
        trefoil_over_two_plus_one_unlinks(oracle),
        generated_two_strand_knot_meridian_slides(oracle),
    ]
    status = "pass" if all(example["status"] == "pass" for example in examples) else "fail"
    return {
        "schema": "twisted-yetter.su2_2-handle-slide-toys.v1",
        "status": status,
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "source_note": "wiki/lab-notes/2026-07-01-su2-2-twisted-kirby-tests.org",
        "scope": (
            "mechanized SU(2)_2 checks for unknotted slides, trefoil one/two-slide "
            "examples from the prior note, and a generated 2-strand knot slide family"
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


def trefoil_over_two_plus_one_unlinks(oracle):
    before = split_knot_with_unlinks(
        knot_n_strands=2,
        knot_word=(1, 1, 1),
        meridian_count=2,
    )
    after = slid_knot_with_meridians(
        knot_word=(1, 1, 1),
        meridian_count=2,
    )

    comparisons = []
    for a, b, c in product((0, 1), repeat=3):
        after_labels = ((a + b + c) % 2, b, c)
        before_value = oracle.omega_value(
            before["n_strands"],
            before["braid_word"],
            before["framings"],
            (a, b, c),
        )
        after_value = oracle.omega_value(
            after["n_strands"],
            after["braid_word"],
            after["framings"],
            after_labels,
        )
        expected_value = trefoil_two_slide_expected(oracle, a, b, c)
        comparisons.append(
            comparison_payload(
                oracle,
                case_name="right-trefoil-over-two-plus-one-unlinks",
                source_test="Test 9",
                labels={"before": [a, b, c], "after": list(after_labels)},
                before=before,
                after=after,
                before_value=before_value,
                after_value=after_value,
                expected_value=expected_value,
            )
        )

    return {
        "name": "right-trefoil-over-two-plus-one-unlinks",
        "status": "pass" if all(item["status"] == "pass" for item in comparisons) else "fail",
        "after_braid_note": (
            "after picture encoded as closure of sigma_1^3 sigma_2^2 "
            "sigma_3 sigma_2^2 sigma_3^-1; linking matrix has K linked once "
            "with each unknot and the unknots mutually unlinked"
        ),
        "comparisons": comparisons,
    }


def generated_two_strand_knot_meridian_slides(oracle):
    knots = [
        {"name": "right-trefoil", "word": (1, 1, 1)},
        {"name": "left-trefoil", "word": (-1, -1, -1)},
        {"name": "t-2-5", "word": (1, 1, 1, 1, 1)},
        {"name": "t-2-minus-5", "word": (-1, -1, -1, -1, -1)},
    ]

    comparisons = []
    for knot in knots:
        for meridian_count in (1, 2, 3):
            before = split_knot_with_unlinks(
                knot_n_strands=2,
                knot_word=knot["word"],
                meridian_count=meridian_count,
            )
            after = slid_knot_with_meridians(
                knot_word=knot["word"],
                meridian_count=meridian_count,
            )
            for labels in product((0, 1), repeat=meridian_count + 1):
                after_labels = ((sum(labels) % 2), *labels[1:])
                before_value = oracle.omega_value(
                    before["n_strands"],
                    before["braid_word"],
                    before["framings"],
                    labels,
                )
                after_value = oracle.omega_value(
                    after["n_strands"],
                    after["braid_word"],
                    after["framings"],
                    after_labels,
                )
                comparisons.append(
                    comparison_payload(
                        oracle,
                        case_name=f"{knot['name']}-over-{meridian_count}-plus-one-unlinks",
                        source_test="generated-family",
                        labels={"before": list(labels), "after": list(after_labels)},
                        before=before,
                        after=after,
                        before_value=before_value,
                        after_value=after_value,
                        expected_value=before_value,
                    )
                )

    return {
        "name": "generated-two-strand-knot-meridian-slides",
        "status": "pass" if all(item["status"] == "pass" for item in comparisons) else "fail",
        "generator_note": (
            "For a 2-strand knot word beta and m split +1 unknots, the after word "
            "is beta followed by pure-braid meridian words linking the knot component "
            "once with each unknot and keeping the unknots mutually unlinked."
        ),
        "comparisons": comparisons,
    }


def split_knot_with_unlinks(*, knot_n_strands, knot_word, meridian_count):
    return {
        "n_strands": knot_n_strands + meridian_count,
        "braid_word": tuple(knot_word),
        "framings": (0,) + tuple(1 for _ in range(meridian_count)),
    }


def slid_knot_with_meridians(*, knot_word, meridian_count):
    braid_word = tuple(knot_word)
    for strand in range(3, 3 + meridian_count):
        braid_word += meridian_word_for_new_strand(strand)
    return {
        "n_strands": 2 + meridian_count,
        "braid_word": braid_word,
        "framings": (meridian_count,) + tuple(1 for _ in range(meridian_count)),
    }


def meridian_word_for_new_strand(strand):
    """Pure braid linking a new strand once with the 2-strand knot component."""

    return (
        tuple(range(strand - 1, 2, -1))
        + (2, 2)
        + tuple(range(-3, -strand, -1))
    )


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


def trefoil_two_slide_expected(oracle, a, b, c):
    z = oracle.ZETA
    sqrt2 = oracle.SQRT2
    if (a, b, c) == (0, 0, 0):
        return 4 * sqrt2 - 4 * sqrt2 * z**4 + 8 * z**6
    if (a, b, c) == (0, 0, 1):
        return -4 * sqrt2 + 4 * sqrt2 * z**4 - 8 * z**6
    if (a, b, c) == (0, 1, 0):
        return -4 * sqrt2 + 4 * sqrt2 * z**4 - 8 * z**6
    if (a, b, c) == (0, 1, 1):
        return 4 * sqrt2 - 4 * sqrt2 * z**4 + 8 * z**6
    if (a, b, c) == (1, 0, 0):
        return -4 * sqrt2 + 4 * sqrt2 * z**4 + 8 * z**6
    if (a, b, c) == (1, 0, 1):
        return 4 * sqrt2 - 4 * sqrt2 * z**4 - 8 * z**6
    if (a, b, c) == (1, 1, 0):
        return 4 * sqrt2 - 4 * sqrt2 * z**4 - 8 * z**6
    if (a, b, c) == (1, 1, 1):
        return -4 * sqrt2 + 4 * sqrt2 * z**4 + 8 * z**6
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
