"""Basic controls for the D(A4) FR braid evaluator.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/da4_fr_braid_evaluator_basic_controls.sage.py

These controls intentionally use the same ``DA4FRBraidEvaluator.fixed_label_value``
implementation as the Yasui a=3 singleton computation.  The expected values are
categorical closed-form identities for simple framed unknots, split unlinks,
and Hopf links, not a second/simpler link evaluator.
"""

from __future__ import annotations

import argparse
import cmath
from datetime import UTC, datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

import numpy as np
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
EVALUATOR_PATH = REPO_ROOT / "experiments" / "sage" / "yasui_figure3_a3_da4_untwisted_chunked.sage.py"
MTC_PATH = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "drinfeld-double-a4-omega0-mtc-fr-data-v1.json"
)
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "drinfeld-double-a4-fr-braid-evaluator-basic-controls-v1.json"
)
TOLERANCE = 1e-7
GROUP_ORDER = 3
FLUX_DEGREE_BY_CLASS = {
    "1A": 0,
    "2A": 0,
    "3A": 1,
    "3B": 2,
}
HUB_TWO_LEAF_BRAID_WORD = (1, 1, 2, 1, 1, -2)
HUB_TWO_LEAF_SAMPLES = (
    ("1A:std3", "1A:std3"),
    ("2A:eps00", "2A:eps11"),
    ("3A:eta0", "3B:eta0"),
    ("1A:chi1", "3A:eta0"),
)


def load_evaluator_module():
    spec = importlib.util.spec_from_file_location("da4_yasui_a3_evaluator_under_test", EVALUATOR_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def command(argv: list[str]) -> str:
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError) as exc:
        return f"unavailable: {type(exc).__name__}"


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def complex_json(value: complex) -> dict[str, str]:
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def row_json(control: str, labels, observed: complex, expected: complex, extra=None):
    difference = observed - expected
    return {
        "control": control,
        "labels": list(labels),
        "observed": complex_json(observed),
        "expected": complex_json(expected),
        "difference": complex_json(difference),
        "abs_difference": repr(float(abs(difference))),
        "pass": bool(abs(difference) <= TOLERANCE),
        **(extra or {}),
    }


def hopf_expected(evaluator, x: str, y: str, *, positive: bool) -> complex:
    total = 0.0 + 0.0j
    for target, multiplicity in evaluator.fusion_outputs(x, y):
        if positive:
            monodromy = evaluator.twist(target) / (evaluator.twist(x) * evaluator.twist(y))
        else:
            monodromy = (evaluator.twist(x) * evaluator.twist(y)) / evaluator.twist(target)
        total += multiplicity * evaluator.dimension(target) * monodromy
    return total


def global_dimension(evaluator) -> float:
    return sum(evaluator.dimension(label) ** 2 for label in evaluator.labels)


def character_value(character: int, label: str) -> complex:
    flux_class = label.split(":", 1)[0]
    degree = FLUX_DEGREE_BY_CLASS[flux_class]
    return cmath.exp(2j * cmath.pi * int(character) * degree / GROUP_ORDER)


def omega_coefficient(evaluator, character: int, label: str) -> complex:
    return evaluator.dimension(label) * character_value(character, label)


def simple_current_targets(evaluator) -> dict[int, str]:
    targets = {}
    for character in range(GROUP_ORDER):
        matches = []
        for candidate in evaluator.labels:
            if abs(evaluator.dimension(candidate) - 1.0) > TOLERANCE:
                continue
            row_matches = True
            for label in evaluator.labels:
                expected = character_value(character, label) * evaluator.dimension(label)
                observed = hopf_expected(evaluator, candidate, label, positive=True)
                if abs(observed - expected) > TOLERANCE:
                    row_matches = False
                    break
            if row_matches:
                matches.append(candidate)
        if len(matches) != 1:
            raise ValueError(f"expected one simple-current target for character {character}, got {matches}")
        targets[character] = matches[0]
    return targets


def fusion_multiplicity(evaluator, left: str, right: str, target: str) -> int:
    return sum(multiplicity for output, multiplicity in evaluator.fusion_outputs(left, right) if output == target)


def parse_args(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--mtc", type=Path, default=MTC_PATH)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    mtc_path = args.mtc.resolve()
    output_path = args.output.resolve()
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    module = load_evaluator_module()
    mtc = json.loads(mtc_path.read_text())
    evaluator = module.DA4FRBraidEvaluator(mtc)
    rows = []
    simple_current_target_by_character = simple_current_targets(evaluator)
    global_dim = global_dimension(evaluator)

    for label in evaluator.labels:
        for framing in (-2, -1, 0, 1, 2):
            observed, stats = evaluator.fixed_label_value(1, (), (label,), (framing,))
            expected = evaluator.dimension(label) * (evaluator.twist(label) ** framing)
            rows.append(
                row_json(
                    "framed_unknot",
                    (label,),
                    observed,
                    expected,
                    {"framing": framing, "evaluator_stats": stats},
                )
            )

    for left in evaluator.labels:
        for right in evaluator.labels:
            for framings in ((0, 0), (1, -1)):
                observed, stats = evaluator.fixed_label_value(2, (), (left, right), framings)
                expected = (
                    evaluator.dimension(left)
                    * evaluator.dimension(right)
                    * (evaluator.twist(left) ** framings[0])
                    * (evaluator.twist(right) ** framings[1])
                )
                rows.append(
                    row_json(
                        "split_two_component_unlink",
                        (left, right),
                        observed,
                        expected,
                        {"framings": list(framings), "evaluator_stats": stats},
                    )
                )

    for left in evaluator.labels:
        for right in evaluator.labels:
            observed, stats = evaluator.fixed_label_value(2, (1, 1), (left, right), (0, 0))
            rows.append(
                row_json(
                    "positive_hopf_sigma1_squared",
                    (left, right),
                    observed,
                    hopf_expected(evaluator, left, right, positive=True),
                    {"braid_word": [1, 1], "framings": [0, 0], "evaluator_stats": stats},
                )
            )
            observed, stats = evaluator.fixed_label_value(2, (-1, -1), (left, right), (0, 0))
            rows.append(
                row_json(
                    "negative_hopf_sigma1_inverse_squared",
                    (left, right),
                    observed,
                    hopf_expected(evaluator, left, right, positive=False),
                    {"braid_word": [-1, -1], "framings": [0, 0], "evaluator_stats": stats},
                )
            )

    for character in range(GROUP_ORDER):
        target = simple_current_target_by_character[(-character) % GROUP_ORDER]
        for fixed_label in evaluator.labels:
            observed = 0.0 + 0.0j
            max_basis_size = 0
            for summand in evaluator.labels:
                fixed_value, stats = evaluator.fixed_label_value(
                    2,
                    (1, 1),
                    (summand, fixed_label),
                    (0, 0),
                )
                observed += omega_coefficient(evaluator, character, summand) * fixed_value
                max_basis_size = max(max_basis_size, int(stats.get("max_basis_size", 0)))
            expected = global_dim if fixed_label == target else 0.0 + 0.0j
            rows.append(
                row_json(
                    "colored_positive_hopf_projector",
                    (f"Omega_{character}", fixed_label),
                    observed,
                    expected,
                    {
                        "braid_word": [1, 1],
                        "framings": [0, 0],
                        "target_simple_current": target,
                        "max_basis_size_seen": max_basis_size,
                    },
                )
            )

    for character in range(GROUP_ORDER):
        target = simple_current_target_by_character[(-character) % GROUP_ORDER]
        for left, right in HUB_TWO_LEAF_SAMPLES:
            observed = 0.0 + 0.0j
            max_basis_size = 0
            for summand in evaluator.labels:
                fixed_value, stats = evaluator.fixed_label_value(
                    3,
                    HUB_TWO_LEAF_BRAID_WORD,
                    (summand, left, right),
                    (0, 0, 0),
                )
                observed += omega_coefficient(evaluator, character, summand) * fixed_value
                max_basis_size = max(max_basis_size, int(stats.get("max_basis_size", 0)))
            multiplicity = fusion_multiplicity(evaluator, left, right, target)
            expected = global_dim * multiplicity
            rows.append(
                row_json(
                    "colored_two_leaf_hub_projector",
                    (f"Omega_{character}", left, right),
                    observed,
                    expected,
                    {
                        "braid_word": list(HUB_TWO_LEAF_BRAID_WORD),
                        "framings": [0, 0, 0],
                        "target_simple_current": target,
                        "target_multiplicity_in_leaf_fusion": multiplicity,
                        "max_basis_size_seen": max_basis_size,
                    },
                )
            )

    failures = [row for row in rows if not row["pass"]]
    max_abs_difference = max(float(row["abs_difference"]) for row in rows) if rows else 0.0
    payload = {
        "schema": "twisted-yetter.da4-fr-braid-evaluator-basic-controls.v1",
        "status": "pass" if not failures else "fail",
        "generator_script": "experiments/sage/da4_fr_braid_evaluator_basic_controls.sage.py",
        "argv": sys.argv[1:],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/da4_fr_braid_evaluator_basic_controls.sage.py '
            f"--mtc {rel(mtc_path)} --output {rel(output_path)}"
        ),
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "tolerance": TOLERANCE,
        "claim_boundary": (
            "Basic numeric controls for the exact same D(A4) FR braid evaluator used by "
            "the Yasui a=3 singleton computation; not a theorem-level proof."
        ),
        "under_test": {
            "evaluator_script": rel(EVALUATOR_PATH),
            "evaluator_class": "DA4FRBraidEvaluator",
            "method": "fixed_label_value",
            "no_alternate_link_evaluator_used": True,
        },
        "source": {
            "mtc_artifact": rel(mtc_path),
            "mtc_sha256": file_sha256(mtc_path),
            "mtc_id": mtc["mtc_id"],
        },
        "tool_versions": {
            "sage": SAGE_VERSION,
            "python": sys.version,
            "numpy": np.__version__,
        },
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "dirty": bool(command(["git", "status", "--short"])),
            "status_short": command(["git", "status", "--short"]),
        },
        "summary": {
            "row_count": len(rows),
            "failure_count": len(failures),
            "max_abs_difference": repr(float(max_abs_difference)),
            "global_dimension": repr(float(global_dim)),
            "simple_current_target_by_character": {
                str(character): target for character, target in simple_current_target_by_character.items()
            },
            "omega_projector_target_by_character": {
                str(character): simple_current_target_by_character[(-character) % GROUP_ORDER]
                for character in range(GROUP_ORDER)
            },
            "controls": {
                "framed_unknot": 14 * 5,
                "split_two_component_unlink": 14 * 14 * 2,
                "positive_hopf_sigma1_squared": 14 * 14,
                "negative_hopf_sigma1_inverse_squared": 14 * 14,
                "colored_positive_hopf_projector": GROUP_ORDER * 14,
                "colored_two_leaf_hub_projector": GROUP_ORDER * len(HUB_TWO_LEAF_SAMPLES),
            },
        },
        "failures": failures[:20],
        "rows": rows,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": payload["status"], "artifact": rel(output_path), "failure_count": len(failures), "max_abs_difference": payload["summary"]["max_abs_difference"]}, sort_keys=True))
    return 0 if payload["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
