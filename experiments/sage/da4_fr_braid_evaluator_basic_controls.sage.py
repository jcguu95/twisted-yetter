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


def load_evaluator_module():
    spec = importlib.util.spec_from_file_location("da4_yasui_a3_evaluator_under_test", EVALUATOR_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def command(argv: list[str]) -> str:
    return subprocess.check_output(argv, cwd=REPO_ROOT, text=True).strip()


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
            "controls": {
                "framed_unknot": 14 * 5,
                "split_two_component_unlink": 14 * 14 * 2,
                "positive_hopf_sigma1_squared": 14 * 14,
                "negative_hopf_sigma1_inverse_squared": 14 * 14,
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
