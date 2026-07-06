"""Character Gauss-sum scan for CP2#2CPbar split unlink candidates."""

from __future__ import annotations

from datetime import UTC, datetime
import cmath
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
import time


REPO_ROOT = Path(__file__).resolve().parents[2]
RESULT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "cp2-2cpbar-character-gauss-scan-v1.json"
)
STANDARD_ORDER = ("h", "e1", "e2")
STANDARD_FRAMINGS = (1, -1, -1)
GROUP_ORDER = 3
TOLERANCE = 1e-7


def command(argv: list[str]) -> str | None:
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


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


def root_of_unity(payload: dict) -> complex:
    if payload.get("kind") != "root_of_unity":
        raise ValueError(f"unsupported root payload: {payload}")
    return cmath.exp(
        2j
        * cmath.pi
        * int(payload.get("exponent", 0))
        / int(payload.get("root_order", 1))
    )


def cyclotomic_json_value(payload: dict) -> complex:
    match = payload.get("field", "")
    if match == "CyclotomicField(36)":
        root_order = 36
    elif match == "CyclotomicField(3)":
        root_order = 3
    else:
        raise ValueError(f"unsupported cyclotomic field: {payload.get('field')}")
    zeta = cmath.exp(2j * cmath.pi / root_order)
    return sum(complex(float(coefficient)) * zeta**index for index, coefficient in enumerate(payload["coefficients"]))


def scan_rows(labels: list[str], dimensions: dict[str, float], twists: dict[str, complex], degrees: dict[str, int]):
    def character(character_id: int, label: str) -> complex:
        return cmath.exp(2j * cmath.pi * int(character_id) * int(degrees[label]) / GROUP_ORDER)

    def gauss(framing: int, character_id: int) -> complex:
        return sum(
            dimensions[label] ** 2
            * character(character_id, label)
            * twists[label] ** int(framing)
            for label in labels
        )

    one_component = {
        str(framing): {
            str(character_id): complex_json(gauss(framing, character_id))
            for character_id in range(GROUP_ORDER)
        }
        for framing in (-1, 1)
    }
    baseline = gauss(1, 0) * gauss(-1, 0) * gauss(-1, 0)
    rows = []
    for alpha in product(range(GROUP_ORDER), repeat=3):
        factors = [
            gauss(framing, character_id)
            for framing, character_id in zip(STANDARD_FRAMINGS, alpha, strict=True)
        ]
        value = factors[0] * factors[1] * factors[2]
        differs = abs(value - baseline) > TOLERANCE
        rows.append(
            {
                "standard_alpha_order": list(STANDARD_ORDER),
                "standard_alpha": list(alpha),
                "standard_framings": list(STANDARD_FRAMINGS),
                "component_factors": [complex_json(factor) for factor in factors],
                "raw_value": complex_json(value),
                "differs_from_baseline": bool(differs),
                "difference_from_baseline": complex_json(value - baseline),
            }
        )
    return baseline, one_component, rows


def da4_candidate(path: Path, candidate_id: str) -> dict:
    mtc = json.loads(path.read_text())
    degree_by_class = {"1A": 0, "2A": 0, "3A": 1, "3B": 2}
    labels = [simple["label"] for simple in mtc["simple_objects"]]
    dimensions = {simple["label"]: float(simple["quantum_dimension"]) for simple in mtc["simple_objects"]}
    twists = {simple["label"]: root_of_unity(simple["twist"]) for simple in mtc["simple_objects"]}
    degrees = {simple["label"]: degree_by_class[simple["class_label"]] for simple in mtc["simple_objects"]}
    return candidate_payload(candidate_id, rel(path), labels, dimensions, twists, degrees)


def su3_3_candidate(path: Path) -> dict:
    payload = json.loads(path.read_text())["exact_output"]["category_data"]
    labels = payload["simple_labels"]
    dimensions = {label: cyclotomic_json_value(value).real for label, value in payload["quantum_dimensions"].items()}
    twists = {label: cyclotomic_json_value(value) for label, value in payload["twists"].items()}
    degrees = {label: int(value) for label, value in payload["universal_group"]["degrees"].items()}
    return candidate_payload("su3_3", rel(path), labels, dimensions, twists, degrees)


def vec_z3_candidate(path: Path) -> dict:
    labels = ["0", "1", "2"]
    dimensions = {label: 1.0 for label in labels}
    zeta3 = cmath.exp(2j * cmath.pi / 3)
    twists = {label: zeta3 ** (int(label) * int(label)) for label in labels}
    degrees = {label: int(label) for label in labels}
    return candidate_payload("vec_z3_pointed_q_x_squared", rel(path), labels, dimensions, twists, degrees)


def candidate_payload(candidate_id: str, source_artifact: str, labels, dimensions, twists, degrees) -> dict:
    baseline, one_component, rows = scan_rows(labels, dimensions, twists, degrees)
    nonbaseline = [row for row in rows if row["differs_from_baseline"]]
    return {
        "candidate_id": candidate_id,
        "source_artifact": source_artifact,
        "universal_group": "Z/3",
        "simple_label_count": len(labels),
        "baseline_alpha": [0, 0, 0],
        "baseline_raw_value": complex_json(baseline),
        "one_component_gauss_sums": one_component,
        "row_count": len(rows),
        "nonbaseline_count": len(nonbaseline),
        "first_nonbaseline_rows": nonbaseline[:8],
        "status": "nonbaseline-found" if nonbaseline else "no-nonbaseline-character-found",
        "rows": rows,
    }


def repo_metadata() -> dict:
    status_short = command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(status_short),
        "status_short": status_short,
    }


def main() -> int:
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    candidates = [
        da4_candidate(
            REPO_ROOT / "experiments" / "results" / "mtc-candidates" / "drinfeld-double-a4-omega0-mtc-fr-data-v1.json",
            "drinfeld_double_a4_omega0",
        ),
        da4_candidate(
            REPO_ROOT / "experiments" / "results" / "mtc-candidates" / "drinfeld-double-a4-c3w1-mtc-fr-data-v1.json",
            "drinfeld_double_a4_c3w1",
        ),
        su3_3_candidate(
            REPO_ROOT / "experiments" / "results" / "mtc-candidates" / "su3-3-multiplicity-stress-v1.json"
        ),
        vec_z3_candidate(
            REPO_ROOT / "experiments" / "results" / "mtc-candidates" / "vec-z3-pointed-stress-v1.json"
        ),
    ]
    payload = {
        "schema": "twisted-yetter.cp2-2cpbar-character-gauss-scan.v1",
        "status": "nonbaseline-found" if any(c["nonbaseline_count"] for c in candidates) else "no-nonbaseline-character-found",
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/sage/cp2_2cpbar_character_gauss_scan.py",
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "repo": repo_metadata(),
        "case": {
            "manifold": "CP2#2CPbar",
            "presentation": "split unlink",
            "standard_component_order": list(STANDARD_ORDER),
            "standard_framings": list(STANDARD_FRAMINGS),
            "character_group_scanned": "Z/3^3",
        },
        "summary": {
            "candidate_count": len(candidates),
            "candidates_with_nonbaseline": [
                candidate["candidate_id"] for candidate in candidates if candidate["nonbaseline_count"]
            ],
            "candidates_without_nonbaseline": [
                candidate["candidate_id"] for candidate in candidates if not candidate["nonbaseline_count"]
            ],
        },
        "candidates": candidates,
        "claim_boundary": (
            "Numeric ordinary split-link Gauss-sum preflight for CP2#2CPbar only; "
            "does not evaluate the Yasui braid presentation."
        ),
    }
    RESULT.parent.mkdir(parents=True, exist_ok=True)
    RESULT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": payload["status"], "artifact": rel(RESULT), **payload["summary"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
