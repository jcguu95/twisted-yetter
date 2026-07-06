"""SU(3)_2 character Gauss-sum scan for CP2#2CPbar split unlink."""

from __future__ import annotations

from datetime import UTC, datetime
from itertools import product
import cmath
import json
import math
from pathlib import Path
import subprocess
import sys
import time


REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "cp2-2cpbar-su3-2-character-gauss-scan-v1.json"
)
LEVEL = 2
STANDARD_ORDER = ("h", "e1", "e2")
STANDARD_FRAMINGS = (1, -1, -1)
TOLERANCE = 1e-9


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


def qint(n: int) -> float:
    return math.sin(n * math.pi / (LEVEL + 3)) / math.sin(math.pi / (LEVEL + 3))


def dimension(label: tuple[int, int]) -> float:
    a, b = label
    return qint(a + 1) * qint(b + 1) * qint(a + b + 2) / qint(2)


def casimir(label: tuple[int, int]) -> float:
    a, b = label
    return (a * a + b * b + a * b + 3 * a + 3 * b) / 3


def twist(label: tuple[int, int]) -> complex:
    return cmath.exp(2j * math.pi * casimir(label) / (LEVEL + 3))


def triality(label: tuple[int, int]) -> int:
    a, b = label
    return (a + 2 * b) % 3


def character(power: int, label: tuple[int, int]) -> complex:
    return cmath.exp(2j * math.pi * power * triality(label) / 3)


def gauss(framing: int, character_power: int) -> complex:
    labels = [(a, b) for a in range(LEVEL + 1) for b in range(LEVEL + 1 - a)]
    return sum(
        dimension(label) ** 2 * character(character_power, label) * twist(label) ** framing
        for label in labels
    )


def simple_current_twist(power: int) -> complex:
    if power % 3 == 0:
        return 1 + 0j
    if power % 3 == 1:
        return twist((LEVEL, 0))
    return twist((0, LEVEL))


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
    labels = [(a, b) for a in range(LEVEL + 1) for b in range(LEVEL + 1 - a)]
    generator_twist = twist((LEVEL, 0))
    one_component = {
        str(framing): {
            str(power): complex_json(gauss(framing, power))
            for power in range(3)
        }
        for framing in (-1, 1)
    }
    baseline = gauss(1, 0) * gauss(-1, 0) * gauss(-1, 0)
    rows = []
    for alpha in product(range(3), repeat=3):
        factors = [
            gauss(framing, power)
            for framing, power in zip(STANDARD_FRAMINGS, alpha, strict=True)
        ]
        value = factors[0] * factors[1] * factors[2]
        ratio = value / baseline
        predicted_ratio = (
            simple_current_twist(alpha[0]) ** -1
            * simple_current_twist(alpha[1])
            * simple_current_twist(alpha[2])
        )
        rows.append(
            {
                "standard_alpha_order": list(STANDARD_ORDER),
                "standard_alpha": list(alpha),
                "standard_framings": list(STANDARD_FRAMINGS),
                "component_factors": [complex_json(factor) for factor in factors],
                "raw_value": complex_json(value),
                "baseline_ratio": complex_json(ratio),
                "predicted_ratio_from_simple_current_twist": complex_json(predicted_ratio),
                "ratio_prediction_error": complex_json(ratio - predicted_ratio),
                "differs_from_baseline": bool(abs(ratio - 1) > TOLERANCE),
            }
        )
    nonbaseline = [row for row in rows if row["differs_from_baseline"]]
    max_ratio_prediction_error = max(
        abs(
            complex(
                float(row["ratio_prediction_error"]["real"]),
                float(row["ratio_prediction_error"]["imag"]),
            )
        )
        for row in rows
    )
    payload = {
        "schema": "twisted-yetter.cp2-2cpbar-su3-2-character-gauss-scan.v1",
        "status": "pass" if max_ratio_prediction_error < TOLERANCE else "mismatch",
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/sage/cp2_2cpbar_su3_2_character_scan.py",
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "repo": repo_metadata(),
        "category": {
            "id": "SU(3)_2",
            "rank": len(labels),
            "global_dimension_numeric": sum(dimension(label) ** 2 for label in labels),
            "simple_current_group": "Z/3 generated by (2,0)",
            "generator_twist": complex_json(generator_twist),
            "generator_twist_closed_form": "exp(4*pi*i/3)",
            "simple_current_quadratic_form": {
                str(power): complex_json(simple_current_twist(power))
                for power in range(3)
            },
            "labels": [
                {
                    "label": list(label),
                    "dimension": repr(float(dimension(label))),
                    "twist": complex_json(twist(label)),
                    "triality": triality(label),
                }
                for label in labels
            ],
        },
        "case": {
            "manifold": "CP2#2CPbar",
            "presentation": "ordinary split unlink",
            "standard_component_order": list(STANDARD_ORDER),
            "standard_framings": list(STANDARD_FRAMINGS),
            "character_group_scanned": "(Z/3)^3",
        },
        "one_component_gauss_sums": one_component,
        "baseline_raw_value": complex_json(baseline),
        "row_count": len(rows),
        "nonbaseline_count": len(nonbaseline),
        "nonbaseline_alphas": [row["standard_alpha"] for row in nonbaseline],
        "max_ratio_prediction_error": repr(float(max_ratio_prediction_error)),
        "rows": rows,
        "claim_boundary": (
            "Numeric CP2#2CPbar split-link SU(3)_2 character Gauss-sum "
            "preflight. It uses closed-form SU(3)_2 modular data only and "
            "does not evaluate the Yasui braid presentation."
        ),
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "artifact": rel(OUTPUT),
                "status": payload["status"],
                "baseline_raw_value": payload["baseline_raw_value"]["display"],
                "row_count": len(rows),
                "nonbaseline_count": len(nonbaseline),
                "first_nonbaseline_alphas": payload["nonbaseline_alphas"][:8],
            },
            sort_keys=True,
        )
    )
    return 0 if payload["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
