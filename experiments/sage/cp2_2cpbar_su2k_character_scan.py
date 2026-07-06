"""SU(2)_k character Gauss-sum scan for CP2#2CPbar split unlink."""

from __future__ import annotations

from datetime import UTC, datetime
import cmath
from itertools import product
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
    / "cp2-2cpbar-su2k-character-gauss-scan-v1.json"
)
STANDARD_ORDER = ("h", "e1", "e2")
STANDARD_FRAMINGS = (1, -1, -1)
COMPLEX_TOLERANCE = 1e-8
RATIO_TOLERANCE = 1e-8
DEFAULT_MAX_LEVEL = 64


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


def su2_dimension(level: int, label: int) -> float:
    return math.sin((label + 1) * math.pi / (level + 2)) / math.sin(math.pi / (level + 2))


def su2_twist(level: int, label: int) -> complex:
    return cmath.exp(2j * math.pi * label * (label + 2) / (4 * (level + 2)))


def su2_character(character: int, label: int) -> int:
    if character not in (0, 1):
        raise ValueError(f"SU(2)_k character must be 0 or 1, got {character}")
    return -1 if character and label % 2 else 1


def su2_gauss(level: int, framing: int, character: int) -> complex:
    return sum(
        su2_dimension(level, label) ** 2
        * su2_character(character, label)
        * su2_twist(level, label) ** framing
        for label in range(level + 1)
    )


def predicted_ratio(level: int, alpha: tuple[int, int, int]) -> complex:
    theta_generator = su2_twist(level, level)
    exponent = -alpha[0] + alpha[1] + alpha[2]
    return theta_generator**exponent


def level_row(level: int) -> dict:
    one_component = {
        str(framing): {
            str(character): complex_json(su2_gauss(level, framing, character))
            for character in (0, 1)
        }
        for framing in (-1, 1)
    }
    baseline = su2_gauss(level, 1, 0) * su2_gauss(level, -1, 0) * su2_gauss(level, -1, 0)
    rows = []
    for alpha in product((0, 1), repeat=3):
        factors = [
            su2_gauss(level, framing, character)
            for framing, character in zip(STANDARD_FRAMINGS, alpha, strict=True)
        ]
        value = factors[0] * factors[1] * factors[2]
        ratio = value / baseline if baseline else complex("nan")
        predicted = predicted_ratio(level, alpha)
        differs = abs(ratio - 1.0) > RATIO_TOLERANCE
        rows.append(
            {
                "standard_alpha_order": list(STANDARD_ORDER),
                "standard_alpha": list(alpha),
                "standard_framings": list(STANDARD_FRAMINGS),
                "component_factors": [complex_json(factor) for factor in factors],
                "raw_value": complex_json(value),
                "baseline_ratio": complex_json(ratio),
                "predicted_ratio_from_generator_twist": complex_json(predicted),
                "ratio_prediction_error": complex_json(ratio - predicted),
                "ratio_tolerance": RATIO_TOLERANCE,
                "differs_from_baseline": bool(differs),
            }
        )
    nonbaseline = [row for row in rows if row["differs_from_baseline"]]
    theta_generator = su2_twist(level, level)
    return {
        "level": level,
        "category_id": f"SU(2)_{level}",
        "universal_group": "Z/2",
        "generator_simple_object": level,
        "generator_twist": complex_json(theta_generator),
        "generator_twist_closed_form": "exp(pi*i*k/2)",
        "level_mod_4": level % 4,
        "quick_elimination": bool(abs(theta_generator - 1.0) <= COMPLEX_TOLERANCE),
        "quick_elimination_reason": (
            "k == 0 mod 4 makes theta_k=1, so every CP2#2CPbar split-link "
            "character-twist ratio is 1."
            if level % 4 == 0
            else "theta_k != 1, so some split-link character twists are nonbaseline."
        ),
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


def main(argv=None) -> int:
    max_level = DEFAULT_MAX_LEVEL
    if argv:
        if len(argv) == 2 and argv[0] == "--max-level":
            max_level = int(argv[1])
        else:
            raise SystemExit("usage: python experiments/sage/cp2_2cpbar_su2k_character_scan.py [--max-level N]")
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    levels = [level_row(level) for level in range(1, max_level + 1)]
    payload = {
        "schema": "twisted-yetter.cp2-2cpbar-su2k-character-gauss-scan.v1",
        "status": "pass",
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": (
            "python experiments/sage/cp2_2cpbar_su2k_character_scan.py "
            f"--max-level {max_level}"
        ),
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "repo": repo_metadata(),
        "case": {
            "manifold": "CP2#2CPbar",
            "presentation": "split unlink",
            "standard_component_order": list(STANDARD_ORDER),
            "standard_framings": list(STANDARD_FRAMINGS),
            "character_group_scanned": "(Z/2)^3",
        },
        "quick_theorem": {
            "status": "INFERENCE_FROM_STANDARD_SU2K_MODULAR_DATA",
            "statement": (
                "For SU(2)_k, the nontrivial universal character is parity. "
                "Let theta_k be the twist of the invertible simple object k. "
                "For CP2#2CPbar with split framings (+1,-1,-1), the character "
                "twist alpha=(alpha_h,alpha_e1,alpha_e2) has value equal to "
                "the untwisted baseline times theta_k^(-alpha_h+alpha_e1+alpha_e2)."
            ),
            "elimination_rule": (
                "If k == 0 mod 4 then theta_k=1, so all character twists on "
                "this ordinary split presentation are baseline and SU(2)_k is "
                "eliminated for this cheap test."
            ),
            "signal_rule": "If k is not 0 mod 4 then some character twists are nonbaseline.",
        },
        "summary": {
            "max_level": max_level,
            "levels_with_nonbaseline": [row["level"] for row in levels if row["nonbaseline_count"]],
            "levels_eliminated": [row["level"] for row in levels if not row["nonbaseline_count"]],
            "levels_eliminated_by_mod4_rule": [row["level"] for row in levels if row["level_mod_4"] == 0],
        },
        "levels": levels,
        "claim_boundary": (
            "Numeric CP2#2CPbar split-link SU(2)_k character Gauss-sum preflight. "
            "It uses closed-form SU(2)_k modular data only and does not evaluate "
            "the Yasui braid presentation."
        ),
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"artifact": rel(OUTPUT), **payload["summary"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
