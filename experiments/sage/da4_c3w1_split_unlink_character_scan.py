"""Scan c3w1 D(A4) character twists on the CP2#2CPbar split unlink."""

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
MTC_PATH = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "drinfeld-double-a4-c3w1-mtc-fr-data-v1.json"
)
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-standard-split-unlink-da4-c3w1-character-scan-v1.json"
)
FLUX_DEGREE_BY_CLASS = {
    "1A": 0,
    "2A": 0,
    "3A": 1,
    "3B": 2,
}
GROUP_ORDER = 3
STANDARD_ORDER = ("h", "e1", "e2")
STANDARD_FRAMINGS = (1, -1, -1)
BASELINE_RAW = 1728.0
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


def twist_value(twist: dict) -> complex:
    if twist.get("kind") != "root_of_unity":
        raise ValueError(f"unsupported twist payload: {twist}")
    return cmath.exp(
        2j
        * cmath.pi
        * int(twist.get("exponent", 0))
        / int(twist.get("root_order", 1))
    )


def character_value(character: int, label: str) -> complex:
    flux_class = label.split(":", 1)[0]
    degree = FLUX_DEGREE_BY_CLASS[flux_class]
    return cmath.exp(2j * cmath.pi * int(character) * degree / GROUP_ORDER)


def one_component_gauss_sum(simple_objects: list[dict], framing: int, character: int) -> complex:
    total = 0.0 + 0.0j
    for simple in simple_objects:
        dimension = float(simple["quantum_dimension"])
        total += (
            dimension
            * dimension
            * character_value(character, simple["label"])
            * (twist_value(simple["twist"]) ** int(framing))
        )
    return total


def yasui_component_twist_from_standard(alpha: tuple[int, int, int]) -> dict:
    alpha_h, alpha_e1, alpha_e2 = alpha
    by_component = {
        "A": (2 * alpha_h + alpha_e2) % GROUP_ORDER,
        "B": alpha_h % GROUP_ORDER,
        "C": (2 * alpha_h + alpha_e1) % GROUP_ORDER,
    }
    return {
        "omega_by_component": by_component,
        "omega_labels_in_braid_order_C_A_B": [
            by_component["C"],
            by_component["A"],
            by_component["B"],
        ],
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
    mtc = json.loads(MTC_PATH.read_text())
    simple_objects = mtc["simple_objects"]
    one_component = {
        str(framing): {
            str(character): complex_json(
                one_component_gauss_sum(simple_objects, framing, character)
            )
            for character in range(GROUP_ORDER)
        }
        for framing in (-1, 1)
    }
    rows = []
    for alpha in product(range(GROUP_ORDER), repeat=3):
        factors = [
            one_component_gauss_sum(simple_objects, framing, character)
            for framing, character in zip(STANDARD_FRAMINGS, alpha, strict=True)
        ]
        value = factors[0] * factors[1] * factors[2]
        differs = abs(value - BASELINE_RAW) > TOLERANCE
        rows.append(
            {
                "standard_alpha_order": list(STANDARD_ORDER),
                "standard_alpha": list(alpha),
                "standard_framings": list(STANDARD_FRAMINGS),
                "yasui_twist_transport": yasui_component_twist_from_standard(alpha),
                "component_factors": [complex_json(factor) for factor in factors],
                "raw_value": complex_json(value),
                "differs_from_1728": bool(differs),
                "difference_from_1728": complex_json(value - BASELINE_RAW),
            }
        )
    nonbaseline = [row for row in rows if row["differs_from_1728"]]
    payload = {
        "schema": "twisted-yetter.da4-c3w1-split-unlink-character-scan.v1",
        "status": "no-nonbaseline-character-found" if not nonbaseline else "nonbaseline-found",
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/sage/da4_c3w1_split_unlink_character_scan.py",
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "repo": repo_metadata(),
        "source": {
            "mtc_artifact": rel(MTC_PATH),
            "mtc_id": mtc.get("mtc_id"),
        },
        "case": {
            "standard_presentation": "split unlink for CP2#2CPbar",
            "standard_component_order": list(STANDARD_ORDER),
            "standard_framings": list(STANDARD_FRAMINGS),
            "universal_group": "Z/3",
            "yasui_class_map": {
                "A": "2h+e2",
                "B": "h",
                "C": "2h+e1",
            },
            "yasui_braid_order": ["C", "A", "B"],
        },
        "one_component_gauss_sums": one_component,
        "summary": {
            "row_count": len(rows),
            "nonbaseline_count": len(nonbaseline),
            "baseline_raw_value": repr(BASELINE_RAW),
            "tolerance": TOLERANCE,
            "conclusion": (
                "All Z/3^3 character twists on the ordinary split presentation "
                "evaluate numerically to the same raw value 1728."
            ),
        },
        "nonbaseline_rows": nonbaseline,
        "rows": rows,
        "claim_boundary": (
            "Numeric split-unlink character scan using one-component Gauss sums "
            "from the c3w1 D(A4) MTC data; not a theorem-level exact proof."
        ),
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": payload["status"], "artifact": rel(OUTPUT), **payload["summary"]}, sort_keys=True))
    return 0 if not nonbaseline else 2


if __name__ == "__main__":
    raise SystemExit(main())
