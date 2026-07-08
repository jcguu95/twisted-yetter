#!/usr/bin/env python3
"""SU(3)_2 AnyonWiki F/R H2-character check for Yasui Figure 2 CP2(a=1).

The a=0 row is the untwisted check.  The a=1,2 rows are the legal Z/3
character twists obtained by pulling a character of H2=<h> back to the Yasui
components A=2h, C=2h, B=h in braid order [A,C,B].
"""

from __future__ import annotations

from datetime import UTC, datetime
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time
from itertools import product


REPO_ROOT = Path(__file__).resolve().parents[2]
EVALUATOR_PATH = REPO_ROOT / "experiments" / "sage" / "su3_2_anyonwiki_fr_braid_evaluator.py"
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure2-cp2-a1-r1-su3-2-anyonwiki-h2-character-check-v1.json"
)
TOLERANCE = 1e-8

N_STRANDS = 5
BRAID_WORD = (
    1,
    1,
    2,
    3,
    3,
    2,
    1,
    2,
    3,
    2,
    2,
    -4,
    3,
    2,
    1,
    2,
    3,
    3,
    2,
    3,
    4,
    -3,
)
COMPONENT_ORDER_IN_BRAID = ("A", "C", "B")
TOTAL_FRAMINGS_IN_BRAID_ORDER = (4, 4, 1)
UNTWISTED_CHARACTER_POWERS = (0, 0, 0)


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def command(argv: list[str]) -> str | None:
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def repo_metadata() -> dict[str, object]:
    status_short = command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(status_short),
        "status_short": status_short,
    }


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def omega_value_from_sectors(su3, evaluator, sectors: dict[tuple[str, ...], complex], character_powers: tuple[int, ...]) -> complex:
    total = 0.0 + 0.0j
    for fixed_labels, amplitude in sectors.items():
        coefficient = 1.0 + 0.0j
        for character_power, simple_label in zip(character_powers, fixed_labels, strict=True):
            coefficient *= evaluator.dimension(simple_label) * su3.character_value(character_power, simple_label)
        total += coefficient * amplitude
    return total


def sector_cache(su3, evaluator):
    sectors = {}
    stats = {
        "sector_count": 0,
        "max_basis_size": 0,
        "max_state_size": 0,
        "max_selected_strand_count": 0,
        "max_subbraid_word_length": 0,
    }
    for labels in product(evaluator.labels, repeat=3):
        value, fixed_stats = evaluator.fixed_label_value(
            N_STRANDS,
            BRAID_WORD,
            tuple(labels),
            TOTAL_FRAMINGS_IN_BRAID_ORDER,
        )
        sectors[tuple(labels)] = value
        stats["sector_count"] += 1
        stats["max_basis_size"] = max(stats["max_basis_size"], int(fixed_stats.get("max_basis_size", 0)))
        stats["max_state_size"] = max(stats["max_state_size"], int(fixed_stats.get("max_state_size", 0)))
        stats["max_selected_strand_count"] = max(
            stats["max_selected_strand_count"],
            int(fixed_stats.get("selected_strand_count", 0)),
        )
        stats["max_subbraid_word_length"] = max(
            stats["max_subbraid_word_length"],
            int(fixed_stats.get("subbraid_word_length", 0)),
        )
    return sectors, stats


def character_comparison_rows(su3, evaluator, sectors, global_dimension: float) -> list[dict[str, object]]:
    rows = []
    for h_character_power in range(3):
        yasui_character_powers = (
            (2 * h_character_power) % 3,
            (2 * h_character_power) % 3,
            h_character_power % 3,
        )
        standard_value = su3.one_component_gauss(evaluator, 1, h_character_power)
        raw = omega_value_from_sectors(su3, evaluator, sectors, yasui_character_powers)
        normalized = raw / (global_dimension * global_dimension)
        difference = normalized - standard_value
        rows.append(
            {
                "h_character_power": h_character_power,
                "component_order_in_braid": list(COMPONENT_ORDER_IN_BRAID),
                "yasui_character_powers_in_braid_order": list(yasui_character_powers),
                "standard_cp2_character_power": h_character_power,
                "standard_unknot_plus_one_value": su3.complex_json(standard_value),
                "yasui_r1_raw": su3.complex_json(raw),
                "yasui_r1_normalized_by_D_squared": su3.complex_json(normalized),
                "difference_normalized_minus_standard": su3.complex_json(difference),
                "abs_difference": repr(float(abs(difference))),
                "normalized_matches_standard": bool(abs(difference) <= TOLERANCE),
            }
        )
    return rows


def run_one_convention(su3, category_parameter: str, braiding_convention: str) -> dict[str, object]:
    evaluator = su3.SU32AnyonWikiFRBraidEvaluator(
        category_parameter=category_parameter,
        braiding_convention=braiding_convention,
    )
    sectors, stats = sector_cache(su3, evaluator)
    global_dimension = su3.global_dimension(evaluator)
    unknot_plus_one = su3.one_component_gauss(evaluator, 1, 0)
    raw = omega_value_from_sectors(su3, evaluator, sectors, UNTWISTED_CHARACTER_POWERS)
    normalized = raw / (global_dimension * global_dimension)
    difference = normalized - unknot_plus_one
    blackboard_self_writhe = evaluator.blackboard_self_writhe(N_STRANDS, BRAID_WORD)
    character_rows = character_comparison_rows(su3, evaluator, sectors, global_dimension)
    return {
        "category": su3.evaluator_metadata(evaluator),
        "blackboard_self_writhe": list(blackboard_self_writhe),
        "total_framings_in_braid_order": list(TOTAL_FRAMINGS_IN_BRAID_ORDER),
        "effective_extra_framing": [
            int(total - writhe)
            for total, writhe in zip(TOTAL_FRAMINGS_IN_BRAID_ORDER, blackboard_self_writhe, strict=True)
        ],
        "sector_stats": stats,
        "global_dimension_D": su3.complex_json(global_dimension),
        "global_dimension_D_squared": su3.complex_json(global_dimension * global_dimension),
        "unknot_plus_one_omega0": su3.complex_json(unknot_plus_one),
        "yasui_r1_raw": su3.complex_json(raw),
        "yasui_r1_normalized_by_D_squared": su3.complex_json(normalized),
        "difference_normalized_minus_unknot": su3.complex_json(difference),
        "abs_difference": repr(float(abs(difference))),
        "normalized_matches_unknot_plus_one": bool(abs(difference) <= TOLERANCE),
        "character_rows": character_rows,
        "all_character_rows_match": bool(all(row["normalized_matches_standard"] for row in character_rows)),
    }


def main() -> int:
    started = time.monotonic()
    su3 = load_module(EVALUATOR_PATH, "su3_2_anyonwiki_for_yasui_figure2_r1")
    rows = [
        run_one_convention(su3, "cat_1_3_1", "anyonwiki_direct"),
        run_one_convention(su3, "cat_1_3_2", "anyonwiki_direct"),
    ]
    primary_pass = bool(rows[0]["normalized_matches_unknot_plus_one"] and rows[0]["all_character_rows_match"])
    all_pass = all(row["normalized_matches_unknot_plus_one"] and row["all_character_rows_match"] for row in rows)
    result = {
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-r1-su3-2-anyonwiki-h2-character-check.v1",
        "status": "pass" if all_pass else ("pass_with_convention_warning" if primary_pass else "needs-review"),
        "mathematical_status": "FLOATING_COMPUTATIONAL_CHECK_NOT_THEOREM",
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/scripts/yasui_figure2_cp2_a1_r1_su3_2_anyonwiki_untwisted.py",
        "utc_start": datetime.now(UTC).isoformat(),
        "repo": repo_metadata(),
        "source": {
            "description": "R1-normalized Yasui Figure 2 CP2(a=1) braid",
            "component_order_in_braid": list(COMPONENT_ORDER_IN_BRAID),
            "n_strands": N_STRANDS,
            "braid_word": list(BRAID_WORD),
            "untwisted_character_powers": list(UNTWISTED_CHARACTER_POWERS),
            "h2_component_pullback": {
                "generator": "h",
                "A": "2h",
                "B": "h",
                "C": "2h"
            },
            "character_assignment_rule": (
                "For h-character a in Z/3, use component powers A=2a, C=2a, B=a "
                "in braid order [A,C,B]; compare against the standard +1 CP2 unknot with power a."
            ),
            "evaluator": rel(EVALUATOR_PATH),
        },
        "normalization": {
            "handle_factor": "divide by D^2 for the two original 3-handles read as dual Tham 5.11 one-handles",
            "framing_convention": "SU32AnyonWikiFRBraidEvaluator takes total framings and subtracts braid blackboard self-writhe internally",
        },
        "tolerance": repr(float(TOLERANCE)),
        "rows": rows,
        "selected_convention": {
            "category_parameter": "cat_1_3_1",
            "braiding_convention": "anyonwiki_direct",
            "reason": (
                "This is the previously selected working convention for Yasui runs; "
                "cat_1_3_2 is retained only as a convention-warning cross-check."
            ),
        },
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "artifact": rel(OUTPUT),
                "status": result["status"],
                "elapsed_seconds": result["elapsed_seconds"],
                "rows": [
                    {
                        "category_parameter": row["category"]["anyonwiki_category_parameter"],
                        "abs_difference": row["abs_difference"],
                        "match": row["normalized_matches_unknot_plus_one"],
                    }
                    for row in rows
                ],
            },
            sort_keys=True,
        )
    )
    return 0 if result["status"] in {"pass", "pass_with_convention_warning"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
