#!/usr/bin/env python3
"""Generate Yasui character-twist history correction artifacts."""

from __future__ import annotations

from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
RESULTS = REPO_ROOT / "experiments" / "results" / "yasui"

SU3_YASUI = RESULTS / "figure3-a1-r1-normalized-su3-2-anyonwiki-aggregate-v1.json"
SU3_SPLIT = RESULTS / "cp2-2cpbar-su3-2-character-gauss-scan-v1.json"
SU2_A1 = RESULTS / "figure3-a1-r1-normalized-su2-2-all-alpha-raw-comparison-v3.json"
SU2_A3 = RESULTS / "figure3-a3-su2-2-all-alpha-chunked-comparison-v1.json"
DIC12_TRACE_MANIFEST = (
    RESULTS
    / "figure3-a1-r1-normalized-dic12-witness-g-component-a-twist-compact-trace-manifest-v1.json"
)
DIC12_TRACE = (
    RESULTS
    / "figure3-a1-r1-normalized-dic12-witness-g-component-a-twist-compact-trace-v1.jsonl"
)

COORDINATE_OUTPUT = (
    RESULTS / "figure3-a1-su3-2-yasui-vs-split-coordinate-comparison-v1.json"
)
LEDGER_OUTPUT = RESULTS / "yasui-character-twist-history-correction-v1.json"

TOLERANCE = 1e-8


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(argv: list[str]) -> str | None:
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def artifact_record(path: Path) -> dict[str, Any]:
    payload = read_json(path)
    return {
        "path": rel(path),
        "sha256": sha256(path),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
    }


def complex_from_json(payload: Any) -> complex:
    if isinstance(payload, dict):
        return complex(float(payload["real"]), float(payload["imag"]))
    if isinstance(payload, str):
        return complex(payload.replace("I", "j").replace(" ", ""))
    raise TypeError(f"cannot parse complex value from {type(payload)!r}")


def complex_json(value: complex) -> dict[str, str]:
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def yasui_to_standard_alpha(alpha: tuple[int, int, int]) -> tuple[int, int, int]:
    c, a, b = alpha
    return (b % 3, (a + b) % 3, (c + 2 * b) % 3)


def su3_coordinate_comparison() -> dict[str, Any]:
    yasui = read_json(SU3_YASUI)
    split = read_json(SU3_SPLIT)
    yasui_rows = {
        tuple(row["alpha"]): complex_from_json(row["raw_value"])
        for row in yasui["all_character_aggregates"]
    }
    split_rows = {
        tuple(row["standard_alpha"]): complex_from_json(row["raw_value"])
        for row in split["rows"]
    }
    direct_rows = []
    mapped_rows = []
    for alpha in sorted(yasui_rows):
        y_value = yasui_rows[alpha]
        direct_split_value = split_rows[alpha]
        mapped_alpha = yasui_to_standard_alpha(alpha)
        mapped_split_value = split_rows[mapped_alpha]
        direct_diff = y_value - direct_split_value
        mapped_diff = y_value - mapped_split_value
        direct_rows.append(
            {
                "yasui_alpha_CAB": list(alpha),
                "standard_alpha_he1e2_direct": list(alpha),
                "yasui_raw": complex_json(y_value),
                "split_raw_direct": complex_json(direct_split_value),
                "difference": complex_json(direct_diff),
                "abs_difference": repr(float(abs(direct_diff))),
                "differs_under_tolerance": abs(direct_diff) > TOLERANCE,
            }
        )
        mapped_rows.append(
            {
                "yasui_alpha_CAB": list(alpha),
                "standard_alpha_he1e2_mapped": list(mapped_alpha),
                "yasui_raw": complex_json(y_value),
                "split_raw_mapped": complex_json(mapped_split_value),
                "difference": complex_json(mapped_diff),
                "abs_difference": repr(float(abs(mapped_diff))),
                "close_under_tolerance": abs(mapped_diff) <= TOLERANCE,
            }
        )

    direct_diffs = [float(row["abs_difference"]) for row in direct_rows]
    mapped_diffs = [float(row["abs_difference"]) for row in mapped_rows]
    return {
        "schema": "twisted-yetter.yasui-su3-2-coordinate-comparison.v1",
        "status": "pass",
        "tolerance": repr(TOLERANCE),
        "claim_boundary": (
            "This artifact compares the saved SU(3)_2 Yasui a=1 all-character "
            "aggregate with the saved CP2#2CPbar split character scan. It shows "
            "that direct same-tuple comparison is misleading and that the current "
            "data match after the recorded character-coordinate map. It is numeric "
            "evidence, not a theorem-level proof."
        ),
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/scripts/yasui_character_twist_history_correction.py",
        "inputs": {
            "yasui_su3_2_all_character_aggregate": artifact_record(SU3_YASUI),
            "cp2_2cpbar_su3_2_split_scan": artifact_record(SU3_SPLIT),
        },
        "coordinate_map": {
            "yasui_alpha_order": ["C", "A", "B"],
            "standard_alpha_order": ["h", "e1", "e2"],
            "formula": "standard(h,e1,e2) = (B, A+B, C+2B) mod 3 for Yasui alpha=(C,A,B)",
            "matrix_rows_standard_from_yasui_CAB_mod_3": [[0, 0, 1], [0, 1, 1], [1, 0, 2]],
        },
        "summary": {
            "row_count": len(yasui_rows),
            "direct_same_tuple_nonmatching_count": sum(row["differs_under_tolerance"] for row in direct_rows),
            "direct_same_tuple_max_abs_difference": repr(max(direct_diffs)),
            "mapped_nonmatching_count": sum(not row["close_under_tolerance"] for row in mapped_rows),
            "mapped_max_abs_difference": repr(max(mapped_diffs)),
            "interpretation": (
                "SU(3)_2 has a nonbaseline character-twist function, but the "
                "saved Yasui a=1 function matches the standard split function "
                "after the displayed coordinate map. Direct same-tuple differences "
                "are coordinate artifacts, not Yasui-vs-standard separation evidence."
            ),
        },
        "direct_same_tuple_rows": direct_rows,
        "mapped_rows": mapped_rows,
    }


def su2_summary(path: Path) -> dict[str, Any]:
    payload = read_json(path)
    rows = payload["rows"]
    base = complex_from_json(rows[0]["yasui_value"])
    vs_alpha0 = []
    for row in rows:
        value = complex_from_json(row["yasui_value"])
        diff = value - base
        vs_alpha0.append((tuple(row["alpha"]), abs(diff), value / base))
    return {
        "artifact": artifact_record(path),
        "alpha_mode": payload.get("alpha_mode"),
        "row_count": len(rows),
        "tolerance": payload.get("tolerance"),
        "yasui_vs_standard_max_abs_difference": repr(max(float(row["abs_difference"]) for row in rows)),
        "nonbaseline_count_vs_alpha0_tolerance_1e_minus_8": sum(diff > TOLERANCE for _, diff, _ in vs_alpha0),
        "max_abs_difference_vs_alpha0": repr(float(max(diff for _, diff, _ in vs_alpha0))),
        "nonbaseline_ratios_vs_alpha0": [
            {"alpha": list(alpha), "ratio_to_alpha0": complex_json(ratio), "abs_difference": repr(float(diff))}
            for alpha, diff, ratio in vs_alpha0
            if diff > TOLERANCE
        ],
        "interpretation": (
            "This is a complete all-alpha nonbaseline Yasui SU(2)_2 run, but "
            "the saved artifact compares Yasui to the corresponding standard value "
            "for each alpha and passes. It is not Yasui-vs-standard separation evidence."
        ),
    }


def dic12_summary() -> dict[str, Any]:
    manifest = read_json(DIC12_TRACE_MANIFEST)
    metadata = json.loads(DIC12_TRACE.open().readline())
    return {
        "artifact": artifact_record(DIC12_TRACE_MANIFEST),
        "compact_trace": {
            "path": rel(DIC12_TRACE),
            "sha256": sha256(DIC12_TRACE),
            "schema": metadata.get("schema"),
            "row_count": metadata.get("row_count"),
        },
        "manifest_mathematical_summary": manifest.get("mathematical_summary"),
        "witness_summary": {
            "category": "omega0 untwisted D(Dic_12)",
            "case": metadata.get("case"),
            "witness_invertible": metadata.get("case", {}).get("witness_invertible"),
            "component": "Yasui component A, interpreted as standard e1",
            "ratio_twisted_to_untwisted": metadata.get("ratio_twisted_to_untwisted"),
            "standard_split_reference": metadata.get("standard_split_reference"),
        },
        "interpretation": (
            "The admitted D(Dic_12) witness changes the Yasui a=1 value by the "
            "same pointed ratio -1 as the CP2#2CPbar split reference. This is a "
            "witness-level pointed bookkeeping signal, not Yasui-vs-standard "
            "separation evidence and not an all-alpha equivalence artifact."
        ),
    }


def correction_ledger(coordinate_artifact: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": "twisted-yetter.yasui-character-twist-history-correction.v1",
        "status": "ESTABLISHED_NUMERIC_REINTERPRETATION",
        "mathematical_status": "NUMERIC_ARTIFACT_SYNTHESIS_AND_HISTORICAL_CORRECTION_NOT_THEOREM_LEVEL",
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/scripts/yasui_character_twist_history_correction.py",
        "claim_boundary": (
            "This ledger corrects the interpretation of existing Yasui character-twist "
            "artifacts. It does not rewrite old CTL objects, prove a theorem-level "
            "no-go result, or claim future exotic targets cannot be separated by "
            "character-twist functions."
        ),
        "terminology": {
            "standard_nonbaseline": (
                "The standard/split presentation has Z(alpha) != Z(0). This is an "
                "ordinary pointed/simple-current phase and is not a success criterion."
            ),
            "presentation_nonbaseline": (
                "A Yasui or other presentation has Z(alpha) != Z(0). This is still "
                "not separation unless the whole function is compared with the "
                "standard function under the correct coordinate identification."
            ),
            "exotic_vs_standard_separation": (
                "After the diffeomorphism-induced handle and character-basis "
                "identification, the exotic target's full character-twist function "
                "differs from the standard function. This is the intended goal."
            ),
        },
        "core_correction": {
            "standard_side_constancy": (
                "If a standard-side character-twist function is constant baseline, "
                "current project knowledge does not identify that as an obstruction "
                "to a future exotic-vs-standard separation. It only says the cheap "
                "standard/split phase is invisible in that case."
            ),
            "wrong_success_condition": (
                "Earlier excitement sometimes treated standard/split nonbaseline "
                "behavior as a positive research signal. This ledger demotes that "
                "behavior to sanity/candidate bookkeeping."
            ),
            "required_future_question": (
                "Does the exotic target's full character-twist function differ from "
                "the standard function after the correct coordinate identification?"
            ),
        },
        "case_summaries": {
            "su2_2_yasui_a1": su2_summary(SU2_A1),
            "su2_2_yasui_a3": su2_summary(SU2_A3),
            "su3_2_yasui_a1": {
                "coordinate_comparison_artifact": {
                    "path": rel(COORDINATE_OUTPUT),
                    "schema": coordinate_artifact["schema"],
                    "status": coordinate_artifact["status"],
                    "sha256": sha256(COORDINATE_OUTPUT),
                },
                "summary": coordinate_artifact["summary"],
                "interpretation": (
                    "The saved SU(3)_2 run is nonbaseline, but it matches the "
                    "CP2#2CPbar split function after the recorded character-coordinate "
                    "map. It should not be advertised as a Yasui-vs-standard "
                    "separation signal or as the first broad positive character-twist run."
                ),
            },
            "dic12_yasui_a1": dic12_summary(),
            "su2_k_k_0_mod_4": {
                "known_split_behavior": "For SU(2)_k with k congruent 0 mod 4, the saved split scan records baseline behavior for all character twists.",
                "interpretation": (
                    "This does not show the category is useless for every future exotic "
                    "target. It only says the standard/split cheap phase does not move."
                ),
            },
        },
        "historical_reinterpretation": {
            "su3_2_first_positive_wording": (
                "Misleading unless 'positive' is restricted to the local SU(3)_2 "
                "AnyonWiki F/R pipeline. SU(2)_2 all-alpha Yasui nonbaseline runs "
                "already existed, and in all current cases nonbaseline is not separation."
            ),
            "dic12_excitement": (
                "The D(Dic_12) result remains useful as an auditable pointed witness "
                "and component-translation check, but should not be treated as an "
                "exotic-sensitive signal."
            ),
            "special_handle_roadmap_preflight": (
                "Ordinary CP2/standard-side nontrivial character twist is a sanity "
                "or candidate-behavior check, not a necessary preflight and not a "
                "success criterion."
            ),
        },
        "future_agent_guardrail": (
            "Do not stop at asking whether a character twist changes a value on the "
            "standard or Yasui presentation. Compare full functions after the correct "
            "basis identification, and treat coordinate-only differences as negative "
            "separation evidence."
        ),
    }


def main() -> int:
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    coordinate_payload = su3_coordinate_comparison()
    coordinate_payload["utc_start"] = utc_start
    coordinate_payload["utc_finish"] = datetime.now(UTC).isoformat()
    coordinate_payload["elapsed_seconds"] = time.monotonic() - started
    coordinate_payload["repo"] = {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(command(["git", "status", "--short"])),
        "status_short": command(["git", "status", "--short"]),
    }
    write_json(COORDINATE_OUTPUT, coordinate_payload)

    ledger_payload = correction_ledger(coordinate_payload)
    ledger_payload["utc_start"] = utc_start
    ledger_payload["utc_finish"] = datetime.now(UTC).isoformat()
    ledger_payload["elapsed_seconds"] = time.monotonic() - started
    ledger_payload["repo"] = {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(command(["git", "status", "--short"])),
        "status_short": command(["git", "status", "--short"]),
    }
    write_json(LEDGER_OUTPUT, ledger_payload)

    print(
        json.dumps(
            {
                "status": "pass",
                "coordinate_artifact": rel(COORDINATE_OUTPUT),
                "ledger_artifact": rel(LEDGER_OUTPUT),
                "direct_same_tuple_nonmatching_count": coordinate_payload["summary"][
                    "direct_same_tuple_nonmatching_count"
                ],
                "mapped_nonmatching_count": coordinate_payload["summary"]["mapped_nonmatching_count"],
                "mapped_max_abs_difference": coordinate_payload["summary"]["mapped_max_abs_difference"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
