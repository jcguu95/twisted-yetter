from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "experiments/scripts/build_twisted_yetter_no_go_computational_audit_v1.py"
)
SPEC = importlib.util.spec_from_file_location("twisted_yetter_no_go_audit_v1", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

AuditError = MODULE.AuditError
build_audit = MODULE.build_audit
comparison_inventory_entry = MODULE._comparison_inventory_entry
content_hash = MODULE._content_hash


def _mutated_input(tmp_path: Path, relative: str, mutate) -> Path:
    source = REPO_ROOT / relative
    payload = json.loads(source.read_text())
    mutate(payload)
    output = tmp_path / source.name
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return output


def test_audit_establishes_only_the_computational_theorem() -> None:
    payload = build_audit()
    assert payload["status"] == (
        "PASS_COMPATIBLE_WITH_EXPLICIT_FIGURE21_NORMALIZATION_DISCREPANCY"
    )
    assert payload["conditional_mathematical_theorem"]["status"] == (
        "CONDITIONAL_PROPOSITION_NOT_YET_ESTABLISHED_AS_PROJECT_THEOREM"
    )
    theorem = payload["established_computational_theorem"]
    assert theorem["status"] == (
        "ESTABLISHED_MACHINE_CHECKED_STATEMENT_ABOUT_RETAINED_ARTIFACTS"
    )
    counts = theorem["machine_checked_counts"]
    assert counts["figure21_pointed_realization_count"] == 15
    assert counts["figure21_raw_exact_pointed_rows"] == 13
    assert counts["figure21_phase_only_pointed_rows"] == 2
    assert counts["figure21_certified_h2_marked_pointwise_rows"] == 0
    assert counts["certified_counterexample_count"] == 0


def test_audit_keeps_rank2_phase_and_premodular_guardrails_visible() -> None:
    payload = build_audit()
    figure21 = next(
        row for row in payload["evidence_groups"] if row["id"] == "figure21-pointed-rank2-5"
    )
    assert figure21["result"] == "13_RAW_EXACT_AND_2_PHASE_ALIGNED"
    assert "global -1 discrepancy" in figure21["caveat"]
    dispositions = {
        row["id"]: row["disposition"] for row in payload["excluded_or_downgraded"]
    }
    assert dispositions["figure21-premodular"] == (
        "OUT_OF_THEOREM_DENOMINATOR_FIXED_SECTOR_CONTROLS_ONLY"
    )
    assert dispositions["figure21-missing-framing-run"] == (
        "REJECTED_HISTORICAL_RESULT_KNOWN_FRAMING_BUG"
    )


def test_audit_fails_if_rank2_raw_discrepancy_is_hidden(tmp_path: Path) -> None:
    path = _mutated_input(
        tmp_path,
        "experiments/results/akbulut-yasui/"
        "figure21-rank2-rank3-standard-comparison-v1.json",
        lambda value: value.__setitem__("differing_row_count", 0),
    )
    with pytest.raises(AuditError, match="raw discrepancy"):
        build_audit({"figure21_rank23": path})


def test_audit_fails_if_completed_yasui_row_is_missing(tmp_path: Path) -> None:
    def mutate(value):
        value["rows"] = copy.deepcopy(value["rows"][:-1])

    path = _mutated_input(
        tmp_path,
        "experiments/results/yasui/"
        "figure3-a1-r1-normalized-su2-8-all-alpha-raw-comparison-v3.json",
        mutate,
    )
    with pytest.raises(AuditError, match="expected 8 rows"):
        build_audit({"yasui_a1_su28": path})


def test_audit_fails_if_known_bad_framing_run_loses_unsafe_status(
    tmp_path: Path,
) -> None:
    path = _mutated_input(
        tmp_path,
        "experiments/results/akbulut-yasui/"
        "figure21-right-su2-2-blackboard-framing-omission-run-v1.json",
        lambda value: value.__setitem__("status", "PASS"),
    )
    with pytest.raises(AuditError, match="unsafe marker"):
        build_audit({"figure21_bad_framing": path})


def test_downgraded_comparison_cannot_silently_become_pass(tmp_path: Path) -> None:
    path = tmp_path / "blocked-comparison.json"
    path.write_text(
        json.dumps(
            {
                "schema": "test.blocked-comparison.v1",
                "status": "pass",
            }
        )
    )
    with pytest.raises(AuditError, match="inconsistent"):
        comparison_inventory_entry(path, "BLOCKED")


def test_checked_in_audit_is_content_addressed_and_clean_generated() -> None:
    path = (
        REPO_ROOT
        / "experiments/results/theory/"
        "twisted-yetter-stable-no-go-computational-audit-v1.json"
    )
    payload = json.loads(path.read_text())
    recorded_hash = payload.pop("content_hash")
    assert content_hash(payload) == recorded_hash
    assert payload["git_dirty_before_output_write"] is False
    inventory = payload["comparison_file_inventory"]
    assert len(inventory) == 24
    assert all(row["sha256"].startswith("sha256:") for row in inventory)
