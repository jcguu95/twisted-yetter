import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_step2_input_materialization_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_step2_materialization_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


BLOCKED_ROW_ORDER = [
    "rank3-ising",
    "rank3-psu2-5",
    "rank4-psu2-7",
    "rank5-su2-4",
    "rank5-psu2-9",
    "rank5-psu3-4",
]


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def attempts_by_family(payload: dict) -> dict[str, dict]:
    return {item["family_id"]: item for item in payload["attempts"]}


def test_step2_materialization_records_all_six_rows_without_resolving_them() -> None:
    payload = load_json("low-rank-step2-input-materialization-v1.json")

    assert payload["status"] == "STEP2_INPUT_MATERIALIZATION_COMPLETE_TERMINAL_BLOCKED"
    assert payload["step"] == "implementation_order_step_2_resolve_the_6_blocked_rows"
    assert payload["blocked_family_ids"] == BLOCKED_ROW_ORDER
    assert payload["resolved_row_count_after_step2"] == 0
    assert payload["terminal_blocked_row_count_after_step2"] == 6
    assert payload["formal_scan_plan_allowed_after_step2"] is False
    assert "No blocked row is resolved by this Step 2 pass." in payload[
        "explicit_non_claims"
    ]

    for attempt in payload["attempts"]:
        assert attempt["formal_row_resolution_after_step2"] == "NOT_RESOLVED"
        assert attempt["formal_admission_allowed"] is False
        assert attempt["existing_snapshot_paths"] == []
        assert "content-addressed ribbon_realization_snapshot artifacts for every branch" in attempt[
            "required_outputs"
        ]


def test_step2_distinguishes_partial_su2k_machinery_from_complete_row_inputs() -> None:
    payload = load_json("low-rank-step2-input-materialization-v1.json")
    attempts = attempts_by_family(payload)

    ising = attempts["rank3-ising"]
    assert ising["materialization_status"] == (
        "PARTIAL_LOCAL_BRANCH_DATA_AVAILABLE_NOT_ROW_RESOLVED"
    )
    assert any("all-sigma" in item for item in ising["available_input_scope"])
    assert any("not full mixed-label" in item for item in ising["why_not_resolved"])

    for family_id in ["rank3-psu2-5", "rank4-psu2-7", "rank5-psu2-9"]:
        attempt = attempts[family_id]
        assert attempt["materialization_status"] == (
            "PRINCIPAL_SU2K_Q6J_BACKEND_AVAILABLE_NOT_ROW_RESOLVED"
        )
        assert any("principal-branch" in item for item in attempt["available_input_scope"])
        assert any("family row denominator" in item for item in attempt["why_not_resolved"])

    su24 = attempts["rank5-su2-4"]
    assert su24["materialization_status"] == (
        "PRINCIPAL_SU2K_BACKEND_AVAILABLE_EXTENSION_BRANCHES_NOT_RESOLVED"
    )
    assert any("Rep(S3)" in item for item in su24["why_not_resolved"])


def test_step2_records_psu3_as_missing_repo_local_fr_input() -> None:
    payload = load_json("low-rank-step2-input-materialization-v1.json")
    psu3 = attempts_by_family(payload)["rank5-psu3-4"]

    assert psu3["materialization_status"] == "NO_REPO_LOCAL_PSU3_FR_INPUT_AVAILABLE"
    assert psu3["available_inputs"] == []
    assert any("multiplicity-two" in item for item in psu3["why_not_resolved"])
    assert any("producer/runtime coherence certificate" in item for item in psu3["why_not_resolved"])


def test_generator_builds_consistent_step2_materialization_artifact() -> None:
    artifacts = MODULE.build_all()
    payload = artifacts["low-rank-step2-input-materialization-v1.json"]

    assert payload["status"] == "STEP2_INPUT_MATERIALIZATION_COMPLETE_TERMINAL_BLOCKED"
    assert payload["blocked_family_ids"] == BLOCKED_ROW_ORDER
    assert payload["resolved_row_count_after_step2"] == 0
    assert payload["terminal_blocked_row_count_after_step2"] == 6
