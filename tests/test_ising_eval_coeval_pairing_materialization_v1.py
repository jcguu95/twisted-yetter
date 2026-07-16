import importlib.util
import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = (
    ROOT
    / "experiments"
    / "scripts"
    / "build_ising_eval_coeval_pairing_materialization_v1.py"
)
SPEC = importlib.util.spec_from_file_location(
    "ising_eval_coeval_pairing_materialization_v1", SCRIPT
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_materialization() -> dict:
    return json.loads(
        (OUT / "ising-eval-coeval-pairing-materialization-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def assert_attempt_hash(attempt: dict) -> None:
    body = dict(attempt)
    attempt_hash = body.pop("attempt_hash")
    assert attempt_hash == stable_content_hash(body)


def test_ising_eval_coeval_materialization_blocks_without_formal_map_source() -> None:
    artifact = load_materialization()

    assert_content_hash(artifact)
    assert artifact["status"] == "ISING_EVAL_COEVAL_PAIRING_MATERIALIZATION_BLOCKED"
    assert artifact["attempt_count"] == 16
    assert artifact["blocked_attempt_count"] == 16
    assert artifact["materialized_map_count"] == 0
    assert artifact["materialized_pairing_count"] == 0
    assert artifact["formal_certificate_count"] == 0
    assert artifact["formal_snapshot_count"] == 0
    assert artifact["row_complete_status"] == "NOT_ROW_COMPLETE"
    assert artifact["formal_scan_plan_allowed"] is False
    assert set(artifact["checks"].values()) == {True}


def test_each_ising_eval_coeval_attempt_records_formulas_as_non_evidence() -> None:
    artifact = load_materialization()

    for attempt in artifact["attempt_records"]:
        assert_attempt_hash(attempt)
        assert attempt["attempt_status"] == (
            "BLOCKED_FORMAL_MAP_SOURCE_OR_BRANCH_CONVENTION_MISSING"
        )
        assert attempt["materialized_evaluation_coevaluation_maps"] is False
        assert attempt["materialized_fusion_pairing"] is False
        assert attempt["formal_certificate_produced"] is False
        assert attempt["formal_snapshot_produced"] is False
        assert "candidate_payload_hash" in attempt
        assert "source_branch_data_hash" in attempt

        formulas = attempt["proposed_map_formulas_not_formal_evidence"]
        assert set(formulas) == {"0", "1", "2"}
        assert formulas["0"]["left_evaluation_scalar_formula"] == "1"
        assert formulas["2"]["right_coevaluation_scalar_formula"] == "1"
        assert formulas["1"]["left_evaluation_scalar_formula"].startswith("sqrt(")

        pairing = attempt["proposed_pairing_not_formal_evidence"]
        assert pairing["basis_gauge"].startswith("multiplicity-free SU(2)_k")
        assert pairing["fusion_channels"]
        for channel in pairing["fusion_channels"].values():
            assert channel["pairing_matrix"] == [["1"]]
            assert channel["inverse_pairing_matrix"] == [["1"]]


def test_ising_eval_coeval_attempts_preserve_precise_blockers() -> None:
    artifact = load_materialization()

    required = {
        "numeric_su2k_pivotal_profile_not_formal_certificate",
        "su2k_evaluator_has_no_formal_eval_coeval_map_exporter",
        "square_root_branch_for_candidate_pivotal_dimensions_not_formally_pinned",
        "fusion_pairing_orthonormality_not_formally_certified_for_row_completion",
        "candidate_galois_branch_sqrt_convention_not_row_certified",
    }
    for attempt in artifact["attempt_records"]:
        assert required.issubset(set(attempt["blockers"]))

    assert any(
        "Need square-root branch choices" in item
        for item in artifact["blocking_requirements_summary"]
    )
    assert any(
        "does not materialize formal evaluation/coevaluation maps" in item
        for item in artifact["explicit_non_claims"]
    )


def test_generator_rebuilds_ising_eval_coeval_materialization_shape() -> None:
    artifacts = MODULE.build_all()
    artifact = artifacts["ising-eval-coeval-pairing-materialization-v1.json"]

    assert artifact["status"] == "ISING_EVAL_COEVAL_PAIRING_MATERIALIZATION_BLOCKED"
    assert artifact["attempt_count"] == 16
    assert artifact["blocked_attempt_count"] == 16
    assert artifact["materialized_map_count"] == 0
    assert len(artifact["attempt_records"]) == 16
