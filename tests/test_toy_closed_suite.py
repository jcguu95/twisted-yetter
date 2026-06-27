import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.decorated_kirby_gate import (
    DECORATED_MOVE_CERT_BLOCKER_ID,
    MATRIX_LEVEL_ONLY_BLOCKER_ID,
    N35_PLANNED_CALLS_BLOCKER_ID,
    NOT_GENERATED_LINK_MOVE_BLOCKER_ID,
    ORDINARY_SURGERY_BLOCKER_ID,
)
from twisted_yetter.ordinary_surgery_gate import (
    CLOSED_CLAIM_BLOCKER_ID,
    N22_BLOCKER_ID,
    N23_BLOCKER_ID,
    SOURCE_BLOCKER_ID,
)
from twisted_yetter.toy_closed_suite import (
    BLOCKED_CLAIMS,
    MISSING_PAIR_METADATA_BLOCKER_ID,
    N24_GATE_BLOCKER_ID,
    N50_GATE_BLOCKER_ID,
    NODE_ID,
    TOY_CLOSED_SUITE_SCHEMA,
    stable_toy_closed_suite_ledger_json,
    toy_closed_suite_ledger_artifact,
    validate_toy_closed_suite_ledger_artifact,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
SUITE_ARTIFACT = REPO_ROOT / "experiments/results/toy-suite/n55-toy-closed-suite.json"


def _assert_no_float(value: object) -> None:
    if isinstance(value, float):
        raise AssertionError(f"unexpected float value: {value!r}")
    if isinstance(value, dict):
        for item in value.values():
            _assert_no_float(item)
    elif isinstance(value, list | tuple):
        for item in value:
            _assert_no_float(item)


def test_n55_ledger_consumes_current_upstream_gates_and_blocks_final_suite() -> None:
    artifact = toy_closed_suite_ledger_artifact()

    assert artifact["schema"] == TOY_CLOSED_SUITE_SCHEMA
    assert artifact["status"] == "blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["claim_level"] == "blocked ledger/certificate"
    assert artifact["input_statuses"] == {
        "ordinary_surgery_gate": "blocked",
        "candidate_validation_suite": "pass",
        "presentation_pair_registry": "pass",
        "decorated_kirby_gate": "blocked",
    }
    assert artifact["global_blocker_reason_ids"] == [
        N24_GATE_BLOCKER_ID,
        N50_GATE_BLOCKER_ID,
    ]
    assert artifact["final_closed_suite_passed"] is False
    assert artifact["metadata_validation"]["valid"] is True


def test_n55_global_blockers_include_n24_and_n50_reason_ids() -> None:
    artifact = toy_closed_suite_ledger_artifact()
    blockers = {blocker["reason_id"]: blocker for blocker in artifact["global_blockers"]}

    n24 = blockers[N24_GATE_BLOCKER_ID]
    assert n24["observed"] == "blocked"
    assert n24["required"] == "pass"
    assert set(n24["upstream_blocker_reason_ids"]) == {
        SOURCE_BLOCKER_ID,
        N22_BLOCKER_ID,
        N23_BLOCKER_ID,
        CLOSED_CLAIM_BLOCKER_ID,
    }
    assert "closed 4-manifold invariant values" in n24["claim_boundary"]

    n50 = blockers[N50_GATE_BLOCKER_ID]
    assert n50["observed"] == "blocked"
    assert n50["required"] == "pass"
    assert n50["upstream_schema"] == "twisted-yetter.decorated-kirby-gate.v2"
    assert n50["classification_status_counts"] == {
        "blocked": 5,
        "metadata-only": 3,
        "not-applicable": 0,
        "pass": 0,
    }
    assert n50["pair_count"] == 8
    assert n50["diagram_pair_count"] == 5
    assert n50["matrix_pair_count"] == 3
    assert n50["evaluator_comparison_input_pair_ids"] == []
    assert ORDINARY_SURGERY_BLOCKER_ID in n50["upstream_pair_blocker_reason_ids"]
    assert DECORATED_MOVE_CERT_BLOCKER_ID in n50["upstream_pair_blocker_reason_ids"]
    assert MATRIX_LEVEL_ONLY_BLOCKER_ID in n50["upstream_pair_blocker_reason_ids"]
    assert N35_PLANNED_CALLS_BLOCKER_ID in n50["upstream_pair_blocker_reason_ids"]
    assert NOT_GENERATED_LINK_MOVE_BLOCKER_ID in n50["upstream_pair_blocker_reason_ids"]
    assert "decorated Kirby invariance evidence" in n50["claim_boundary"]


def test_n55_records_n50_classification_inventory_without_evaluator_inputs() -> None:
    artifact = toy_closed_suite_ledger_artifact()
    inventory = artifact["decorated_gate_inventory"]

    assert inventory == {
        "source_node": "n50-decorated-kirby-move-gate",
        "schema": "twisted-yetter.decorated-kirby-gate.v2",
        "status": "blocked",
        "classification_status_counts": {
            "blocked": 5,
            "metadata-only": 3,
            "not-applicable": 0,
            "pass": 0,
        },
        "pair_count": 8,
        "diagram_pair_count": 5,
        "matrix_pair_count": 3,
        "evaluator_comparison_input_pair_ids": [],
        "all_pairs_blocked_or_metadata_only": True,
        "all_pairs_have_structured_blockers": True,
        "claim_boundary": (
            "n55 may consume this classification inventory, but zero n50 "
            "pass pairs means no evaluator comparison inputs and no closed "
            "decorated invariant values"
        ),
    }
    assert artifact["metadata_validation"]["decorated_gate_inventory_ok"] is True


def test_toy_cases_record_upstream_readiness_and_case_refs() -> None:
    artifact = toy_closed_suite_ledger_artifact()
    cases = {case["case_id"]: case for case in artifact["toy_cases"]}

    assert set(cases) == {
        "s4-trivial-zero",
        "cp2-z2-zero",
        "cp2-z2-nonzero",
        "s2xs2-hopf-z2-mixed-10",
        "s2xs2-hopf-z2-mixed-01",
        "unlink-two-component-z2-zero",
        "unlink-two-component-z2-mixed",
        "unlink-two-component-z2-nonzero",
    }
    assert artifact["all_cases_have_diagram_metadata"] is True
    assert artifact["all_cases_have_decorated_core_metadata"] is True
    assert artifact["all_cases_have_pair_metadata"] is False

    paired = cases["cp2-z2-zero"]
    assert paired["upstream_readiness"] == {
        "diagram_metadata": True,
        "decorated_core_metadata": True,
        "presentation_pair_metadata": True,
    }
    assert paired["presentation_pair_refs"] == ["identity-cp2-z2-zero"]
    assert paired["blocked_reason_ids"] == [
        N24_GATE_BLOCKER_ID,
        N50_GATE_BLOCKER_ID,
    ]

    unpaired = cases["s2xs2-hopf-z2-mixed-10"]
    assert unpaired["upstream_readiness"]["diagram_metadata"] is True
    assert unpaired["upstream_readiness"]["decorated_core_metadata"] is True
    assert unpaired["upstream_readiness"]["presentation_pair_metadata"] is True
    assert unpaired["presentation_pair_refs"] == [
        "component-relabel-s2xs2-hopf-z2-mixed-swap-dry-run"
    ]
    assert unpaired["blocked_reason_ids"] == [
        N24_GATE_BLOCKER_ID,
        N50_GATE_BLOCKER_ID,
    ]

    still_unpaired = cases["unlink-two-component-z2-zero"]
    assert still_unpaired["upstream_readiness"]["presentation_pair_metadata"] is False
    assert still_unpaired["presentation_pair_refs"] == []
    assert MISSING_PAIR_METADATA_BLOCKER_ID in still_unpaired["blocked_reason_ids"]


def test_n55_refuses_closed_decorated_and_exotic_claim_promoters() -> None:
    artifact = toy_closed_suite_ledger_artifact()

    assert artifact["closed_4_manifold_invariant_claim_allowed"] is False
    assert artifact["ordinary_surgery_theorem_claim_allowed"] is False
    assert artifact["decorated_kirby_theorem_claim_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["blocked_claims"] == list(BLOCKED_CLAIMS)
    assert "closed 4-manifold invariant calculator" in artifact["claim_boundary"]

    with pytest.raises(ValueError, match="refuses closed 4-manifold invariant"):
        toy_closed_suite_ledger_artifact(claim_closed_invariant=True)
    with pytest.raises(ValueError, match="refuses closed 4-manifold invariant"):
        toy_closed_suite_ledger_artifact(claim_decorated_kirby_theorem=True)
    with pytest.raises(ValueError, match="refuses closed 4-manifold invariant"):
        toy_closed_suite_ledger_artifact(claim_exotic_detection=True)


def test_n55_ledger_json_is_stable_exact_and_float_free() -> None:
    first = toy_closed_suite_ledger_artifact()
    second = toy_closed_suite_ledger_artifact()

    first_json = stable_toy_closed_suite_ledger_json(first)
    second_json = stable_toy_closed_suite_ledger_json(second)
    assert first_json == second_json
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    assert ".0" not in first_json
    _assert_no_float(first)


def test_validator_rejects_missing_required_fields() -> None:
    validation = validate_toy_closed_suite_ledger_artifact(
        {"schema": TOY_CLOSED_SUITE_SCHEMA}
    )

    assert validation["valid"] is False
    assert "toy_cases" in validation["missing_required_fields"]


def test_checked_in_n55_certificate_records_blocked_ledger() -> None:
    certificate = json.loads(SUITE_ARTIFACT.read_text())

    validate_certificate(certificate)

    exact_output = certificate["exact_output"]
    assert certificate["status"] == "inconclusive"
    assert exact_output["schema"] == TOY_CLOSED_SUITE_SCHEMA
    assert exact_output["status"] == "blocked"
    assert exact_output["node_id"] == NODE_ID
    assert exact_output["final_closed_suite_passed"] is False
    assert exact_output["global_blocker_reason_ids"] == [
        N24_GATE_BLOCKER_ID,
        N50_GATE_BLOCKER_ID,
    ]
    assert exact_output["decorated_gate_inventory"]["pair_count"] == 8
    assert exact_output["decorated_gate_inventory"][
        "classification_status_counts"
    ] == {
        "blocked": 5,
        "metadata-only": 3,
        "not-applicable": 0,
        "pass": 0,
    }
    assert exact_output["decorated_gate_inventory"][
        "evaluator_comparison_input_pair_ids"
    ] == []
    assert exact_output["metadata_validation"]["valid"] is True
    assert exact_output["closed_4_manifold_invariant_claim_allowed"] is False
    assert exact_output["decorated_kirby_theorem_claim_allowed"] is False
    assert exact_output["exotic_detection_claim_allowed"] is False
