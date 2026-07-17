from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "experiments/scripts/"
    "build_twisted_yetter_quadratic_block_prediction_audit_v1.py"
)
SPEC = importlib.util.spec_from_file_location("quadratic_block_prediction_audit_v1", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

AuditError = MODULE.AuditError
build_audit = MODULE.build_audit
content_hash = MODULE._content_hash
even_block_analysis = MODULE.even_block_analysis
REFERENCE_LEDGER = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "twisted-yetter-quadratic-block-primary-sources-v1.json"
)


def _mutated_input(tmp_path: Path, relative: str, mutate) -> Path:
    source = REPO_ROOT / relative
    payload = json.loads(source.read_text())
    mutate(payload)
    output = tmp_path / source.name
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return output


def test_all_eligible_marked_data_match_the_prediction() -> None:
    payload = build_audit()
    assert payload["status"] == (
        "PASS_ALL_ELIGIBLE_H2_MARKED_DATA_MATCH_QUADRATIC_BLOCK_PREDICTION_"
        "FIGURE21_POINTWISE_BLOCKED"
    )
    result = payload["machine_checked_result"]
    assert result["eligible_h2_marked_artifact_row_count"] == 201
    assert result["su2_all_alpha_table_count"] == 9
    assert result["su2_all_alpha_row_count"] == 72
    assert result["su3_figure3_all_alpha_row_count"] == 27
    assert result["su3_general_form_control_row_count"] == 72
    assert result["da4_split_all_alpha_row_count"] == 27
    assert result["certified_counterexample_count"] == 0


def test_off_diagonal_and_coordinate_witnesses_are_nonvacuous() -> None:
    payload = build_audit()
    result = payload["machine_checked_result"]
    assert result["off_diagonal_mutual_intersection_witness_count"] > 0
    assert result["wrong_direct_Q_model_mismatch_count"] > 0
    group = payload["evidence_groups"]["su3_general_intersection_forms"]
    assert group["formula"] == "phase(lambda)=zeta3^(lambda^T Q^(-1) lambda)"


def test_figure21_is_not_promoted_to_an_all_alpha_check() -> None:
    payload = build_audit()
    figure21 = payload["evidence_groups"]["figure21_exotic_target"]
    assert figure21["status"] == (
        "DISTRIBUTION_LEVEL_COMPATIBLE_BLOCKED_FOR_POINTWISE_QUADRATIC_AUDIT"
    )
    assert figure21["certified_h2_marked_pointwise_row_count"] == 0
    assert figure21["raw_graph_distribution_match_count"] == 13
    assert figure21["ordinary_normalized_distribution_match_count"] == 15
    assert figure21["nonidentity_presentation_correction_count"] == 2


def test_eleven_eighths_role_is_arithmetically_explicit() -> None:
    boundary = even_block_analysis(2, 6)
    assert boundary["eleven_eighths_inequality_holds"] is True
    assert boundary["unstabilized_standard_model"] == {
        "signed_K3_count": 2,
        "S2xS2_count": 0,
    }
    violating = even_block_analysis(2, 5)
    assert violating["eleven_eighths_inequality_holds"] is False
    assert violating["unstabilized_standard_model"] is None
    assert violating["minimum_algebraic_H_stabilizations_for_standard_block_form"] == 1


def test_su2_standard_value_mutation_fails_closed(tmp_path: Path) -> None:
    relative = (
        "experiments/results/yasui/"
        "figure3-a1-r1-normalized-su2-3-all-alpha-raw-comparison-v2.json"
    )

    def mutate(payload):
        payload["rows"][3]["standard_value"]["real"] = "123.0"

    path = _mutated_input(tmp_path, relative, mutate)
    with pytest.raises(AuditError, match="block-to-standard"):
        build_audit({"yasui-figure3-a1-su2-3": path})


def test_su3_off_diagonal_value_mutation_fails_closed(tmp_path: Path) -> None:
    relative = (
        "experiments/results/small-handle-examples/"
        "su3-2-standard-form-character-controls-v1.json"
    )

    def mutate(payload):
        example = next(
            item
            for item in payload["examples"]
            if item["id"] == "s2xs2-one-dotted-three-two-handles"
        )
        row = next(
            item
            for item in example["rows"]
            if item["values_on_h2_quotient_basis"] == [1, 1]
        )
        row["baseline_ratio"]["real"] = "1.0"
        row["baseline_ratio"]["imag"] = "0.0"

    path = _mutated_input(tmp_path, relative, mutate)
    with pytest.raises(AuditError, match="small-handle quadratic prediction"):
        build_audit({"su3_small_handles": path})


def test_figure21_missing_marking_guard_fails_closed(tmp_path: Path) -> None:
    relative = (
        "experiments/results/theory/"
        "twisted-yetter-stable-no-go-computational-audit-v1.json"
    )

    def mutate(payload):
        payload["established_computational_theorem"]["machine_checked_counts"][
            "figure21_certified_h2_marked_pointwise_rows"
        ] = 1

    path = _mutated_input(tmp_path, relative, mutate)
    with pytest.raises(AuditError, match="H2-marked"):
        build_audit({"figure21_compatibility": path})


def test_checked_in_artifact_is_content_addressed_and_clean_generated() -> None:
    path = (
        REPO_ROOT
        / "experiments/results/theory/"
        "twisted-yetter-quadratic-block-prediction-audit-v1.json"
    )
    payload = json.loads(path.read_text())
    recorded_hash = payload.pop("content_hash")
    assert content_hash(payload) == recorded_hash
    assert payload["repo"]["dirty_before_output_write"] is False
    assert all(
        row["sha256"].startswith("sha256:")
        for row in payload["input_artifacts"]
    )


def test_primary_source_ledger_pins_the_required_locators_and_guardrails() -> None:
    ledger = json.loads(REFERENCE_LEDGER.read_text())
    references = {
        row["reference_id"]: row for row in ledger["references"]
    }
    assert set(references) == {
        "ref:freedman-topology-four-dimensional-manifolds-1982",
        "ref:furuta-monopole-11-8-2001",
        "ref:yetter-homologically-twisted-hepth-9311082",
        "ref:cky-state-sum-hepth-9409167",
    }
    assert all(
        len(row["snapshot"]["sha256"]) == 64 for row in references.values()
    )
    assert references[
        "ref:freedman-topology-four-dimensional-manifolds-1982"
    ]["locators"][0]["location"] == "Theorem 1.5"
    assert references["ref:furuta-monopole-11-8-2001"]["locators"][0][
        "printed_page"
    ] == 279
    assert "still presented as a conjecture" in ledger[
        "current_status_reference"
    ]["status_fact"]
    guardrails = " ".join(ledger["scope_guardrails"])
    assert "not the tangent-bundle class p1(TM)" in guardrails
