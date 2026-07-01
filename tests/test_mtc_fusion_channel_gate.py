import json
from pathlib import Path


ARTIFACT = Path("experiments/results/mtc-candidates/mtc-fusion-channel-gate-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_fusion_channel_gate_records_scope_and_boundaries() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.mtc-fusion-channel-gate.v1"
    assert "fusion-channel evidence" in exact["claim_level"]
    assert "full local-piece F/R evaluator" in exact["not_scope"]
    assert [item["status"] for item in exact["validations"]] == ["pass", "pass", "pass"]


def test_su2_6_step3_hopf_star_controls_are_nontrivial() -> None:
    exact = _exact_output()
    step3 = exact["step_3_su2_6_hopf_star_fusion_channel_gate"]

    assert step3["status"] == "pass"
    assert step3["target_simple_currents"] == {"0": "0", "1": "6"}

    controls = {item["name"]: item for item in step3["controls"]}
    assert controls["1x1_omega0_keeps_vacuum"]["actual_global_dimension_multiplier"] == 1
    assert controls["1x1_omega1_rejects_simple_current"]["actual_global_dimension_multiplier"] == 0
    assert controls["3x3_omega1_keeps_simple_current"]["actual_global_dimension_multiplier"] == 1
    assert controls["2x4_omega0_rejects_vacuum"]["actual_global_dimension_multiplier"] == 0
    assert controls["2x4_omega1_keeps_simple_current"]["actual_global_dimension_multiplier"] == 1


def test_su2_6_step4_shows_linking_matrix_is_not_enough() -> None:
    exact = _exact_output()
    step4 = exact["step_4_su2_6_pressure_controls"]

    assert step4["status"] == "pass"
    assert step4["associativity_triple_count"] == 343
    assert step4["associativity_failure_count"] == 0

    witnesses = step4["same_linking_matrix_not_enough_witnesses"]
    assert len(witnesses) == 2
    assert {item["status"] for item in witnesses} == {"pass"}
    assert witnesses[0]["left_multiplier"] != witnesses[0]["right_multiplier"]
    assert witnesses[1]["left_multiplier"] != witnesses[1]["right_multiplier"]
    assert all("linking-matrix-only evaluator would be wrong" in item["interpretation"] for item in witnesses)


def test_su3_2_step5_is_a_structured_blocker_not_a_fake_evaluator() -> None:
    exact = _exact_output()
    step5 = exact["step_5_su3_2_next_candidate_gate"]

    assert step5["status"] == "pass"
    assert step5["readiness"] == "structured-blocker"
    assert step5["invertible_labels_detected_from_dimension_one"] == ["(0,0)", "(2,0)", "(0,2)"]
    assert step5["blocker"]["reason_id"] == "su3-2-projector-target-map-not-yet-certified"
    assert "full F/R-symbol backend" in step5["blocker"]["message"]
    assert step5["fusion_channel_samples"]
