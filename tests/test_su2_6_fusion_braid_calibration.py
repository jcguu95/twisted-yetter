import json
from decimal import Decimal
from pathlib import Path


ARTIFACT = Path("experiments/results/sage-stress/su2-6-fusion-braid-calibration-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_su2_6_fusion_braid_calibration_records_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su2-6-fusion-braid-calibration.v1"
    assert exact["category_id"] == "SU(2)_6"
    assert "fusion-braid evaluator" in exact["claim_level"]
    assert "Yasui diagram admission" in exact["not_scope"]
    assert "arbitrary MTC evaluator" in exact["not_scope"]


def test_su2_6_fusion_braid_calibration_all_groups_pass() -> None:
    exact = _exact_output()
    groups = {group["name"]: group for group in exact["control_groups"]}

    assert set(groups) == {
        "fixed_unknot",
        "split_unlink",
        "positive_hopf",
        "one_component_braid_knot",
        "omega_expansion",
    }
    assert {group["status"] for group in groups.values()} == {"pass"}
    assert {len(group["sample_failures"]) for group in groups.values()} == {0}
    assert groups["fixed_unknot"]["control_count"] == 35
    assert groups["split_unlink"]["control_count"] == 98
    assert groups["positive_hopf"]["control_count"] == 98
    assert groups["one_component_braid_knot"]["control_count"] == 56
    assert groups["omega_expansion"]["control_count"] == 8


def test_su2_6_fusion_braid_calibration_is_numerically_tight() -> None:
    exact = _exact_output()

    assert Decimal(exact["max_abs_difference"]) < Decimal("1e-10")
    assert all(
        Decimal(group["max_abs_difference"]) < Decimal("1e-10")
        for group in exact["control_groups"]
    )


def test_su2_6_colored_jones_q_convention_is_recorded() -> None:
    exact = _exact_output()

    notes = exact["convention_notes"]
    assert any("q=A^4 for even simple labels" in note for note in notes)
    assert any("q=A^-4 for odd simple labels" in note for note in notes)
    assert any("degree-linking phase" in note and "not applied at level 6" in note for note in notes)
