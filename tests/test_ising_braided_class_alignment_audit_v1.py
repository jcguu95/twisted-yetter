import importlib.util
import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_ising_braided_class_alignment_audit_v1.py"
SPEC = importlib.util.spec_from_file_location("ising_braided_alignment_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_audit() -> dict:
    return json.loads(
        (OUT / "ising-braided-class-alignment-audit-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def test_ising_braided_alignment_covers_all_eight_theta_sigma_classes() -> None:
    audit = load_audit()

    assert_content_hash(audit)
    assert audit["status"] == (
        "ISING_BRAIDED_CLASS_ALIGNMENT_BY_THETA_SIGMA_ESTABLISHED_RIBBON_LIFTS_PENDING"
    )
    assert audit["braided_class_alignment_status"] == "PASS"
    assert audit["ribbon_lift_status"] == "NOT_MATERIALIZED"
    assert audit["row_complete_status"] == "NOT_ROW_COMPLETE"
    assert set(audit["checks"].values()) == {True}
    assert audit["input_artifacts"]["classification_matrix"]["modular_braided_class_count"] == 8
    assert audit["input_artifacts"]["classification_matrix"][
        "spherical_structures_per_braided_class"
    ] == 2

    records = audit["candidate_branch_records"]
    assert len(records) == 8
    assert [record["theta_sigma_zeta16_power"] for record in records] == [
        1,
        3,
        5,
        7,
        9,
        11,
        13,
        15,
    ]
    assert {record["braided_class_id"] for record in records} == {
        f"rank3-ising:theta_sigma=zeta16^{power}"
        for power in range(1, 16, 2)
    }
    assert all(record["theta_psi"] == "-1" for record in records)
    assert all(record["formal_ribbon_lifts_materialized"] is False for record in records)


def test_ising_alignment_records_mirror_reverse_pairs_without_resolving_lifts() -> None:
    audit = load_audit()

    assert audit["mirror_reverse_pairs_by_theta_sigma"] == [
        {"pair": [1, 15]},
        {"pair": [3, 13]},
        {"pair": [5, 11]},
        {"pair": [7, 9]},
    ]
    by_exponent = {
        record["theta_sigma_zeta16_power"]: record
        for record in audit["candidate_branch_records"]
    }
    for exponent, reverse_exponent in [(1, 15), (3, 13), (5, 11), (7, 9)]:
        assert by_exponent[exponent]["mirror_reverse_theta_sigma_zeta16_power"] == (
            reverse_exponent
        )
        assert by_exponent[reverse_exponent][
            "mirror_reverse_theta_sigma_zeta16_power"
        ] == exponent

    assert any("does not establish Ising row-complete" in item for item in audit["explicit_non_claims"])
    assert any("materialize pivotal/ribbon lifts" in item for item in audit["remaining_growth"])


def test_generator_rebuilds_ising_alignment_audit_shape() -> None:
    artifacts = MODULE.build_all()
    audit = artifacts["ising-braided-class-alignment-audit-v1.json"]

    assert audit["braided_class_alignment_status"] == "PASS"
    assert audit["ribbon_lift_status"] == "NOT_MATERIALIZED"
    assert audit["row_complete_status"] == "NOT_ROW_COMPLETE"
    assert len(audit["candidate_branch_records"]) == 8
