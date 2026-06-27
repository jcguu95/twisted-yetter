import json

import pytest

from twisted_yetter.finite_groups import TRIVIAL_GROUP, Z2_GROUP, cyclic_group
from twisted_yetter.omega_a import (
    BLOCKED_HIGH_CLAIMS,
    DEFAULT_Z2_LABEL_CHARACTER_ASSIGNMENT,
    DOES_NOT_COMPUTE,
    OMEGA_A_SCHEMA,
    omega_a_candidate_artifact_certificate,
    omega_a_candidate_certificate,
    stable_omega_a_json,
)
from twisted_yetter.artifacts import dumps_certificate
from twisted_yetter.omega_a_contract import OMEGA_A_CANDIDATE_FORMULA_ID
from twisted_yetter.ordinary_kirby_color import omega_coefficients
from twisted_yetter.su2_level2 import SQRT2, QuadraticSurd


def test_trivial_group_specializes_to_ordinary_omega_coefficients() -> None:
    certificate = omega_a_candidate_certificate(TRIVIAL_GROUP)

    assert certificate["schema"] == OMEGA_A_SCHEMA
    assert certificate["status"] == "pass"
    assert certificate["claim_level"] == "candidate-experimental"
    assert certificate["candidate_formula_id"] == OMEGA_A_CANDIDATE_FORMULA_ID
    assert certificate["finite_group_id"] == "trivial"
    assert certificate["ordinary_surgery_gate_status"] == "blocked"
    assert certificate["metadata_validation"]["valid"] is True
    assert certificate["closed_4_manifold_claim_allowed"] is False
    assert certificate["theorem_claim_allowed"] is False
    assert certificate["exotic_detection_claim_allowed"] is False

    assert certificate["ordinary_omega_coefficients"] == {
        label: omega_coefficients()[label].to_jsonable()
        for label in ("0", "1", "2")
    }
    assert certificate["sectors"] == [
        {
            "sector_id": "e",
            "element": [],
            "coefficients": [
                _coefficient("0", "trivial", 1, QuadraticSurd(1)),
                _coefficient("1", "trivial", 1, SQRT2),
                _coefficient("2", "trivial", 1, QuadraticSurd(1)),
            ],
        }
    ]


def test_z2_nontrivial_sector_uses_explicit_local_sign_assignment() -> None:
    certificate = omega_a_candidate_certificate(Z2_GROUP)

    assert certificate["finite_group_id"] == "Z/2"
    assert certificate["character_table_source"] == "twisted_yetter.finite_groups:Z2_GROUP"
    assert certificate["character_orthogonality_status"] == "pass/exact inherited from n11"
    assert certificate["label_character_assignment"] == {
        "status": "candidate/local",
        "source_status": (
            "candidate/local assignment; not sourced as a Yetter theorem"
        ),
        "finite_group_id": "Z/2",
        "assignment": {"0": "chi_0", "1": "chi_1", "2": "chi_0"},
        "interpretation": (
            "For Z/2 this local scaffold assigns the middle SU(2)_2 label 1 "
            "to the sign character and labels 0,2 to the trivial character; "
            "this realizes the sign-weighted theta-style target only as a "
            "candidate/local convention."
        ),
    }
    assert DEFAULT_Z2_LABEL_CHARACTER_ASSIGNMENT == {
        "0": (0,),
        "1": (1,),
        "2": (0,),
    }

    sectors = {sector["sector_id"]: sector for sector in certificate["sectors"]}
    assert list(sectors) == ["0", "1"]
    assert sectors["0"]["coefficients"] == [
        _coefficient("0", "chi_0", 1, QuadraticSurd(1)),
        _coefficient("1", "chi_1", 1, SQRT2),
        _coefficient("2", "chi_0", 1, QuadraticSurd(1)),
    ]
    assert sectors["1"]["coefficients"] == [
        _coefficient("0", "chi_0", 1, QuadraticSurd(1)),
        _coefficient("1", "chi_1", -1, -SQRT2),
        _coefficient("2", "chi_0", 1, QuadraticSurd(1)),
    ]


def test_certificate_json_is_stable_and_has_no_float_markers() -> None:
    first = omega_a_candidate_certificate(Z2_GROUP)
    second = omega_a_candidate_certificate(Z2_GROUP)

    assert first == second
    assert stable_omega_a_json(first) == stable_omega_a_json(second)
    assert json.loads(stable_omega_a_json(first)) == first
    assert ".0" not in stable_omega_a_json(first)


def test_artifact_bundle_preserves_n32_metadata_for_supported_groups() -> None:
    artifact = omega_a_candidate_artifact_certificate()
    exact_output = artifact["exact_output"]
    groups = exact_output["groups"]

    assert artifact["schema"] == "twisted-yetter.certificate.v1"
    assert artifact["status"] == "pass"
    assert exact_output["node_id"] == "n33-omega-a-implementation"
    assert exact_output["claim_level"] == "candidate-experimental"
    assert exact_output["candidate_formula_id"] == OMEGA_A_CANDIDATE_FORMULA_ID
    assert exact_output["ordinary_surgery_gate_status"] == "blocked"
    assert set(groups) == {"trivial", "Z/2"}
    for certificate in groups.values():
        assert certificate["metadata_validation"]["valid"] is True
        assert certificate["marking_basis_status"].startswith("not-in-scope")
        assert certificate["ordinary_surgery_gate_status"] == "blocked"

    encoded = dumps_certificate(artifact)
    assert json.loads(encoded) == artifact
    assert ".0" not in encoded


def test_high_claims_are_blocked_or_absent_from_n33_artifact() -> None:
    certificate = omega_a_candidate_certificate(Z2_GROUP)

    assert certificate["blocked_high_claims"] == list(BLOCKED_HIGH_CLAIMS)
    assert "exotic detection claim" in certificate["blocked_high_claims"]
    assert "claim-supporting closed 4D invariant" in certificate["blocked_high_claims"]
    assert "closed 4-manifold invariant" in certificate["does_not_compute"]
    assert "exotic smooth-structure detection evidence" in certificate["does_not_compute"]
    assert set(certificate["does_not_compute"]) == set(DOES_NOT_COMPUTE)
    encoded = stable_omega_a_json(certificate)
    assert "detected exotic" not in encoded
    assert "closed homologically twisted Yetter invariant" not in encoded


def test_character_table_metadata_is_inherited_exactly() -> None:
    certificate = omega_a_candidate_certificate(Z2_GROUP)
    finite_group_certificate = certificate["character_table_certificate"]

    assert finite_group_certificate["schema"] == (
        "twisted-yetter.finite-abelian-character-data.v1"
    )
    assert finite_group_certificate["status"] == "pass"
    assert finite_group_certificate["character_table"]["chi_1"]["1"] == {
        "type": "integer",
        "value": "-1",
    }


def test_unsupported_group_and_bad_assignment_are_rejected() -> None:
    with pytest.raises(ValueError, match="unsupported exact cyclic character table"):
        cyclic_group(3)

    with pytest.raises(ValueError, match="unknown character"):
        omega_a_candidate_certificate(Z2_GROUP, label_character_assignment={
            "0": (0,),
            "1": (2,),
            "2": (0,),
        })


def _coefficient(
    label: str,
    character_label: str,
    character_value: int,
    candidate_coefficient: QuadraticSurd,
) -> dict[str, object]:
    return {
        "label": label,
        "ordinary_dimension_coefficient": omega_coefficients()[label].to_jsonable(),
        "character_label": character_label,
        "character_value": {"type": "integer", "value": str(character_value)},
        "candidate_coefficient": candidate_coefficient.to_jsonable(),
        "coefficient_formula": "d_i * lambda_i(a)",
    }
