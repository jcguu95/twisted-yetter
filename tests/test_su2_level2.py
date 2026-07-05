import json

import pytest

from twisted_yetter.legacy_prose import legacy_prose_member_ref
from twisted_yetter.su2_level2 import (
    GLOBAL_DIMENSION,
    LINK_DATA_CLAIM_LEVELS,
    OMEGA_THETA_CONVENTION,
    QUANTUM_DIMENSIONS,
    S_MATRIX,
    SIMPLE_LABELS,
    SQRT2,
    TWIST_VALUES,
    UNSUPPORTED_DATA,
    QuadraticSurd,
    RootOfUnityPower,
    certificate_payload,
    fusion,
    global_dimension_from_simples,
    hopf_control_entry,
    s_matrix_entry,
    validate_certificate,
)


def test_simple_labels_and_dimensions_are_exact() -> None:
    assert SIMPLE_LABELS == ("0", "1", "2")
    assert QUANTUM_DIMENSIONS == {
        "0": QuadraticSurd(1),
        "1": SQRT2,
        "2": QuadraticSurd(1),
    }
    assert SQRT2 * SQRT2 == QuadraticSurd(2)


def test_fusion_rules_are_the_su2_level2_fusion_ring() -> None:
    assert fusion("0", "1") == {"1": 1}
    assert fusion("1", "1") == {"0": 1, "2": 1}
    assert fusion("1", "2") == {"1": 1}
    assert fusion("2", "2") == {"0": 1}


def test_unknown_simple_label_is_rejected() -> None:
    with pytest.raises(ValueError, match="unknown SU\\(2\\)_2 simple label"):
        fusion("1", "3")


def test_global_dimension_sanity_check_passes() -> None:
    assert global_dimension_from_simples() == QuadraticSurd(4)
    assert GLOBAL_DIMENSION == QuadraticSurd(4)
    validate_certificate()


def test_s_matrix_is_exact_symmetric_and_recovers_dimensions() -> None:
    assert S_MATRIX == (
        (QuadraticSurd("1/2"), QuadraticSurd(0, "1/2"), QuadraticSurd("1/2")),
        (QuadraticSurd(0, "1/2"), QuadraticSurd(0), QuadraticSurd(0, "-1/2")),
        (QuadraticSurd("1/2"), QuadraticSurd(0, "-1/2"), QuadraticSurd("1/2")),
    )

    for left in SIMPLE_LABELS:
        for right in SIMPLE_LABELS:
            assert s_matrix_entry(left, right) == s_matrix_entry(right, left)
            assert (
                s_matrix_entry("0", right)
                == s_matrix_entry("0", "0") * QUANTUM_DIMENSIONS[right]
            )


def test_s_matrix_square_is_identity_for_self_dual_labels() -> None:
    for row, left in enumerate(SIMPLE_LABELS):
        for column, right in enumerate(SIMPLE_LABELS):
            total = sum(
                S_MATRIX[row][middle] * S_MATRIX[middle][column]
                for middle in range(len(SIMPLE_LABELS))
            )
            assert total == (QuadraticSurd(1) if left == right else QuadraticSurd(0))


def test_hopf_control_uses_s_over_s00_without_evaluating_links() -> None:
    assert hopf_control_entry("0", "0") == QuadraticSurd(1)
    assert hopf_control_entry("0", "1") == SQRT2
    assert hopf_control_entry("1", "1") == QuadraticSurd(0)
    assert hopf_control_entry("1", "2") == -SQRT2
    assert hopf_control_entry("2", "2") == QuadraticSurd(1)


def test_twists_are_exact_symbolic_local_convention_values() -> None:
    assert TWIST_VALUES == {
        "0": RootOfUnityPower(16, 0),
        "1": RootOfUnityPower(16, 3),
        "2": RootOfUnityPower(16, 8),
    }
    assert TWIST_VALUES["1"].to_jsonable() == {
        "kind": "root_of_unity_power",
        "symbol": "zeta_16",
        "order": 16,
        "exponent": 3,
    }


def test_link_data_claim_levels_keep_source_needed_boundary() -> None:
    assert (
        LINK_DATA_CLAIM_LEVELS["fusion_dimension_algebra"]["claim_level"]
        == "computed evidence/schema-test-safe"
    )
    assert LINK_DATA_CLAIM_LEVELS["s_matrix"]["claim_level"].startswith("SOURCE NEEDED")
    assert LINK_DATA_CLAIM_LEVELS["hopf_control"]["claim_level"].startswith(
        "SOURCE NEEDED"
    )
    assert LINK_DATA_CLAIM_LEVELS["twists"]["claim_level"].startswith("SOURCE NEEDED")
    assert LINK_DATA_CLAIM_LEVELS["twists"]["positive_framing_sign"] == "SOURCE NEEDED"


def test_omega_theta_convention_cites_ledger_and_stays_source_needed() -> None:
    assert OMEGA_THETA_CONVENTION["status"] == "source-needed/working"
    assert (
        OMEGA_THETA_CONVENTION["ledger"]
        == legacy_prose_member_ref("wiki/understandings/formula-conventions.org")
    )
    assert "SOURCE NEEDED" in OMEGA_THETA_CONVENTION["reason_numeric_coefficients_absent"]


def test_unsupported_data_is_explicitly_absent() -> None:
    assert "f_symbols" in UNSUPPORTED_DATA
    assert "r_symbols" in UNSUPPORTED_DATA
    assert "invariant_formula" in UNSUPPORTED_DATA
    assert all("absent" in reason for reason in UNSUPPORTED_DATA.values())


def test_certificate_payload_is_stable_json_data() -> None:
    payload = certificate_payload()
    encoded = json.dumps(payload, sort_keys=True)

    assert payload["schema"] == "twisted-yetter.su2-level2-category-data.v1"
    assert payload["status"] == "pass"
    assert payload["node_id"] == "n15-su2-level2-link-data"
    assert payload["simple_labels"] == ["0", "1", "2"]
    assert payload["quantum_dimensions"]["1"] == {
        "kind": "Q(sqrt2)",
        "rational": {"type": "integer", "value": "0"},
        "sqrt2": {"type": "integer", "value": "1"},
    }
    assert payload["twists"]["1"] == {
        "kind": "root_of_unity_power",
        "symbol": "zeta_16",
        "order": 16,
        "exponent": 3,
    }
    assert payload["hopf_control"]["1,2"] == {
        "kind": "Q(sqrt2)",
        "rational": {"type": "integer", "value": "0"},
        "sqrt2": {"type": "integer", "value": "-1"},
    }
    assert '"positive_framing_sign": "SOURCE NEEDED"' in encoded
