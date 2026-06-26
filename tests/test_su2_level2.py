import json

import pytest

from twisted_yetter.su2_level2 import (
    GLOBAL_DIMENSION,
    OMEGA_THETA_CONVENTION,
    QUANTUM_DIMENSIONS,
    SIMPLE_LABELS,
    SQRT2,
    UNSUPPORTED_DATA,
    QuadraticSurd,
    certificate_payload,
    fusion,
    global_dimension_from_simples,
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


def test_omega_theta_convention_cites_ledger_and_stays_source_needed() -> None:
    assert OMEGA_THETA_CONVENTION["status"] == "source-needed/working"
    assert (
        OMEGA_THETA_CONVENTION["ledger"]
        == "wiki/understandings/formula-conventions.org"
    )
    assert "SOURCE NEEDED" in OMEGA_THETA_CONVENTION["reason_numeric_coefficients_absent"]


def test_unsupported_data_is_explicitly_absent() -> None:
    assert "twists" in UNSUPPORTED_DATA
    assert "f_symbols" in UNSUPPORTED_DATA
    assert "r_symbols" in UNSUPPORTED_DATA
    assert "invariant_formula" in UNSUPPORTED_DATA
    assert all("absent" in reason for reason in UNSUPPORTED_DATA.values())


def test_certificate_payload_is_stable_json_data() -> None:
    payload = certificate_payload()
    encoded = json.dumps(payload, sort_keys=True)

    assert payload["schema"] == "twisted-yetter.su2-level2-category-data.v1"
    assert payload["status"] == "pass"
    assert payload["simple_labels"] == ["0", "1", "2"]
    assert payload["quantum_dimensions"]["1"] == {
        "kind": "Q(sqrt2)",
        "rational": {"type": "integer", "value": "0"},
        "sqrt2": {"type": "integer", "value": "1"},
    }
    assert '"twists": "absent:' in encoded
