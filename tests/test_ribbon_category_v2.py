import copy

import numpy as np
import pytest

from experiments.sage.morse_pivotal_contract import (
    test_pivotal_profile as make_test_pivotal_profile,
)
from experiments.sage.ribbon_category_v2 import (
    LegacyRibbonCategoryV2Adapter,
    RIBBON_CATEGORY_CONTRACT_VERSION,
    RibbonCategoryContractError,
    category_contract_snapshot,
    validate_ribbon_category_v2,
)


class LegacyVec:
    labels = (0,)
    unit = 0
    category_id = "test-vec"
    pivotal_profile = make_test_pivotal_profile(category_id=category_id)

    def dual(self, label):
        return label

    def dimension(self, label):
        return 1.0

    def twist(self, label):
        return 1.0

    def fusion_multiplicity(self, left, right, output):
        return int(left == right == output == 0)

    def f_block(self, a, b, c, d):
        assert (a, b, c, d) == (0, 0, 0, 0)
        basis = ((0, 0, 0),)
        return {
            "left_basis": basis,
            "right_basis": basis,
            "left_index": {basis[0]: 0},
            "right_index": {basis[0]: 0},
            "right_to_left": np.eye(1, dtype=np.complex128),
            "left_to_right": np.eye(1, dtype=np.complex128),
        }

    def r_matrix(self, a, b, c, positive):
        return np.eye(1, dtype=np.complex128)


def full_vec():
    category = LegacyRibbonCategoryV2Adapter(LegacyVec())
    category._coherence_certificate = {
        "status": "PASS_FULL_NUMERIC_RIBBON_COHERENCE",
        "category_data_hash": category.category_data_hash,
        "maximum_residual": 0.0,
    }
    return category


def test_v2_contract_accepts_complete_vec_data():
    category = full_vec()
    report = validate_ribbon_category_v2(category)
    assert category.contract_version == RIBBON_CATEGORY_CONTRACT_VERSION
    assert report.coherence_status == "PASS_FULL_NUMERIC_RIBBON_COHERENCE"
    assert report.maximum_pairing_residual == 0.0
    assert category_contract_snapshot(category)["category_data_hash"] == (
        category.category_data_hash
    )


def test_legacy_bridge_is_structural_only_without_coherence_certificate():
    category = LegacyRibbonCategoryV2Adapter(LegacyVec())
    with pytest.raises(RibbonCategoryContractError, match="full numeric coherence"):
        validate_ribbon_category_v2(category)
    report = validate_ribbon_category_v2(category, require_full_coherence=False)
    assert report.coherence_status == "LEGACY_PROFILE_STRUCTURAL_ONLY"


def test_v2_contract_rejects_noninvertible_fusion_pairing():
    category = full_vec()
    category.fusion_pairing = lambda a, b, c: np.zeros((1, 1), dtype=np.complex128)
    category.fusion_pairing_inverse = (
        lambda a, b, c: np.zeros((1, 1), dtype=np.complex128)
    )
    with pytest.raises(RibbonCategoryContractError, match="residual exceeds"):
        validate_ribbon_category_v2(category)


def test_v2_contract_rejects_certificate_for_different_data_hash():
    category = full_vec()
    category._coherence_certificate = {
        "status": "PASS_FULL_NUMERIC_RIBBON_COHERENCE",
        "category_data_hash": "sha256:" + "0" * 64,
        "maximum_residual": 0.0,
    }
    with pytest.raises(RibbonCategoryContractError, match="not bound"):
        validate_ribbon_category_v2(category)


def test_legacy_bridge_rejects_unrecorded_nonorthogonal_pairing():
    legacy = LegacyVec()
    legacy.pivotal_profile = copy.deepcopy(legacy.pivotal_profile)
    legacy.pivotal_profile["fusion_space_pairing"]["orthonormal"] = False
    with pytest.raises(ValueError, match="orthonormal"):
        LegacyRibbonCategoryV2Adapter(legacy)


def test_historical_fr_only_category_cannot_enter_v2_contract():
    class HistoricalFR:
        labels = (0,)
        unit = 0
        category_id = "historical-fr-only"
        pivotal_profile = None

    with pytest.raises(ValueError, match="no explicit pivotal profile"):
        LegacyRibbonCategoryV2Adapter(HistoricalFR())
