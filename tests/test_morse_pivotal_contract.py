import hashlib
import json
from pathlib import Path
import subprocess

import pytest

from experiments.sage.morse_fusion_evaluator import MorseEvaluator
from experiments.sage.morse_pivotal_contract import (
    PivotalCapabilityError,
    require_pivotal_capabilities,
    test_pivotal_profile as make_test_pivotal_profile,
    validate_pivotal_profile,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
PIVOTAL_ROOT = REPO_ROOT / "experiments" / "inputs" / "category-pivotal"


class FROnlyHistoricalCategory:
    labels = (0,)
    unit = 0
    category_id = "omega0_untwisted_D_A4"

    def cost_profile(self):
        return {"f": 1.0, "r": 1.0}


def test_historical_da4_fr_only_fixture_always_rejects_pivotal_use():
    fixture = json.loads(
        (PIVOTAL_ROOT / "historical-da4-fr-only-no-pivotal-v1.json").read_text()
    )
    assert fixture["historical_source"]["git_commit"] == (
        "1af78a26e814b5937458dff7d4972dce50a5e190"
    )
    assert fixture["historical_source"]["git_blob"] == (
        "125ad28098f47ef515c01fe6dee2ba1e4e1e5737"
    )
    assert fixture["pivotal_profile"] is None
    historical_bytes = subprocess.check_output(
        [
            "git",
            "show",
            f"{fixture['historical_source']['git_commit']}:"
            f"{fixture['historical_source']['path']}",
        ],
        cwd=REPO_ROOT,
    )
    assert hashlib.sha256(historical_bytes).hexdigest() == fixture[
        "historical_source"
    ]["sha256"]
    category = FROnlyHistoricalCategory()
    category.pivotal_profile = fixture["pivotal_profile"]
    with pytest.raises(PivotalCapabilityError, match="no explicit pivotal profile"):
        require_pivotal_capabilities(category, {"rigid_bends"})


def test_morse_evaluator_rejects_bent_fr_only_category_before_evaluation():
    category = FROnlyHistoricalCategory()
    forms = (
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]},
    )
    with pytest.raises(PivotalCapabilityError, match="no explicit pivotal profile"):
        MorseEvaluator(category).fixed_label_value(forms, {"A": 0})


@pytest.mark.parametrize(
    "filename,category_id",
    [
        ("su2-k-standard-pivotal-v1.json", "su2-k2"),
        ("su2-k-standard-pivotal-v1.json", "su2-k8"),
        ("su3-2-anyonwiki-pivotal-v1.json", "su3-k2-anyonwiki-fr"),
        (
            "drinfeld-double-dic12-pivotal-v1.json",
            "omega0_untwisted_D_Dic12",
        ),
    ],
)
def test_recorded_positive_profiles_validate(filename, category_id):
    profile = json.loads((PIVOTAL_ROOT / filename).read_text())
    assert validate_pivotal_profile(
        profile, expected_category_id=category_id
    ) is profile


def test_contract_rejects_boolean_only_capability_claim():
    profile = make_test_pivotal_profile(category_id="test")
    del profile["evaluation_coevaluation"]
    with pytest.raises(PivotalCapabilityError, match="missing required fields"):
        validate_pivotal_profile(profile, expected_category_id="test")


def test_positive_profile_evidence_hashes_match_repo_files():
    for filename in (
        "su2-k-standard-pivotal-v1.json",
        "su3-2-anyonwiki-pivotal-v1.json",
        "drinfeld-double-dic12-pivotal-v1.json",
    ):
        profile = json.loads((PIVOTAL_ROOT / filename).read_text())
        for evidence in profile["evidence"]:
            if "sha256" not in evidence:
                continue
            source = REPO_ROOT / evidence["path"]
            assert hashlib.sha256(source.read_bytes()).hexdigest() == evidence["sha256"]
