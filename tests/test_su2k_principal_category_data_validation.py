import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = (
    ROOT
    / "experiments"
    / "results"
    / "foundation-v2-safety-substrate"
    / "grown-category-certificates"
)
DATA = (
    ROOT
    / "experiments"
    / "results"
    / "foundation-v2-safety-substrate"
    / "grown-category-data"
)


EXPECTED = {
    "rank3-ising": {
        "certificate": "rank3-ising-principal-su2-level2-strict-export-validation-v1.json",
        "export": "rank3-ising-principal-su2-level2-category-data-export-v1.json",
        "export_status": "PRINCIPAL_SU2_BRANCH_DATA_EXPORTED_NOT_ROW_COMPLETE",
        "counts": {
            "dimension_entries": 3,
            "f_symbol_entries": 36,
            "fusion_entries": 9,
            "r_inverse_entries": 20,
            "r_symbol_entries": 20,
            "twist_entries": 3,
        },
    },
    "rank5-su2-4": {
        "certificate": "rank5-su2-4-principal-su2-level4-strict-export-validation-v1.json",
        "export": "rank5-su2-4-principal-su2-level4-category-data-export-v1.json",
        "export_status": "PRINCIPAL_SU2_BRANCH_DATA_EXPORTED_NOT_EXTENSION_COMPLETE",
        "counts": {
            "dimension_entries": 5,
            "f_symbol_entries": 329,
            "fusion_entries": 25,
            "r_inverse_entries": 70,
            "r_symbol_entries": 70,
            "twist_entries": 5,
        },
    },
}


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def test_strict_principal_validation_certificates_are_hash_bound() -> None:
    for family_id, spec in EXPECTED.items():
        cert = load_json(OUT / spec["certificate"])
        export = load_json(DATA / spec["export"])

        assert_content_hash(cert)
        assert cert["family_id"] == family_id
        assert cert["status"] == "PASS_STRICT_PRINCIPAL_EXPORT_REVALIDATION"
        assert cert["validated_export"]["content_hash"] == export["content_hash"]
        assert cert["validated_export"]["status"] == spec["export_status"]
        assert cert["checked_entry_counts"] == spec["counts"]


def test_strict_principal_validation_recomputes_every_recorded_surface() -> None:
    required_checks = {
        "category_data_hash_fresh",
        "dimension_entries_recomputed",
        "entry_counts_match",
        "export_content_hash_fresh",
        "f_symbol_entries_recomputed",
        "fusion_entries_recomputed",
        "r_inverse_entries_recomputed",
        "r_symbol_entries_recomputed",
        "source_machinery_hash_matches",
        "twist_entries_recomputed",
    }

    for spec in EXPECTED.values():
        cert = load_json(OUT / spec["certificate"])

        assert set(cert["checks"]) == required_checks
        assert set(cert["checks"].values()) == {"PASS"}
        assert cert["formal_row_resolution_allowed"] is False
        assert cert["formal_ribbon_realization_snapshot_produced"] is False
        assert any("not a row-complete" in item for item in cert["explicit_non_claims"])
