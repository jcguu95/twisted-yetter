import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = (
    ROOT
    / "experiments"
    / "results"
    / "foundation-v2-safety-substrate"
    / "grown-category-branches"
)


EXPECTED = {
    "rank3-ising": {
        "export": "rank3-ising-su2-level2-galois-branch-candidates-v1.json",
        "certificate": "rank3-ising-su2-level2-galois-branch-candidates-validation-v1.json",
        "powers": [1, 3, 5, 7, 9, 11, 13, 15],
        "per_branch_counts": {
            "dimensions": 3,
            "f_symbols": 36,
            "fusion_products": 9,
            "r_symbols": 20,
            "twists": 3,
        },
        "checked_counts": {
            "branch_count": 8,
            "dimension_entries": 24,
            "f_symbol_entries": 288,
            "fusion_entries": 72,
            "r_inverse_entries": 160,
            "r_symbol_entries": 160,
            "twist_entries": 24,
        },
    },
    "rank5-su2-4": {
        "export": "rank5-su2-4-su2-level4-galois-branch-candidates-v1.json",
        "certificate": "rank5-su2-4-su2-level4-galois-branch-candidates-validation-v1.json",
        "powers": [1, 5, 7, 11, 13, 17, 19, 23],
        "per_branch_counts": {
            "dimensions": 5,
            "f_symbols": 329,
            "fusion_products": 25,
            "r_symbols": 70,
            "twists": 5,
        },
        "checked_counts": {
            "branch_count": 8,
            "dimension_entries": 40,
            "f_symbol_entries": 2632,
            "fusion_entries": 200,
            "r_inverse_entries": 560,
            "r_symbol_entries": 560,
            "twist_entries": 40,
        },
    },
}


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def test_galois_branch_candidate_exports_are_hash_bound_but_not_formal_snapshots() -> None:
    for family_id, spec in EXPECTED.items():
        export = load_json(OUT / spec["export"])

        assert_content_hash(export)
        assert export["family_id"] == family_id
        assert export["status"] == "SU2K_GALOIS_BRANCH_CANDIDATES_EXPORTED_NOT_ROW_COMPLETE"
        assert export["candidate_branch_count"] == 8
        assert export["galois_powers"] == spec["powers"]
        assert export["per_branch_entry_counts"] == spec["per_branch_counts"]
        assert export["formal_row_resolution_allowed"] is False
        assert export["formal_ribbon_realization_snapshot_produced"] is False
        assert any("not formal ribbon_realization_snapshot" in item for item in export["explicit_non_claims"])

        branch_ids = [branch["branch_id"] for branch in export["branches"]]
        assert len(branch_ids) == len(set(branch_ids)) == 8
        for branch, power in zip(export["branches"], spec["powers"], strict=True):
            assert branch["galois_power"] == power
            assert branch["field_embedding"]["cyclotomic_root"].endswith(f"^{power}")
            assert "sqrt_branch_convention" in branch["field_embedding"]
            assert branch["pairing"]["fusion_pairing_invertibility_checked"] is False


def test_galois_branch_candidate_certificates_recompute_all_entries() -> None:
    required_checks = {
        "branch_hashes_fresh",
        "candidate_branch_count_matches",
        "dimension_entries_recomputed",
        "export_content_hash_fresh",
        "f_symbol_entries_recomputed",
        "fusion_entries_recomputed",
        "r_inverse_entries_recomputed",
        "r_symbol_entries_recomputed",
        "source_machinery_hash_matches",
        "twist_entries_recomputed",
    }

    for spec in EXPECTED.values():
        export = load_json(OUT / spec["export"])
        cert = load_json(OUT / spec["certificate"])

        assert_content_hash(cert)
        assert cert["status"] == "PASS_STRICT_GALOIS_BRANCH_CANDIDATE_REVALIDATION"
        assert cert["validated_export"]["content_hash"] == export["content_hash"]
        assert cert["checked_entry_counts"] == spec["checked_counts"]
        assert set(cert["checks"]) == required_checks
        assert set(cert["checks"].values()) == {"PASS"}
        assert cert["formal_row_resolution_allowed"] is False
        assert cert["formal_ribbon_realization_snapshot_produced"] is False
        assert any("not a row-complete" in item for item in cert["explicit_non_claims"])
