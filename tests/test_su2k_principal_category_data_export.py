import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = (
    ROOT
    / "experiments"
    / "results"
    / "foundation-v2-safety-substrate"
    / "grown-category-data"
)


def load_export(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def test_ising_principal_export_contains_full_level2_fr_data_but_not_row_completion() -> None:
    payload = load_export("rank3-ising-principal-su2-level2-category-data-export-v1.json")

    assert_content_hash(payload)
    assert payload["family_id"] == "rank3-ising"
    assert payload["status"] == "PRINCIPAL_SU2_BRANCH_DATA_EXPORTED_NOT_ROW_COMPLETE"
    assert payload["formal_row_resolution_allowed"] is False
    assert payload["formal_ribbon_realization_snapshot_produced"] is False
    assert payload["entry_counts"] == {
        "dimensions": 3,
        "f_symbols": 36,
        "fusion_products": 9,
        "r_symbols": 20,
        "twists": 3,
    }
    data = payload["category_data"]
    assert data["labels"] == [0, 1, 2]
    assert data["fusion"]["1x1"] == [0, 2]
    assert "F(1,1,1->1;0,0)" in data["f_symbols"]
    assert "R+(1,1->0)" in data["r_symbols"]
    assert "principal SU(2)_k branch" in payload["why_not_row_complete"][0]


def test_su2_4_principal_export_contains_full_level4_fr_data_but_not_extensions() -> None:
    payload = load_export("rank5-su2-4-principal-su2-level4-category-data-export-v1.json")

    assert_content_hash(payload)
    assert payload["family_id"] == "rank5-su2-4"
    assert payload["status"] == "PRINCIPAL_SU2_BRANCH_DATA_EXPORTED_NOT_EXTENSION_COMPLETE"
    assert payload["formal_row_resolution_allowed"] is False
    assert payload["formal_ribbon_realization_snapshot_produced"] is False
    assert payload["entry_counts"] == {
        "dimensions": 5,
        "f_symbols": 329,
        "fusion_products": 25,
        "r_symbols": 70,
        "twists": 5,
    }
    data = payload["category_data"]
    assert data["labels"] == [0, 1, 2, 3, 4]
    assert data["fusion"]["1x1"] == [0, 2]
    assert data["fusion"]["2x2"] == [0, 2, 4]
    assert "F(2,2,2->2;0,0)" in data["f_symbols"]
    assert "R+(2,2->4)" in data["r_symbols"]
    assert any("Galois/mirror/pivotal/ribbon" in item for item in payload["why_not_row_complete"])
