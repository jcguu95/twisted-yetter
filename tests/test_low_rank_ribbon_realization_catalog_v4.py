import copy
import importlib.util
import json
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import (
    RIBBON_CATALOG_ESTABLISHED,
    RIBBON_CATALOG_PARTIAL,
    FoundationSafetyError,
    stable_content_hash,
    validate_formal_evidence,
    validate_low_rank_ribbon_catalog,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_ribbon_realization_catalog_v4.py"
SPEC = importlib.util.spec_from_file_location("low_rank_ribbon_catalog_v4", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_rank2_sage_certificate_is_content_bound_and_has_negative_controls() -> None:
    certificate = load_json("rank2-fibonacci-yang-lee-sage-coherence-v1.json")
    body = dict(certificate)
    content_hash = body.pop("content_hash")

    assert certificate["status"] == "PASS"
    assert certificate["branch_count"] == 4
    assert content_hash == stable_content_hash(body)

    for branch in certificate["branches"]:
        assert branch["status"] == "PASS"
        assert all(branch["exact_checks"].values())
        negative = branch["negative_controls"]["wrong_rx_square_root"]
        assert "FAIL" in {
            negative["right_hexagon_status"],
            negative["left_hexagon_status"],
        }


def test_checked_in_v4_catalog_resolves_rank2_fib_yang_lee_without_unblocking_scan() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v4.json")
    readiness = load_json("formal-low-rank-scan-readiness-v4.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 3
    assert catalog["blocked_row_count"] == 11
    assert catalog["resolved_family_ids"] == [
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank5-su5-1",
    ]
    assert catalog["formal_scan_plan_allowed"] is False
    assert readiness["status"] == "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY"
    assert readiness["scan_plan_generation_allowed"] is False


def test_resolved_v4_rows_do_not_keep_stale_unverified_level_metadata() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v4.json")

    for row in catalog["families"]:
        if row["terminal_status"] != "RESOLVED_RIBBON_REALIZATION":
            continue
        assert row["spherical_level"]["status"] == "HASH_BOUND_SPHERICAL_DATA_MATERIALIZED"
        assert row["pivotal_level"]["status"] == "HASH_BOUND_PIVOTAL_DATA_MATERIALIZED"
        assert row["ribbon_level"]["status"] == "VERIFIED_BY_FORMAL_SNAPSHOT_CERTIFICATES"
        assert "NOT_" not in row["spherical_level"]["status"]
        assert "NOT_" not in row["pivotal_level"]["status"]
        assert "NOT_" not in row["ribbon_level"]["status"]


def test_rank2_fib_yang_lee_row_has_four_formal_snapshot_hashes() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v4.json")
    row = {item["family_id"]: item for item in catalog["families"]}[
        "rank2-fibonacci-yang-lee"
    ]

    assert row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    assert row["formal_admission_allowed"] is True
    assert row["resolved_modular_braided_class_count"] == 4
    assert len(row["ribbon_realization_snapshot_hashes"]) == 4
    assert row["blocker_ids"] == []
    assert row["missing_evidence"] == []


def test_rank2_fib_yang_lee_snapshots_pass_formal_evidence_validation() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v4.json")
    certificate = load_json("rank2-fibonacci-yang-lee-sage-coherence-v1.json")
    row = {item["family_id"]: item for item in catalog["families"]}[
        "rank2-fibonacci-yang-lee"
    ]
    expected_hashes = set(row["ribbon_realization_snapshot_hashes"])
    actual_hashes = set()

    for path in catalog["resolved_snapshot_paths"]:
        if "rank2-fibonacci-yang-lee" not in path:
            continue
        snapshot = json.loads((ROOT / path).read_text(encoding="utf-8"))
        validate_formal_evidence(snapshot)
        actual_hashes.add(snapshot["content_hash"])
        assert snapshot["family_id"] == "rank2-fibonacci-yang-lee"
        assert snapshot["category_data"]["fusion"]["x*x"] == {"1": 1, "x": 1}
        assert snapshot["category_data"]["basis_gauge"].endswith("[1,x]")
        assert snapshot["structural_checks"]["pentagon"] == "PASS"
        assert snapshot["structural_checks"]["hexagon"] == "PASS"
        assert snapshot["structural_checks"]["balancing"] == "PASS"
        assert (
            snapshot["pinned_payload_hashes"]["rank2_sage_coherence_certificate"]
            == certificate["content_hash"]
        )

    assert actual_hashes == expected_hashes


def test_v4_catalog_cannot_be_labeled_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v4.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_v4_generator_rejects_missing_negative_control() -> None:
    certificate = load_json("rank2-fibonacci-yang-lee-sage-coherence-v1.json")
    bad = copy.deepcopy(certificate)
    bad["branches"][0]["negative_controls"]["wrong_rx_square_root"] = {
        "right_hexagon_status": "PASS",
        "left_hexagon_status": "PASS",
    }

    with pytest.raises(FoundationSafetyError, match="negative control"):
        MODULE.require_sage_certificate(bad)


def test_generator_builds_valid_v4_partial_catalog() -> None:
    artifacts = MODULE.build_all()
    catalog = artifacts["low-rank-ribbon-realization-catalog-v4.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_family_ids"] == [
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank5-su5-1",
    ]
    for name, payload in artifacts.items():
        if "snapshot" in name:
            validate_formal_evidence(payload)
