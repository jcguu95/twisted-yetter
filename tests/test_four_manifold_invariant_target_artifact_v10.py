from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v10.json"
)


def canonical_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode()


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def test_content_hash_and_status() -> None:
    artifact = load_artifact()
    payload = dict(artifact)
    observed = payload.pop("content_hash")
    assert observed == sha256_bytes(canonical_bytes(payload))
    assert (
        artifact["schema"]
        == "twisted-yetter.four-manifold-invariant-target.v10"
    )
    assert artifact["status"] == (
        "PASS_FIFTEEN_FOUNDATION_CONDITIONS_ESTABLISHED_"
        "FIVE_CONCRETE_INSTANCES_OPEN"
    )
    assert artifact["mathematical_status"].endswith(
        "CONCRETE_FOUR_MANIFOLD_INVARIANT_NOT_YET_ESTABLISHED"
    )


def test_target_condition_partition() -> None:
    ledger = load_artifact()["target_condition_ledger"]
    assert ledger["counts"] == {
        "required": 20,
        "established": 15,
        "open": 5,
    }
    assert (
        ledger["established_conditions"] + ledger["open_conditions"]
        == ledger["required_conditions"]
    )
    assert "integralCharacterKirbyColorCompilerMechanism" in (
        ledger["established_conditions"]
    )
    assert ledger["open_conditions"] == [
        "integralCycleRepresentativeSystemInstance",
        "tensorAutomorphismGeneratorInstance",
        "globalFiniteKirbyColorExpansionInstance",
        "sourceBoundGraphicalMoveCompilerInstance",
        "sourceBoundEvaluatorCompilerInstance",
    ]


def test_integral_character_scope_and_guards() -> None:
    artifact = load_artifact()
    scope = artifact["integral_character_scope"]
    assert "degree-two cycles" in scope["representative"]
    assert "homology-class equality" in scope["representative"]
    assert scope["specially_dotted_status"].startswith("excluded")

    checks = artifact["checks"]["integral_character_compiler"]
    assert checks["status"] == "PASS_KERNEL_CHECKED_MECHANISM"
    assert checks["mutation_count"] == 3
    assert checks["custom_domain_axiom_count"] == 0
    assert checks["arbitrary_weight_compiler_rejected"] is True
    assert checks["missing_cycle_class_soundness_rejected"] is True
    assert checks["missing_tensor_law_rejected"] is True


def test_target_remains_conditional_and_nonclaims_are_explicit() -> None:
    artifact = load_artifact()
    target = artifact["target_theorem"]
    assert target["conditional_on_concrete_inputs"] is True
    assert target["concrete_inputs_constructed"] is False
    assert len(artifact["open_instance_details"]) == 5
    nonclaims = "\n".join(artifact["non_claims"])
    assert "No concrete four-manifold invariant" in nonclaims
    assert "No arbitrary H2(X; A)" in nonclaims
    assert "No specially-dotted presentation" in nonclaims


def test_source_file_hashes_are_fresh() -> None:
    artifact = load_artifact()
    for relative, record in artifact["inputs"]["source_files"].items():
        data = (ROOT / relative).read_bytes()
        assert record == {
            "bytes": len(data),
            "sha256": sha256_bytes(data),
        }
