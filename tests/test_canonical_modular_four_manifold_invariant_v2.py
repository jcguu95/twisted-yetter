from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "canonical-modular-four-manifold-invariant-v2.json"
)
CURRENT_CORRECTION = (
    ROOT
    / "experiments/results/lean-kirby/"
    "dual-handle-convention-correction-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def test_v2_is_content_addressed_historical_snapshot() -> None:
    artifact = load_artifact()
    assert artifact["schema"] == (
        "canonical-modular-four-manifold-invariant-v2"
    )
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["mathematical_status"] == (
        "ESTABLISHED_RELATIVE_TO_NAMED_INPUTS"
    )
    assert artifact["final_theorem"]["is_axiom_free"] is False
    assert artifact["final_theorem"][
        "is_kernel_checked_relative_to_inputs"
    ] is True
    correction = json.loads(CURRENT_CORRECTION.read_text())
    safety = correction["resource_safety"]
    assert (
        "experiments/results/lean-kirby/"
        "canonical-modular-four-manifold-invariant-v2.json"
    ) in safety["unsafe_prior_artifacts"]
    assert correction["remaining_global_obligation"]["status"] == (
        "BLOCKED_GLOBAL_DUAL_BOUNDARY_MOVIE_INTEGRATION"
    )


def test_external_statement_denominator_is_exact_and_partitioned() -> None:
    denominator = load_artifact()["external_statement_denominator"]
    assert denominator["total_count"] == 16
    assert denominator["smooth_topology_arguments"]["count"] == 4
    assert denominator["handle_chain_axioms"]["count"] == 1
    assert denominator["diagrammatic_realization_axioms"]["count"] == 2
    assert denominator["category_literature_axioms"]["count"] == 9
    assert (
        4 + 1 + 2 + 9 == denominator["total_count"]
    )


def test_second_block_does_not_hide_the_planar_realization_gap() -> None:
    second = load_artifact()["second_block"]
    assert second["caller_supplies_local_realization"] is False
    assert second["caller_supplies_final_equality"] is False
    assert second["raw_planar_endpoint_compiler"]["status"] == (
        "TARGET_PINNED_NOT_IMPLEMENTED"
    )
    compiler = second["raw_planar_endpoint_compiler"]
    assert compiler["instruction_contains_whole_target"] is False
    assert compiler["instruction_contains_target_hash"] is False
    assert compiler["required_obligations"] == [
        "generated components equal the local splice",
        "generated events equal the local splice",
        "the generated formal presentation is the exact topology target",
        "the generated move compiles to LocalCycleCalculation",
    ]
    assert second["local_move_classes"] == [
        "framedIsotopy",
        "oneOverOne",
        "twoOverOne",
        "twoOverTwo",
        "oneTwoBirth",
        "oneTwoDeath",
        "twoThreeBirth",
        "twoThreeDeath",
    ]


def test_public_alpha_is_actual_handle_chain_second_homology() -> None:
    artifact = load_artifact()
    assert artifact["first_block"]["public_alpha_type"] == (
        "presentation.topology.handleChain.SecondHomology"
    )
    guards = artifact["checks"]["source_guards"]
    assert guards[
        "public_eval_alpha_is_actual_second_homology"
    ] is True
    assert guards[
        "final_ambient_h2_coordinate_bridge_absent"
    ] is True
    assert "actual handle-chain SecondHomology" in (
        artifact["final_theorem"]["alpha_interface"]
    )


def test_axiom_audit_and_fail_closed_guards_pass() -> None:
    artifact = load_artifact()
    checks = artifact["checks"]
    assert checks["umbrella_build"]["returncode"] == 0
    assert checks["final_axiom_audit_build"]["returncode"] == 0
    assert checks["layer_axiom_audit_build"]["returncode"] == 0
    audit = checks["final_axiom_audit"]
    assert len(audit["project_axioms"]) == 12
    assert audit["foundational_axioms"] == [
        "Classical.choice",
        "Quot.sound",
        "propext",
    ]
    guards = checks["source_guards"]
    assert guards["status"] == "PASS_FAIL_CLOSED_SOURCE_GUARDS"
    assert guards["proof_holes"] == []
    assert guards["local_move_class_count"] == 8
    assert guards["diagrammatic_axiom_count"] == 2
    assert guards["raw_planar_compiler_present"] is False
    assert guards["raw_planar_compiler_target_pinned"] is True
    assert guards["raw_planar_compiler_target_status"] == (
        "TARGET_PINNED_NOT_IMPLEMENTED"
    )
    assert guards["raw_instruction_accepts_whole_target"] is False
    assert guards["raw_instruction_accepts_target_hash"] is False
    assert guards[
        "retired_chosen_representative_slide_route_absent"
    ] is True


def test_historical_source_snapshot_metadata_is_well_formed() -> None:
    artifact = load_artifact()
    for group in ("source_files", "reference_records"):
        for relative, metadata in artifact["inputs"][group].items():
            assert relative
            assert metadata["bytes"] > 0
            assert len(metadata["sha256"]) == 64


def test_nonclaims_forbid_axiom_free_or_premodular_promotion() -> None:
    nonclaims = "\n".join(load_artifact()["explicit_non_claims"])
    assert "not an axiom-free" in nonclaims
    assert "diagrammatic realization statements are still axioms" in nonclaims
    assert "not arbitrary premodular categories" in nonclaims
    assert "not identified here with Yetter's original" in nonclaims
