from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-modular-final-theorem-refactor-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def test_artifact_is_content_addressed_and_explicit_about_axioms() -> None:
    artifact = load_artifact()
    assert artifact["status"] == (
        "SUPERSEDED_BY_CANONICAL_MODULAR_FOUR_MANIFOLD_INVARIANT_V1"
    )
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["target_theorem"]["status"] == (
        "KERNEL_CHECKED_BOUNDARY_CERTIFIED_KIRBY_QUOTIENT_"
        "DESCENT_RELATIVE_TO_EXPLICIT_GRAPHICAL_AND_"
        "HANDLE_CHAIN_NATURALITY_AXIOMS"
    )
    assert artifact["target_theorem"]["lean_name"] == (
        "TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator."
        "boundaryCertifiedEvaluationOnKirbyClass_mk"
    )
    assert artifact["target_theorem"][
        "caller_supplies_graphical_laws"
    ] is False
    assert artifact["graphical_target_predicate"][
        "rule_independent_public_eval_constructor_status"
    ] == "AVAILABLE_IN_SUPERSEDING_ARTIFACT"
    assert artifact["supersession"]["artifact"] == (
        "experiments/results/lean-kirby/"
        "canonical-modular-four-manifold-invariant-v1.json"
    )
    assert artifact["four_manifold_boundary"]["status"] == (
        "GENERIC_DERIVATION_KERNEL_CHECKED_CONCRETE_INSTANCES_OPEN"
    )


def test_final_proof_layers_and_axioms_are_visible() -> None:
    checks = load_artifact()["checks"]
    assert checks["presentation_marking"] == (
        "PASS_MARKING_IS_EACH_PRESENTATION_HANDLE_CHAIN_H2"
    )
    assert checks["elementary_transport"] == (
        "PASS_DERIVED_FROM_CHAIN_HOMOTOPY_EQUIVALENCE"
    )
    assert checks["local_move_soundness"] == (
        "PASS_FROM_CONCRETE_EIGHT_CASE_COMPILER_AND_FIXED_"
        "LITERATURE_BACKED_GRAPHICAL_ENVIRONMENT"
    )
    assert checks["generated_equivalence_soundness"] == (
        "PASS_REFL_SYMM_TRANS_INDUCTION"
    )
    assert checks["kirby_quotient_descent"] == "PASS_QUOTIENT_LIFT"
    assert checks["axiom_audit"]["audited_declaration_count"] == 12
    assert checks["axiom_audit"][
        "topology_axioms_used_by_quotient_descent"
    ] == []
    assert len(
        checks["axiom_audit"]["graphical_environment_axioms"]
    ) == 5
    assert len(
        checks["graphical_axiom_audit"]["graphical_literature_axioms"]
    ) == 4
    assert len(checks["textbook_axiom_audit"]["textbook_axioms"]) == 3
    assert checks["proof_relevant_kirby_movie"] == (
        "PASS_MOVIE_LIVES_IN_TYPE_AND_ONLY_EXISTENCE_IS_ERASED"
    )
    assert checks["derived_d3_and_h2"] == (
        "PASS_D3_DERIVED_FROM_TRANSPORTED_SPHERES_AND_"
        "INTERSECTION_NUMBERS"
    )
    assert checks["legacy_evaluator_bridge"] == (
        "PASS_EVALUATOR_CONSUMES_BOUNDARY_DERIVED_HANDLE_CHAIN_H2_"
        "AND_MOVE_TRANSPORT_IS_DERIVED_FROM_VISIBLE_AXIOM"
    )
    assert checks["derived_mathlib_handle_chain_model"] == (
        "PASS_CHAIN_COMPLEX_D2_D3_AND_H2_ARE_BOUNDARY_DERIVED"
    )
    assert checks["certified_legacy_adapter"] == (
        "PASS_NO_CALLER_SUPPLIED_HANDLE_CHAIN"
    )
    boundary_audit = checks["boundary_axiom_audit"]
    assert boundary_audit["status"] == (
        "PASS_ALL_BOUNDARY_LAYERS_AUDITED"
    )
    assert len(boundary_audit["files"]) == 5
    for report in boundary_audit["files"].values():
        assert report["project_axioms"] == []
    evaluator_audit = checks["boundary_evaluator_axiom_audit"]
    assert evaluator_audit["status"] == (
        "PASS_EXACT_GRAPHICAL_AXIOMS_PLUS_VISIBLE_"
        "HANDLE_CHAIN_NATURALITY_AXIOM"
    )
    assert evaluator_audit["audited_declaration_count"] == 6
    expected_axioms = [
        *checks["axiom_audit"]["graphical_environment_axioms"],
        *load_artifact()["used_topology_axioms"],
    ]
    assert sorted(evaluator_audit["project_axioms"]) == sorted(expected_axioms)


def test_historical_source_snapshot_metadata_is_well_formed() -> None:
    artifact = load_artifact()
    for relative, metadata in artifact["inputs"]["source_files"].items():
        assert relative
        assert metadata["bytes"] > 0
        assert len(metadata["sha256"]) == 64
    for key in ("reference_records", "design_records"):
        for relative, metadata in artifact["inputs"][key].items():
            assert relative
            assert metadata["bytes"] > 0
            assert len(metadata["sha256"]) == 64


def test_nonclaims_preserve_the_real_remaining_boundary() -> None:
    artifact = load_artifact()
    nonclaims = "\n".join(artifact["explicit_non_claims"])
    assert "No axiom-free derivation" in nonclaims
    assert "did not provide the canonical Eval_C constructor" in nonclaims
    assert "boundary standardization certificate generator" in nonclaims
    assert "standard handle-chain naturality statement" in nonclaims
    assert "accepts no independent legacy handle chain" in nonclaims
    assert "explicit marked-coordinate equivalence" in nonclaims
    assert "one fixed manifold input" in nonclaims
    assert "No concrete modular category instance" in nonclaims
    assert "No premodular-category" in nonclaims
    boundary = artifact["graphical_rule_boundary"]
    assert boundary["status"] == (
        "DISCHARGED_RELATIVE_TO_EXPLICIT_LITERATURE_AXIOMS"
    )
    assert boundary["rule_count"] == 3
    assert len(boundary["rules"]) == 3
    assert boundary["caller_supplies_graphical_laws"] is False
    remaining = artifact["remaining_concrete_instantiation_boundary"]
    assert remaining["status"] == (
        "CONCRETE_TOPOLOGY_GLOBAL_FAMILY_AND_COMPILER_"
        "INSTANCES_REMAIN_OPEN"
    )
    assert remaining["not_a_global_graphical_law"] is True
    assert remaining["terminal_blocker"] is None
    assert "evaluator bridge is closed" in remaining["meaning"]


def test_anti_hack_guards_are_machine_readable() -> None:
    guards = load_artifact()["anti_hack_guards"]
    assert guards["status"] == "PASS_FORBIDDEN_SHORTCUTS_ABSENT"
    assert guards["forbidden_legacy_interfaces"] == [
        "ClosedFourManifoldKirbyCorrespondence",
        "kirbyCerfAndThreeHandleCompletion",
        "inductive KirbyEquivalent",
    ]
    assert "BoundaryCertifiedPresentation has no handleChain field" in (
        guards["required_design_properties"]
    )
    assert "the legacy adapter handleChain is definitionally derived" in (
        guards["required_design_properties"]
    )
    assert (
        "the evaluator marking is the boundary-derived handle-chain H2"
        in guards["required_design_properties"]
    )
    assert "BoundaryCertifiedMove has no homology transport field" in (
        guards["required_design_properties"]
    )
