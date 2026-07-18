from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v9.json"
)
TOPOLOGY_AXIOM = (
    "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
    "standardSpecialKirbyCalculusConnected"
)
HOMOLOGY_AXIOM = (
    "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
    "standardHandleChainNaturalityInput"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode()
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    ).stdout


def test_v9_is_content_addressed_and_not_promoted() -> None:
    artifact = load_artifact()
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == (
        "PASS_FOURTEEN_FOUNDATION_CONDITIONS_ESTABLISHED_"
        "FOUR_CONCRETE_INSTANCES_OPEN"
    )
    assert artifact["git"]["dirty_before_generation"] is False
    assert artifact["admission"]["ctl_theorem_claim_admitted"] is False


def test_exact_fourteen_four_partition() -> None:
    ledger = load_artifact()["target_condition_ledger"]
    assert ledger["counts"] == {"required": 18, "established": 14, "open": 4}
    assert ledger["required_conditions"] == (
        ledger["established_conditions"] + ledger["open_conditions"]
    )
    assert ledger["established_conditions"][-1] == (
        "categoryBoundKirbyColorCompilerMechanism"
    )
    assert ledger["open_conditions"] == [
        "homologicalKirbyColorWeightsInstance",
        "globalFiniteKirbyColorExpansionInstance",
        "sourceBoundGraphicalMoveCompilerInstance",
        "sourceBoundEvaluatorCompilerInstance",
    ]


def test_exact_two_domain_axioms_and_no_hidden_result() -> None:
    boundary = load_artifact()["domain_axiom_boundary"]
    assert boundary["count"] == 2
    assert boundary["axioms"] == sorted([TOPOLOGY_AXIOM, HOMOLOGY_AXIOM])
    assert boundary["homology_axiom_contains_chain_equivalences"] is True
    assert boundary["homology_axiom_contains_coordinate_naturality"] is True
    assert boundary["homology_axiom_contains_final_h2_identity"] is False
    assert boundary["homology_axiom_contains_evaluator_equality"] is False
    assert boundary["geometric_h2_semantics_external"] is True


def test_exact_mutation_and_axiom_denominators() -> None:
    checks = load_artifact()["checks"]
    assert checks["local_move_recipe"]["mutation_count"] == 8
    assert checks["categorical_compiler"]["mutation_count"] == 6
    assert (
        checks["category_bound_kirby_color_compiler"]["mutation_count"] == 3
    )
    assert checks["ribbon_graphical_algebra"]["mutation_count"] == 3
    assert (
        checks["source_bound_graphical_move_compiler"]["mutation_count"] == 4
    )
    assert checks["geometric_h2_mechanism"]["mutation_count"] == 2
    assert checks["handle_chain_domain"]["mutation_count"] == 2
    assert checks["target"]["mutation_count"] == 5
    assert checks["local_move_recipe"]["custom_domain_axiom_count"] == 0
    assert checks["categorical_compiler"]["custom_domain_axiom_count"] == 0
    assert (
        checks["category_bound_kirby_color_compiler"][
            "custom_domain_axiom_count"
        ]
        == 0
    )
    assert (
        checks["ribbon_graphical_algebra"]["custom_domain_axiom_count"] == 0
    )
    assert (
        checks["source_bound_graphical_move_compiler"][
            "custom_domain_axiom_count"
        ]
        == 0
    )
    assert (
        checks["geometric_h2_mechanism"]["custom_domain_axiom_count"] == 0
    )
    assert checks["handle_chain_domain"]["custom_domain_axioms"] == [
        HOMOLOGY_AXIOM
    ]
    assert checks["target"]["custom_domain_axioms"] == sorted(
        [TOPOLOGY_AXIOM, HOMOLOGY_AXIOM]
    )


def test_every_recorded_source_replays_from_pinned_commit() -> None:
    artifact = load_artifact()
    commit = artifact["git"]["commit"]
    for relative, record in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == record["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            record["sha256"]
        ), relative


def test_exact_four_open_instance_obligations() -> None:
    obligations = load_artifact()["remaining_instance_obligations"]
    assert [item["condition"] for item in obligations] == [
        "homologicalKirbyColorWeightsInstance",
        "globalFiniteKirbyColorExpansionInstance",
        "sourceBoundGraphicalMoveCompilerInstance",
        "sourceBoundEvaluatorCompilerInstance",
    ]
    assert all(item["status"] == "OPEN" for item in obligations)


def test_category_binding_guards_are_all_recorded() -> None:
    check = load_artifact()["checks"]["category_bound_kirby_color_compiler"]
    assert check["simple_label_type_bound"] is True
    assert check["zero_class_ordinary_weight_bound"] is True
    assert check["strand_simple_dual_interpretation_bound"] is True
    assert check["framing_twist_bound_to_graphical_algebra"] is True
    assert check["nonzero_homological_coefficients_constructed"] is False


def test_concrete_invariant_and_crane_yetter_are_explicit_nonclaims() -> None:
    nonclaims = load_artifact()["explicit_nonclaims"]
    assert any("concrete invariant value" in item for item in nonclaims)
    assert any("not identified with Crane-Yetter" in item for item in nonclaims)
