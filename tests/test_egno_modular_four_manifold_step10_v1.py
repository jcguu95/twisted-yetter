from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-modular-four-manifold-step10-v1.json"
)
ROADMAP = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-canonical-pivotal-roadmap-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def test_step10_artifact_is_content_addressed_and_clean() -> None:
    artifact = load_artifact()
    assert artifact["status"] == (
        "PASS_STEP_10_MARKED_FOUR_MANIFOLD_INVARIANT_RELATIVE_TO_"
        "EXPLICIT_SOURCE_BOUND_COMPILERS_AND_STANDARD_TOPOLOGY_INPUTS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_historical_roadmap_is_terminal_but_conditional() -> None:
    artifact = load_artifact()
    historical = json.loads(
        git_bytes(
            artifact["git"]["commit"],
            str(ROADMAP.relative_to(ROOT)),
        )
    )
    assert historical["status"] == (
        "TEN_STEP_CATEGORY_TO_MARKED_FOUR_MANIFOLD_INVARIANT_ROUTE_"
        "ESTABLISHED_RELATIVE_TO_EXPLICIT_DOMAIN_INPUTS"
    )
    assert historical["steps"][9]["status"] == (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_EXPLICIT_SOURCE_BOUND_"
        "COMPILERS_AND_STANDARD_TOPOLOGY_DOMAIN_INPUTS"
    )
    assert len(historical["steps"][9]["visible_domain_input_classes"]) == 6


def test_global_sum_and_coefficients_are_derived() -> None:
    checks = load_artifact()["checks"]
    assert checks["global_labeling"] == (
        "PASS_ONE_COMPLETE_LABEL_ASSIGNMENT_PER_FINITE_SUM_TERM"
    )
    assert checks["coefficient_origin"] == (
        "PASS_DIMENSION_TIMES_DERIVED_AUTOMORPHISM_POWER_AT_"
        "CANONICAL_INTEGRAL_EXPONENT"
    )
    assert checks["eventwise_compilation"] == (
        "PASS_VALIDATED_EXECUTION_TRACE_COMPILED_BEFORE_SUMMATION"
    )


def test_proof_grammars_and_all_move_families_remain_separate() -> None:
    checks = load_artifact()["checks"]
    assert checks["proof_grammar_separation"] == (
        "PASS_ISOTOPY_ORDINARY_SLIDE_GENERALIZED_SLIDE_AND_"
        "CANCELLATION_REMAIN_DISTINCT"
    )
    assert checks["move_coverage"] == (
        "PASS_ALL_EIGHT_DIRECTED_TABLE2_CONSTRUCTORS"
    )
    assert checks["movie_induction"] == "PASS_STRUCTURAL_INDUCTION"


def test_exact_axiom_and_domain_input_denominators_are_visible() -> None:
    artifact = load_artifact()
    assert len(artifact["visible_domain_input_classes"]) == 6
    assert artifact["checks"]["domain_input_denominator"] == (
        "PASS_EXACTLY_SIX_VISIBLE_CLASSES"
    )
    assert artifact["explicit_custom_topology_axioms"] == [
        (
            "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
            "standardHandleChainNaturalityInput"
        ),
        (
            "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
            "standardSpecialKirbyCalculusConnected"
        ),
    ]


def test_axiom_audit_and_mutations_passed() -> None:
    checks = load_artifact()["checks"]
    assert checks["axiom_audit"]["audited_declaration_count"] == 145
    assert checks["mutations"]["rejected_count"] == 46
    assert checks["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )


def test_generic_route_is_terminal_without_overclaiming() -> None:
    artifact = load_artifact()
    assert artifact["remaining_steps_in_ten_step_generic_route"] == []
    assert len(artifact["concrete_instantiation_obligations"]) == 3
    nonclaims = "\n".join(artifact["explicit_non_claims"])
    assert "original Crane--Yetter or Yetter state-sum" in nonclaims
    assert "No concrete category has been instantiated." in nonclaims
    assert "general premodular" in nonclaims


def test_pinned_sources_replay_from_clean_source_commit() -> None:
    artifact = load_artifact()
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative
