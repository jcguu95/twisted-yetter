from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v12.json"
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


def test_content_hash_and_honest_status() -> None:
    artifact = load_artifact()
    payload = dict(artifact)
    observed = payload.pop("content_hash")
    assert observed == sha256_bytes(canonical_bytes(payload))
    assert (
        artifact["schema"]
        == "twisted-yetter.four-manifold-invariant-target.v12"
    )
    assert artifact["status"] == (
        "PASS_LAST_FIVE_TERMINALIZED_"
        "WITH_EXPLICIT_CONCRETE_INPUT_BLOCKERS"
    )
    assert artifact["mathematical_status"].endswith(
        "CONCRETE_FOUR_MANIFOLD_INVARIANT_NOT_YET_ESTABLISHED"
    )


def test_exact_target_partition_is_16_plus_4() -> None:
    ledger = load_artifact()["target_condition_ledger"]
    assert ledger["counts"] == {
        "required": 20,
        "established": 16,
        "open": 4,
    }
    assert (
        ledger["established_conditions"] + ledger["open_conditions"]
        == ledger["required_conditions"]
    )
    assert ledger["established_conditions"][-1] == (
        "integralCycleRepresentativeSystemInstance"
    )
    assert ledger["open_conditions"] == [
        "tensorAutomorphismGeneratorInstance",
        "globalFiniteKirbyColorExpansionInstance",
        "sourceBoundGraphicalMoveCompilerInstance",
        "sourceBoundEvaluatorCompilerInstance",
    ]


def test_all_five_requested_items_have_terminal_outcomes() -> None:
    outcomes = load_artifact()["last_five_terminal_outcomes"]
    assert [outcome["ordinal"] for outcome in outcomes] == [1, 2, 3, 4, 5]
    assert outcomes[0]["status"] == "ESTABLISHED_KERNEL_CHECKED"
    assert all(
        outcome["status"].startswith("TERMINAL_BLOCKED_")
        for outcome in outcomes[1:]
    )
    assert outcomes[4]["mechanism_status"] == (
        "PASS_FINAL_ASSEMBLER_KERNEL_CHECKED"
    )
    assert "outcomes 3 and 4" in outcomes[4]["missing"]


def test_event_and_cancellation_silent_fail_guards() -> None:
    artifact = load_artifact()
    safety = artifact["safety_hardening"]
    assert safety["whole_event_compiler_is_derived"] is True
    assert safety["event_exterior_is_coherence_only"] is True
    assert "coupon ID and label" in safety["event_windows_bind"]
    assert "framing-twist strand ID" in safety["event_windows_bind"]
    assert safety["birth_and_death_use_explicit_exact_pairings"] is True
    assert safety["category_dual_cannot_be_silently_replaced"] is True
    assert (
        safety["cancellation_raw_factor_is_derived_from_diagram_factorization"]
        is True
    )
    assert safety["handwritten_raw_or_normalized_move_equality_rejected"]
    assert safety["final_assembler_accepts_no_evaluator_function"] is True
    assert safety["final_assembler_accepts_no_move_equality"] is True


def test_mutation_axiom_and_thread_denominators() -> None:
    checks = load_artifact()["checks"]
    assert checks["mutation_denominators"] == {
        "categorical_event_compiler": 9,
        "integral_character_compiler": 7,
        "source_bound_graphical_compiler": 5,
        "four_manifold_target": 5,
    }
    assert checks["proof_oracles"] == []
    assert checks["mechanism_custom_domain_axioms"] == []
    assert checks["target_domain_axioms"] == [
        (
            "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
            "standardHandleChainNaturalityInput"
        ),
        (
            "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
            "standardSpecialKirbyCalculusConnected"
        ),
    ]
    assert checks["umbrella_build"] == {
        "status": "PASS",
        "lean_num_threads": 1,
    }


def test_terminal_blockers_cannot_be_closed_by_metadata() -> None:
    artifact = load_artifact()
    boundary = artifact["terminal_blocker_boundary"]
    assert boundary["repo_has_concrete_lean_mtc_fixture"] is False
    assert boundary["repo_has_category_neutral_source_recipes"] is True
    assert (
        boundary["category_neutral_recipes_include_typed_category_morphisms"]
        is False
    )
    assert boundary["blockers_can_be_closed_by_hash_only"] is False
    assert boundary["blockers_can_be_closed_by_numerical_artifacts_only"] is (
        False
    )
    assert len(boundary["required_next_evidence"]) == 3

    target = artifact["target_theorem"]
    assert target["conditional_on_concrete_inputs"] is True
    assert target["concrete_inputs_constructed"] is False
    nonclaims = "\n".join(artifact["non_claims"])
    assert "No concrete four-manifold invariant" in nonclaims
    assert "No open condition was renamed" in nonclaims
    assert "No numerical category artifact" in nonclaims


def test_source_file_hashes_are_fresh() -> None:
    artifact = load_artifact()
    for relative, record in artifact["inputs"]["source_files"].items():
        data = (ROOT / relative).read_bytes()
        assert record == {
            "bytes": len(data),
            "sha256": sha256_bytes(data),
        }
