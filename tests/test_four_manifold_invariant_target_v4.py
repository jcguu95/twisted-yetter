from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.four_manifold_invariant_target_v4 import (
    COMPILER_CASES,
    ESTABLISHED_CONDITIONS,
    EXPLICIT_NONCLAIMS,
    OPEN_CONDITIONS,
    REQUIRED_CONDITIONS,
    build_target_runtime,
    canonical_hash,
    validate_target_runtime,
)


@pytest.fixture
def runtime() -> dict[str, object]:
    return build_target_runtime()


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_exact_six_three_condition_partition(
    runtime: dict[str, object],
) -> None:
    validate_target_runtime(runtime)
    assert runtime["required_conditions"] == list(REQUIRED_CONDITIONS)
    assert runtime["established_conditions"] == list(
        ESTABLISHED_CONDITIONS
    )
    assert runtime["open_conditions"] == list(OPEN_CONDITIONS)
    assert runtime["condition_counts"] == {
        "required": 9,
        "established": 6,
        "open": 3,
    }


def test_topology_axiom_is_exactly_one_and_bare(
    runtime: dict[str, object],
) -> None:
    completeness = runtime["source_backed_special_kirby_completeness"]
    assert completeness["domain_axiom_count"] == 1
    assert completeness["output"] == "TopologicalTableTwoMovie"
    assert completeness["evaluator_equality_in_output"] is False
    assert completeness["marked_h2_transport_in_output"] is False
    assert completeness["local_chain_enrichment_required"] is True


def test_evaluator_compiler_denominator_is_exact(
    runtime: dict[str, object],
) -> None:
    compiler = runtime["evaluator_compiler_mechanism"]
    assert compiler["required_cases"] == list(COMPILER_CASES)
    assert compiler["required_case_count"] == 8
    assert compiler["direct_local_step_field_admitted"] is False
    assert compiler["direct_prescription_target_input_admitted"] is False
    assert compiler["source_bound_instance_constructed"] is False


def test_marked_assembly_is_derived_but_not_instantiated(
    runtime: dict[str, object],
) -> None:
    assembly = runtime["marked_pair_assembly_mechanism"]
    assert assembly["marked_transport_sound_is_derived"] is True
    assert assembly["direct_marked_system_target_input_admitted"] is False
    assert assembly["local_transport_identity_required"] is True
    assert assembly["source_bound_instance_constructed"] is False


def test_local_recipe_gap_is_machine_visible(
    runtime: dict[str, object],
) -> None:
    recipes = runtime["source_bound_local_move_recipes"]
    assert recipes["status"] == "OPEN_DATA_MODEL_AND_COMPILER_INPUT"
    assert recipes["raw_presentation_schema_sufficient"] is False
    assert recipes["opaque_semantic_prop_is_sufficient"] is False
    assert len(recipes["required_outputs"]) == 3


def test_topology_axiom_growth_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    completeness = mutation["source_backed_special_kirby_completeness"]
    completeness["domain_axioms"].append("HiddenAxiom")
    completeness["domain_axiom_count"] = 2
    rehash(mutation)
    with pytest.raises(ValueError, match="domain-axiom"):
        validate_target_runtime(mutation)


@pytest.mark.parametrize(
    "field",
    ("evaluator_equality_in_output", "marked_h2_transport_in_output"),
)
def test_silent_topology_enrichment_fails_closed(
    runtime: dict[str, object], field: str
) -> None:
    mutation = deepcopy(runtime)
    mutation["source_backed_special_kirby_completeness"][field] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="silently enriched"):
        validate_target_runtime(mutation)


def test_premature_invariant_promotion_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["four_manifold_invariant_established"] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="premature"):
        validate_target_runtime(mutation)


def test_closing_recipe_gap_without_evidence_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    condition = mutation["open_conditions"].pop(0)
    mutation["established_conditions"].append(condition)
    mutation["condition_counts"] = {
        "required": 9,
        "established": 7,
        "open": 2,
    }
    rehash(mutation)
    with pytest.raises(ValueError, match="established"):
        validate_target_runtime(mutation)


def test_compiler_case_loss_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["evaluator_compiler_mechanism"]["required_cases"].pop()
    mutation["evaluator_compiler_mechanism"]["required_case_count"] = 7
    rehash(mutation)
    with pytest.raises(ValueError, match="compiler mechanism"):
        validate_target_runtime(mutation)


def test_fake_local_recipe_sufficiency_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["source_bound_local_move_recipes"][
        "raw_presentation_schema_sufficient"
    ] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="local recipe"):
        validate_target_runtime(mutation)


def test_three_handle_and_h2_boundaries_remain_explicit(
    runtime: dict[str, object],
) -> None:
    normalization = runtime["three_handle_normalization"]
    assert normalization["three_handle_weight"] == "d(C)^-1"
    assert normalization["zero_handle_link_weight"] == "1"
    assert normalization["four_handle_link_weight"] == "1"
    h2 = runtime["chain_derived_marked_h2_transport"]
    assert h2["move_input"] == "chain_homotopy_equivalence"
    assert h2["handwritten_h2_equivalence_admitted"] is False


def test_nonclaim_denominator_is_exact(runtime: dict[str, object]) -> None:
    assert runtime["explicit_nonclaims"] == list(EXPLICIT_NONCLAIMS)
    assert runtime["target_theorem"][
        "concrete_input_instance_constructed"
    ] is False
