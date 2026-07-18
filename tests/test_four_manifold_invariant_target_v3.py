from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.four_manifold_invariant_target_v3 import (
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


def test_exact_four_two_condition_partition(
    runtime: dict[str, object],
) -> None:
    validate_target_runtime(runtime)
    assert runtime["required_conditions"] == list(REQUIRED_CONDITIONS)
    assert runtime["established_conditions"] == list(
        ESTABLISHED_CONDITIONS
    )
    assert runtime["open_conditions"] == list(OPEN_CONDITIONS)
    assert runtime["condition_counts"] == {
        "required": 6,
        "established": 4,
        "open": 2,
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


def test_closing_compiler_without_evidence_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    condition = mutation["open_conditions"].pop(0)
    mutation["established_conditions"].append(condition)
    mutation["condition_counts"] = {
        "required": 6,
        "established": 5,
        "open": 1,
    }
    rehash(mutation)
    with pytest.raises(ValueError, match="established"):
        validate_target_runtime(mutation)


def test_three_handle_and_h2_boundaries_remain_explicit(
    runtime: dict[str, object],
) -> None:
    assert runtime["three_handle_normalization"]["three_handle_weight"] == (
        "d(C)^-1"
    )
    h2 = runtime["chain_derived_marked_h2_transport"]
    assert h2["move_input"] == "chain_homotopy_equivalence"
    assert h2["handwritten_h2_equivalence_admitted"] is False


def test_nonclaim_denominator_is_exact(runtime: dict[str, object]) -> None:
    assert runtime["explicit_nonclaims"] == list(EXPLICIT_NONCLAIMS)
    assert runtime["target_theorem"][
        "concrete_input_instance_constructed"
    ] is False
