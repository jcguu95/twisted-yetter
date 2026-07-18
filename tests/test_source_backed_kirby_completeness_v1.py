from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.source_backed_kirby_completeness_v1 import (
    DOMAIN_AXIOM,
    EXPLICIT_NONCLAIMS,
    MATHEMATICAL_STATUS,
    RUNTIME_STATUS,
    SOURCE_REFS,
    TOPOLOGY_MOVE_FAMILIES,
    build_runtime,
    canonical_hash,
    validate_runtime,
)


@pytest.fixture
def runtime() -> dict[str, object]:
    return build_runtime()


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_exactly_one_named_domain_axiom(runtime: dict[str, object]) -> None:
    validate_runtime(runtime)
    assert runtime["status"] == RUNTIME_STATUS
    assert runtime["mathematical_status"] == MATHEMATICAL_STATUS
    assert runtime["domain_axioms"] == [DOMAIN_AXIOM]
    assert runtime["domain_axiom_count"] == 1


def test_source_and_move_denominators_are_exact(
    runtime: dict[str, object],
) -> None:
    assert runtime["source_refs"] == list(SOURCE_REFS)
    assert runtime["topology_move_families"] == list(
        TOPOLOGY_MOVE_FAMILIES
    )


def test_domain_axiom_returns_bare_topology_only(
    runtime: dict[str, object],
) -> None:
    assert runtime["domain_axiom_output"] == "TopologicalTableTwoMovie"
    assert runtime["evaluator_data_in_domain_axiom"] is False
    assert runtime["marked_h2_data_in_domain_axiom"] is False


def test_local_chain_enrichment_remains_required(
    runtime: dict[str, object],
) -> None:
    assert runtime["local_chain_enrichment_required"] is True
    assert runtime["local_chain_enrichment_output"] == "MarkedH2Transport"
    assert runtime["movie_enrichment_forgetfulness_proved"] is True


def test_hidden_second_domain_axiom_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["domain_axioms"].append("unsafe.secondAxiom")
    mutation["domain_axiom_count"] = 2
    rehash(mutation)
    with pytest.raises(ValueError, match="axiom denominator"):
        validate_runtime(mutation)


def test_hidden_enrichment_in_domain_axiom_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["domain_axiom_output"] = "TableTwoMovie"
    mutation["marked_h2_data_in_domain_axiom"] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="output was enriched|marked H2"):
        validate_runtime(mutation)


def test_scope_widening_fails_closed(runtime: dict[str, object]) -> None:
    mutation = deepcopy(runtime)
    mutation["scope"]["closed"] = False
    rehash(mutation)
    with pytest.raises(ValueError, match="scope"):
        validate_runtime(mutation)


def test_premature_invariant_promotion_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["four_manifold_invariant_established"] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="premature"):
        validate_runtime(mutation)


def test_nonclaim_denominator_is_exact(runtime: dict[str, object]) -> None:
    assert runtime["explicit_nonclaims"] == list(EXPLICIT_NONCLAIMS)
    assert any("not a Lean proof" in item for item in EXPLICIT_NONCLAIMS)
