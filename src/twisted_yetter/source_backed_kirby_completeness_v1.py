"""Fail-closed contract for the special Kirby topology domain axiom."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from typing import Any, Mapping


RUNTIME_SCHEMA = (
    "twisted-yetter.source-backed-special-kirby-completeness-runtime.v1"
)
RUNTIME_STATUS = (
    "SPECIAL_KIRBY_TOPOLOGY_COMPLETENESS_IMPORTED_AS_ONE_DOMAIN_AXIOM"
)
MATHEMATICAL_STATUS = (
    "TOPOLOGY_COMPLETENESS_ESTABLISHED_RELATIVE_TO_EXPLICIT_DOMAIN_AXIOM"
)
DOMAIN_AXIOM = (
    "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
    "standardSpecialKirbyCalculusConnected"
)
SOURCE_REFS = (
    "ref:baerenz-barrett-dichromatic-2018",
    "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
    "ref:de-sa-link-calculus-1979",
)
TOPOLOGY_MOVE_FAMILIES = (
    "framed_isotopy",
    "one_over_one_slide",
    "two_over_one_slide",
    "two_over_two_slide",
    "one_two_cancellation",
    "two_three_cancellation",
)
EXPLICIT_NONCLAIMS = (
    "This contract imports one topology domain axiom; it is not a Lean proof "
    "of special Kirby calculus.",
    "The domain axiom returns only TopologicalTableTwoMovie.",
    "The domain axiom does not return an evaluator equality.",
    "The domain axiom does not return a chain map, H2 map, or marked-class "
    "compatibility proof.",
    "Concrete presentation certificates and local chain enrichment remain "
    "open assembly inputs.",
    "This contract does not establish a four-manifold invariant.",
    "This contract does not identify any construction with Crane-Yetter.",
    "This repo-local artifact does not admit a CTL theorem claim.",
)


def canonical_hash(payload: Mapping[str, Any]) -> str:
    """Hash a JSON object while omitting its own content hash."""

    body = deepcopy(dict(payload))
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def build_runtime() -> dict[str, Any]:
    """Build the exact current domain-axiom boundary."""

    payload: dict[str, Any] = {
        "schema": RUNTIME_SCHEMA,
        "status": RUNTIME_STATUS,
        "mathematical_status": MATHEMATICAL_STATUS,
        "domain_axioms": [DOMAIN_AXIOM],
        "domain_axiom_count": 1,
        "source_refs": list(SOURCE_REFS),
        "topology_move_families": list(TOPOLOGY_MOVE_FAMILIES),
        "scope": {
            "dimension": 4,
            "smooth": True,
            "oriented": True,
            "closed": True,
            "connected": True,
            "presentation": "special_framed_link",
            "unique_zero_handle": True,
            "unique_four_handle": True,
        },
        "domain_axiom_output": "TopologicalTableTwoMovie",
        "evaluator_data_in_domain_axiom": False,
        "marked_h2_data_in_domain_axiom": False,
        "local_chain_enrichment_required": True,
        "local_chain_enrichment_output": "MarkedH2Transport",
        "movie_enrichment_forgetfulness_proved": True,
        "four_manifold_invariant_established": False,
        "explicit_nonclaims": list(EXPLICIT_NONCLAIMS),
    }
    payload["content_hash"] = canonical_hash(payload)
    validate_runtime(payload)
    return payload


def validate_runtime(payload: Mapping[str, Any]) -> None:
    """Reject axiom growth, scope widening, or hidden enrichment."""

    _require(payload.get("schema") == RUNTIME_SCHEMA, "schema mismatch")
    _require(payload.get("status") == RUNTIME_STATUS, "status mismatch")
    _require(
        payload.get("mathematical_status") == MATHEMATICAL_STATUS,
        "mathematical status mismatch",
    )
    _require(
        payload.get("content_hash") == canonical_hash(payload),
        "content hash is stale",
    )
    _require(
        payload.get("domain_axioms") == [DOMAIN_AXIOM]
        and payload.get("domain_axiom_count") == 1,
        "domain axiom denominator changed",
    )
    _require(
        payload.get("source_refs") == list(SOURCE_REFS),
        "source reference denominator changed",
    )
    _require(
        payload.get("topology_move_families")
        == list(TOPOLOGY_MOVE_FAMILIES),
        "topology move denominator changed",
    )
    scope = payload.get("scope")
    _require(
        scope
        == {
            "dimension": 4,
            "smooth": True,
            "oriented": True,
            "closed": True,
            "connected": True,
            "presentation": "special_framed_link",
            "unique_zero_handle": True,
            "unique_four_handle": True,
        },
        "special Kirby scope changed",
    )
    _require(
        payload.get("domain_axiom_output") == "TopologicalTableTwoMovie",
        "domain axiom output was enriched",
    )
    _require(
        payload.get("evaluator_data_in_domain_axiom") is False
        and payload.get("marked_h2_data_in_domain_axiom") is False,
        "evaluator or marked H2 data entered the topology axiom",
    )
    _require(
        payload.get("local_chain_enrichment_required") is True
        and payload.get("local_chain_enrichment_output")
        == "MarkedH2Transport"
        and payload.get("movie_enrichment_forgetfulness_proved") is True,
        "chain enrichment boundary changed",
    )
    _require(
        payload.get("four_manifold_invariant_established") is False,
        "premature four-manifold invariant promotion",
    )
    _require(
        payload.get("explicit_nonclaims") == list(EXPLICIT_NONCLAIMS),
        "nonclaim denominator changed",
    )
