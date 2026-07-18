"""Fail-closed v3 contract for the four-manifold invariant target."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from typing import Any, Mapping

from twisted_yetter.source_backed_kirby_completeness_v1 import DOMAIN_AXIOM


RUNTIME_SCHEMA = "twisted-yetter.four-manifold-invariant-target-runtime.v3"
RUNTIME_STATUS = (
    "TARGET_STATED_FOUR_FOUNDATION_CONDITIONS_ESTABLISHED_"
    "TWO_CONCRETE_CONDITIONS_OPEN"
)
MATHEMATICAL_STATUS = "FOUR_MANIFOLD_INVARIANT_NOT_YET_ESTABLISHED"
REQUIRED_CONDITIONS = (
    "category_and_graphical_algebra",
    "explicit_three_handle_normalization",
    "chain_derived_marked_h2_transport",
    "source_backed_special_kirby_calculus_completeness",
    "concrete_evaluator_compiler",
    "concrete_marked_pair_assembly",
)
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:4]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[4:]
EXPLICIT_NONCLAIMS = (
    "This artifact does not claim that a concrete four-manifold invariant "
    "has been established.",
    "Special Kirby completeness is relative to exactly one explicit "
    "source-backed topology domain axiom, not proved from first principles "
    "in Lean.",
    "The topology domain axiom supplies no evaluator equality, chain map, "
    "H2 map, or marked-class compatibility proof.",
    "A concrete evaluator compiler has not yet assembled every local move "
    "from coupon and link syntax.",
    "Concrete Kirby presentations are not yet bound to handle boundary "
    "matrices, local chain equivalences, and marked-pair certificates.",
    "An arbitrary inhabitant of FourManifoldInvariantInputs is not "
    "admissible evidence.",
    "No identification with a Crane-Yetter state sum is required or claimed.",
    "No CTL theorem claim is admitted by this repo-local artifact.",
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


def build_target_runtime() -> dict[str, Any]:
    """Build the exact current target boundary."""

    payload: dict[str, Any] = {
        "schema": RUNTIME_SCHEMA,
        "status": RUNTIME_STATUS,
        "mathematical_status": MATHEMATICAL_STATUS,
        "required_conditions": list(REQUIRED_CONDITIONS),
        "established_conditions": list(ESTABLISHED_CONDITIONS),
        "open_conditions": list(OPEN_CONDITIONS),
        "condition_counts": {
            "required": 6,
            "established": 4,
            "open": 2,
        },
        "four_manifold_invariant_established": False,
        "three_handle_normalization": {
            "dimension_symbol": "d(C)",
            "three_handle_weight": "d(C)^-1",
            "isolated_two_handle_factor": "d(C)",
            "cancelling_pair_product": "1",
        },
        "chain_derived_marked_h2_transport": {
            "status": "ESTABLISHED_GENERIC_MECHANISM",
            "chain_ring": "Z",
            "move_input": "chain_homotopy_equivalence",
            "derived_output": "additive_equivalence_on_second_homology",
            "handwritten_h2_equivalence_admitted": False,
            "handwritten_target_character_admitted": False,
        },
        "source_backed_special_kirby_completeness": {
            "status": (
                "ESTABLISHED_RELATIVE_TO_EXACTLY_ONE_DOMAIN_AXIOM"
            ),
            "domain_axioms": [DOMAIN_AXIOM],
            "domain_axiom_count": 1,
            "output": "TopologicalTableTwoMovie",
            "evaluator_equality_in_output": False,
            "marked_h2_transport_in_output": False,
            "local_chain_enrichment_required": True,
        },
        "target_theorem": {
            "lean_input_type": "FourManifoldInvariantInputs",
            "lean_theorem": (
                "FourManifoldInvariantInputs."
                "four_manifold_invariant_target"
            ),
            "statement": (
                "Any two certified special Kirby realizations of the same "
                "marked pair have equal normalized evaluator values."
            ),
            "concrete_input_instance_constructed": False,
        },
        "explicit_nonclaims": list(EXPLICIT_NONCLAIMS),
    }
    payload["content_hash"] = canonical_hash(payload)
    validate_target_runtime(payload)
    return payload


def validate_target_runtime(payload: Mapping[str, Any]) -> None:
    """Reject condition loss, axiom growth, or premature promotion."""

    _require(payload.get("schema") == RUNTIME_SCHEMA, "target schema mismatch")
    _require(payload.get("status") == RUNTIME_STATUS, "target status mismatch")
    _require(
        payload.get("mathematical_status") == MATHEMATICAL_STATUS,
        "target mathematical status mismatch",
    )
    _require(
        payload.get("content_hash") == canonical_hash(payload),
        "target content hash is stale",
    )
    required = payload.get("required_conditions")
    established = payload.get("established_conditions")
    open_conditions = payload.get("open_conditions")
    _require(
        required == list(REQUIRED_CONDITIONS),
        "required target-condition denominator changed",
    )
    _require(
        established == list(ESTABLISHED_CONDITIONS),
        "established target-condition set changed",
    )
    _require(
        open_conditions == list(OPEN_CONDITIONS),
        "open target-condition set changed",
    )
    _require(
        established + open_conditions == required,
        "target condition partition mismatch",
    )
    _require(
        payload.get("condition_counts")
        == {"required": 6, "established": 4, "open": 2},
        "target condition counts changed",
    )
    _require(
        payload.get("four_manifold_invariant_established") is False,
        "premature four-manifold invariant promotion",
    )
    _require(
        all("crane_yetter" not in item for item in required),
        "Crane-Yetter identification entered the target denominator",
    )

    normalization = payload.get("three_handle_normalization")
    _require(
        isinstance(normalization, dict)
        and normalization.get("three_handle_weight") == "d(C)^-1"
        and normalization.get("isolated_two_handle_factor") == "d(C)"
        and normalization.get("cancelling_pair_product") == "1",
        "three-handle normalization convention changed",
    )

    h2 = payload.get("chain_derived_marked_h2_transport")
    _require(
        isinstance(h2, dict)
        and h2.get("status") == "ESTABLISHED_GENERIC_MECHANISM"
        and h2.get("move_input") == "chain_homotopy_equivalence"
        and h2.get("derived_output")
        == "additive_equivalence_on_second_homology"
        and h2.get("handwritten_h2_equivalence_admitted") is False
        and h2.get("handwritten_target_character_admitted") is False,
        "chain-derived H2 boundary changed",
    )

    completeness = payload.get(
        "source_backed_special_kirby_completeness"
    )
    _require(
        isinstance(completeness, dict)
        and completeness.get("status")
        == "ESTABLISHED_RELATIVE_TO_EXACTLY_ONE_DOMAIN_AXIOM"
        and completeness.get("domain_axioms") == [DOMAIN_AXIOM]
        and completeness.get("domain_axiom_count") == 1,
        "special Kirby domain-axiom denominator changed",
    )
    _require(
        completeness.get("output") == "TopologicalTableTwoMovie"
        and completeness.get("evaluator_equality_in_output") is False
        and completeness.get("marked_h2_transport_in_output") is False
        and completeness.get("local_chain_enrichment_required") is True,
        "topology completeness was silently enriched",
    )

    theorem = payload.get("target_theorem")
    _require(
        isinstance(theorem, dict)
        and theorem.get("lean_input_type") == "FourManifoldInvariantInputs"
        and theorem.get("lean_theorem")
        == "FourManifoldInvariantInputs.four_manifold_invariant_target"
        and theorem.get("concrete_input_instance_constructed") is False,
        "target theorem boundary changed",
    )
    _require(
        payload.get("explicit_nonclaims") == list(EXPLICIT_NONCLAIMS),
        "target non-claim denominator changed",
    )
