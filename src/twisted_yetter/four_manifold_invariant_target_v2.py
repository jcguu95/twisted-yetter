"""Fail-closed v2 contract for the four-manifold invariant target."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from typing import Any, Mapping


RUNTIME_SCHEMA = "twisted-yetter.four-manifold-invariant-target-runtime.v2"
RUNTIME_STATUS = (
    "TARGET_STATED_THREE_FOUNDATION_CONDITIONS_ESTABLISHED_"
    "THREE_HARD_CONDITIONS_OPEN"
)
MATHEMATICAL_STATUS = "FOUR_MANIFOLD_INVARIANT_NOT_YET_ESTABLISHED"
REQUIRED_CONDITIONS = (
    "category_and_graphical_algebra",
    "explicit_three_handle_normalization",
    "chain_derived_marked_h2_transport",
    "concrete_evaluator_compiler",
    "special_kirby_calculus_completeness",
    "concrete_marked_pair_assembly",
)
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:3]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[3:]
H2_LEAN_WITNESSES = (
    "HandleChainEquivalence.secondHomologyLinearEquiv",
    "HandleChainEquivalence.secondHomologyAddEquiv",
    "HandleChainEquivalence.secondHomologyEquiv_refl_apply",
    "MarkedH2Transport.targetClass_add",
    "MarkedH2Transport.pairing_preserved",
    "TableTwoMovie.targetClass_add",
    "TableTwoMovie.homologyEquiv_trans",
)
EXPLICIT_NONCLAIMS = (
    "This artifact does not claim that a concrete four-manifold invariant "
    "has been established.",
    "The special Kirby calculus completeness theorem remains an explicit "
    "source-backed topology input.",
    "A concrete evaluator compiler has not yet assembled every local-step "
    "proof from coupon and link syntax.",
    "The generic chain-derived H2 mechanism is established, but concrete "
    "Kirby diagrams are not yet bound to boundary matrices and chain maps.",
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
            "required": len(REQUIRED_CONDITIONS),
            "established": len(ESTABLISHED_CONDITIONS),
            "open": len(OPEN_CONDITIONS),
        },
        "four_manifold_invariant_established": False,
        "three_handle_normalization": {
            "dimension_symbol": "d(C)",
            "three_handle_weight": "d(C)^-1",
            "total_quantum_dimension_warning": (
                "If script-D^2 = d(C), this weight is script-D^-2."
            ),
            "isolated_two_handle_factor": "d(C)",
            "cancelling_pair_product": "1",
        },
        "chain_derived_marked_h2_transport": {
            "status": "ESTABLISHED_GENERIC_MECHANISM",
            "chain_ring": "Z",
            "chain_degrees": [0, 1, 2, 3, 4],
            "second_homology_degree": 2,
            "move_input": "chain_homotopy_equivalence",
            "derived_output": "additive_equivalence_on_second_homology",
            "character_transport": "precomposition_with_inverse",
            "handwritten_h2_equivalence_admitted": False,
            "handwritten_target_character_admitted": False,
            "lean_witnesses": list(H2_LEAN_WITNESSES),
            "remaining_concrete_boundary": (
                "Bind each concrete Kirby presentation and move to its "
                "handle boundary matrices, bases, and chain equivalence."
            ),
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
    """Reject condition loss, handwritten H2 data, or premature promotion."""

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
        len(set(required)) == len(REQUIRED_CONDITIONS),
        "duplicate target condition",
    )
    _require(
        established + open_conditions == required,
        "target condition partition mismatch",
    )
    _require(
        payload.get("condition_counts")
        == {"required": 6, "established": 3, "open": 3},
        "target condition counts changed",
    )
    _require(
        payload.get("four_manifold_invariant_established") is False,
        "premature four-manifold invariant promotion",
    )
    _require(
        all("crane_yetter" not in item for item in required),
        "Crane-Yetter identification was added as a target condition",
    )

    normalization = payload.get("three_handle_normalization")
    _require(
        isinstance(normalization, dict)
        and normalization.get("dimension_symbol") == "d(C)"
        and normalization.get("three_handle_weight") == "d(C)^-1"
        and normalization.get("isolated_two_handle_factor") == "d(C)"
        and normalization.get("cancelling_pair_product") == "1",
        "three-handle normalization convention changed",
    )

    h2 = payload.get("chain_derived_marked_h2_transport")
    _require(isinstance(h2, dict), "chain-derived H2 section missing")
    _require(
        h2.get("status") == "ESTABLISHED_GENERIC_MECHANISM",
        "chain-derived H2 status changed",
    )
    _require(
        h2.get("chain_ring") == "Z"
        and h2.get("chain_degrees") == [0, 1, 2, 3, 4]
        and h2.get("second_homology_degree") == 2,
        "handle-chain model changed",
    )
    _require(
        h2.get("move_input") == "chain_homotopy_equivalence"
        and h2.get("derived_output")
        == "additive_equivalence_on_second_homology",
        "H2 transport is no longer chain-derived",
    )
    _require(
        h2.get("handwritten_h2_equivalence_admitted") is False
        and h2.get("handwritten_target_character_admitted") is False,
        "handwritten H2 or character transport was admitted",
    )
    _require(
        h2.get("lean_witnesses") == list(H2_LEAN_WITNESSES),
        "chain-derived H2 Lean witness denominator changed",
    )
    _require(
        isinstance(h2.get("remaining_concrete_boundary"), str)
        and "boundary matrices" in h2["remaining_concrete_boundary"],
        "concrete H2 assembly boundary was hidden",
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
