"""Fail-closed runtime contract for the four-manifold invariant target."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from typing import Any, Mapping


RUNTIME_SCHEMA = "twisted-yetter.four-manifold-invariant-target-runtime.v1"
RUNTIME_STATUS = (
    "TARGET_STATED_SIMPLE_THREE_HANDLE_NORMALIZATION_ESTABLISHED_"
    "HARD_CONDITIONS_OPEN"
)
MATHEMATICAL_STATUS = "FOUR_MANIFOLD_INVARIANT_NOT_YET_ESTABLISHED"
REQUIRED_CONDITIONS = (
    "category_and_graphical_algebra",
    "explicit_three_handle_normalization",
    "concrete_evaluator_compiler",
    "special_kirby_calculus_completeness",
    "chain_derived_marked_h2_transport",
    "concrete_marked_pair_assembly",
)
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:2]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[2:]
EXPLICIT_NONCLAIMS = (
    "This target artifact does not claim that a concrete four-manifold "
    "invariant has been established.",
    "The special Kirby calculus completeness bridge remains an explicit "
    "source-backed topology input.",
    "The marked H2 transport has not yet been derived from a handle chain "
    "complex in Lean.",
    "A concrete evaluator compiler has not yet assembled the localStep "
    "proof for every presentation, move, and marked class.",
    "An arbitrary inhabitant of FourManifoldInvariantInputs is not admissible "
    "until its nested semantic boundaries are concretely derived.",
    "No identification with a Crane-Yetter state sum is required or claimed.",
    "No CTL theorem, objective note, or claim is admitted by this artifact.",
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
            "lean_witnesses": [
                "GlobalDimensionProfile."
                "twoThreeFactor_mul_threeHandleWeight",
                "GlobalDimensionProfile.denominator_ratio_addTwoThree",
                "TwoThreeLocalCalculation."
                "raw_with_explicit_three_handle",
            ],
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
    """Reject any hidden condition loss or premature invariant promotion."""

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
        == {"required": 6, "established": 2, "open": 4},
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
    _require(
        len(normalization.get("lean_witnesses", [])) == 3,
        "three-handle Lean witness denominator changed",
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
