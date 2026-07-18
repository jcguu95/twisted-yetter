"""Fail-closed v4 contract for the four-manifold invariant target."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from typing import Any, Mapping

from twisted_yetter.source_backed_kirby_completeness_v1 import DOMAIN_AXIOM


RUNTIME_SCHEMA = "twisted-yetter.four-manifold-invariant-target-runtime.v4"
RUNTIME_STATUS = (
    "TARGET_STATED_SIX_FOUNDATION_MECHANISMS_ESTABLISHED_"
    "THREE_SOURCE_BOUND_CONDITIONS_OPEN"
)
MATHEMATICAL_STATUS = "FOUR_MANIFOLD_INVARIANT_NOT_YET_ESTABLISHED"
REQUIRED_CONDITIONS = (
    "category_and_graphical_algebra",
    "explicit_three_handle_normalization",
    "chain_derived_marked_h2_transport",
    "source_backed_special_kirby_calculus_completeness",
    "exhaustive_evaluator_compiler_mechanism",
    "marked_pair_assembly_mechanism",
    "source_bound_local_move_recipes",
    "source_bound_evaluator_compiler_instance",
    "source_bound_geometric_h2_compiler_instance",
)
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:6]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[6:]
COMPILER_CASES = (
    "framed_isotopy",
    "one_over_one",
    "two_over_one",
    "two_over_two",
    "one_two_birth",
    "one_two_death",
    "two_three_birth",
    "two_three_death",
)
EXPLICIT_NONCLAIMS = (
    "This artifact does not claim that a concrete four-manifold invariant "
    "has been established.",
    "Special Kirby completeness is relative to exactly one explicit "
    "source-backed topology domain axiom, not proved from first principles "
    "in Lean.",
    "The topology domain axiom supplies no evaluator equality, chain map, "
    "H2 map, or marked-class compatibility proof.",
    "The eight-case evaluator compiler is an exhaustive interface, not a "
    "constructed source-bound compiler instance.",
    "Marked-pair assembly is derived once local geometric H2 transport is "
    "supplied, but no source-bound local H2 compiler instance exists yet.",
    "The current raw presentation and move metadata do not yet carry enough "
    "typed local edit data to compile graphical and chain proofs.",
    "An arbitrary inhabitant of FourManifoldInvariantInputs is conditional "
    "theorem input and is not admissible construction evidence.",
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
            "required": 9,
            "established": 6,
            "open": 3,
        },
        "four_manifold_invariant_established": False,
        "three_handle_normalization": {
            "dimension_symbol": "d(C)",
            "three_handle_weight": "d(C)^-1",
            "isolated_two_handle_factor": "d(C)",
            "cancelling_pair_product": "1",
            "zero_handle_link_weight": "1",
            "four_handle_link_weight": "1",
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
        "evaluator_compiler_mechanism": {
            "status": "ESTABLISHED_EXHAUSTIVE_INTERFACE_ONLY",
            "required_cases": list(COMPILER_CASES),
            "required_case_count": 8,
            "direct_local_step_field_admitted": False,
            "direct_prescription_target_input_admitted": False,
            "source_bound_instance_constructed": False,
        },
        "marked_pair_assembly_mechanism": {
            "status": "ESTABLISHED_DERIVED_MOVIE_ASSEMBLY_ONLY",
            "direct_marked_system_target_input_admitted": False,
            "marked_transport_sound_is_derived": True,
            "local_transport_identity_required": True,
            "source_bound_instance_constructed": False,
        },
        "source_bound_local_move_recipes": {
            "status": "OPEN_DATA_MODEL_AND_COMPILER_INPUT",
            "raw_presentation_schema_sufficient": False,
            "required_outputs": [
                "typed_local_graphical_recipe",
                "typed_local_handle_chain_recipe",
                "exact_source_target_hash_binding",
            ],
            "opaque_semantic_prop_is_sufficient": False,
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
        == {"required": 9, "established": 6, "open": 3},
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
        and normalization.get("cancelling_pair_product") == "1"
        and normalization.get("zero_handle_link_weight") == "1"
        and normalization.get("four_handle_link_weight") == "1",
        "handle normalization convention changed",
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

    evaluator = payload.get("evaluator_compiler_mechanism")
    _require(
        isinstance(evaluator, dict)
        and evaluator.get("status")
        == "ESTABLISHED_EXHAUSTIVE_INTERFACE_ONLY"
        and evaluator.get("required_cases") == list(COMPILER_CASES)
        and evaluator.get("required_case_count") == 8
        and evaluator.get("direct_local_step_field_admitted") is False
        and evaluator.get("direct_prescription_target_input_admitted")
        is False
        and evaluator.get("source_bound_instance_constructed") is False,
        "evaluator compiler mechanism boundary changed",
    )

    assembly = payload.get("marked_pair_assembly_mechanism")
    _require(
        isinstance(assembly, dict)
        and assembly.get("status")
        == "ESTABLISHED_DERIVED_MOVIE_ASSEMBLY_ONLY"
        and assembly.get("direct_marked_system_target_input_admitted")
        is False
        and assembly.get("marked_transport_sound_is_derived") is True
        and assembly.get("local_transport_identity_required") is True
        and assembly.get("source_bound_instance_constructed") is False,
        "marked-pair assembly mechanism boundary changed",
    )

    recipes = payload.get("source_bound_local_move_recipes")
    _require(
        isinstance(recipes, dict)
        and recipes.get("status") == "OPEN_DATA_MODEL_AND_COMPILER_INPUT"
        and recipes.get("raw_presentation_schema_sufficient") is False
        and recipes.get("opaque_semantic_prop_is_sufficient") is False
        and recipes.get("required_outputs")
        == [
            "typed_local_graphical_recipe",
            "typed_local_handle_chain_recipe",
            "exact_source_target_hash_binding",
        ],
        "source-bound local recipe boundary changed",
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
