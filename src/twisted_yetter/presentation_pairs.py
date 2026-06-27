"""Deterministic Kirby presentation-pair dry-run registry for n45.

This module records toy presentation-pair metadata for later decorated Kirby
move gates.  It is deliberately a registry layer only: no handle-slide algebra,
no basis-change proof, no link evaluation, no Kirby sum, no closed invariant,
and no exotic-smooth claim.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from typing import Final, Mapping, Sequence

from twisted_yetter.candidate_validation_suite import (
    many_case_candidate_validation_suite_artifact,
)
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate

PRESENTATION_PAIR_REGISTRY_SCHEMA: Final = (
    "twisted-yetter.kirby-presentation-pair-registry.v1"
)
PRESENTATION_PAIR_NOTE: Final = (
    "wiki/understandings/kirby-presentation-pair-generator.org"
)

CLAIM_LEVEL: Final = "computed evidence scaffold"
SOURCE_STATUS: Final = (
    "n45 deterministic Kirby/link presentation-pair dry-run metadata; "
    "candidate pairs only and no equivalence proof is recorded"
)

RELATION_STATUS: Final = "candidate/dry-run"
DEFAULT_LINEAGE_STATUS: Final = (
    "placeholder only; component lineage is recorded for n50 consumption and "
    "does not certify a Kirby move"
)
DEFAULT_BASIS_MAP_STATUS: Final = (
    "placeholder only; no GL(n,Z), H2 marking, or handle-slide proof"
)

DOES_NOT_PROVE: Final = (
    "presentation equivalence",
    "Kirby move proof",
    "decorated Kirby move proof",
    "basis-change proof",
    "link evaluation",
    "Kirby color sum",
    "closed invariant",
    "exotic claims",
)

BLOCKED_HIGH_CLAIMS: Final = (
    "presentation equivalence theorem",
    "decorated Kirby move proof",
    "claim-supporting closed 4D invariant",
    "exotic detection claim",
)


@dataclass(frozen=True)
class PresentationPairSpec:
    """A fixed n45 dry-run pair assembled from n36 case summaries."""

    pair_id: str
    left_case_id: str
    right_case_id: str
    relation_type: str
    component_lineage: Mapping[str, str]
    component_lineage_status: str = DEFAULT_LINEAGE_STATUS
    basis_map_status: str = DEFAULT_BASIS_MAP_STATUS
    source_status: str = "schema/test-safe dry-run fixture metadata"


DEFAULT_PAIR_SPECS: Final[tuple[PresentationPairSpec, ...]] = (
    PresentationPairSpec(
        pair_id="identity-s4-trivial-zero",
        left_case_id="s4-trivial-zero",
        right_case_id="s4-trivial-zero",
        relation_type="identity",
        component_lineage={},
        component_lineage_status=(
            "identity on the empty component set; still not a closed invariant claim"
        ),
        basis_map_status="empty identity placeholder; no H2 marking is certified",
    ),
    PresentationPairSpec(
        pair_id="identity-cp2-z2-zero",
        left_case_id="cp2-z2-zero",
        right_case_id="cp2-z2-zero",
        relation_type="identity/zero-decoration",
        component_lineage={"cp2_h": "cp2_h"},
        component_lineage_status="identity component lineage placeholder",
        basis_map_status="1x1 identity placeholder; not a Kirby proof",
    ),
    PresentationPairSpec(
        pair_id="identity-cp2-z2-nonzero",
        left_case_id="cp2-z2-nonzero",
        right_case_id="cp2-z2-nonzero",
        relation_type="identity/nonzero-Z2-decoration",
        component_lineage={"cp2_h": "cp2_h"},
        component_lineage_status="identity component lineage placeholder",
        basis_map_status="1x1 identity placeholder; not a Kirby proof",
    ),
    PresentationPairSpec(
        pair_id="component-order-unlink-z2-mixed-dry-run",
        left_case_id="unlink-two-component-z2-mixed",
        right_case_id="unlink-two-component-z2-mixed",
        relation_type="component-order-placeholder",
        component_lineage={"u1": "u2", "u2": "u1"},
        component_lineage_status=(
            "recorded swap-shaped lineage for downstream field coverage only; "
            "the right fixture is not a transformed diagram"
        ),
        basis_map_status=(
            "swap-shaped placeholder; no component-order operation has been "
            "applied or proved"
        ),
        source_status=(
            "schema/test-safe component-order dry-run; intentionally not a "
            "handle-slide or basis-change certificate"
        ),
    ),
)


def presentation_pair_registry_artifact(
    *,
    pair_specs: Sequence[PresentationPairSpec] = DEFAULT_PAIR_SPECS,
) -> dict[str, object]:
    """Return deterministic n45 presentation-pair dry-run metadata."""

    n24 = ordinary_surgery_gate_certificate()
    suite = many_case_candidate_validation_suite_artifact()
    cases_by_id = {str(case["case_id"]): case for case in suite["cases"]}  # type: ignore[index]
    pairs = [
        _pair_artifact(spec, cases_by_id=cases_by_id)
        for spec in sorted(pair_specs, key=lambda item: item.pair_id)
    ]

    artifact: dict[str, object] = {
        "schema": PRESENTATION_PAIR_REGISTRY_SCHEMA,
        "status": "pass",
        "node_id": "n45-kirby-presentation-pair-generator",
        "claim_level": CLAIM_LEVEL,
        "source_status": SOURCE_STATUS,
        "ordinary_surgery_gate_status": n24["status"],
        "ordinary_surgery_gate_status_explanation": (
            "n45 records presentation-pair metadata only and inherits the "
            "blocked n24 ordinary surgery gate"
        ),
        "upstream_nodes": [
            "n35-twisted-decorated-core",
            "n36-many-case-candidate-validation-suite",
        ],
        "downstream_consumer_nodes": ["n50-decorated-kirby-move-gate"],
        "pair_count": len(pairs),
        "pairs": pairs,
        "all_pairs_relation_status": RELATION_STATUS,
        "all_pairs_json_stable": all(pair["stable_json_roundtrip"] is True for pair in pairs),
        "all_pairs_exact_json_no_float_markers": all(
            pair["exact_json_no_float_markers"] is True for pair in pairs
        ),
        "proof_claim_allowed": False,
        "presentation_equivalence_claim_allowed": False,
        "decorated_kirby_move_proof_claim_allowed": False,
        "closed_4_manifold_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "does_not_prove": list(DOES_NOT_PROVE),
        "blocked_high_claims": list(BLOCKED_HIGH_CLAIMS),
        "claim_boundary": (
            "passing n45 means deterministic pair metadata exists for n50 dry "
            "runs; it is not evidence of equivalence, invariance, or exotic "
            "distinction"
        ),
        "ledger_note": PRESENTATION_PAIR_NOTE,
    }
    artifact["metadata_validation"] = validate_presentation_pair_registry_metadata(
        artifact
    )
    return artifact


def validate_presentation_pair_registry_metadata(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Check n45 registry metadata without interpreting Kirby moves."""

    required = {
        "claim_level",
        "source_status",
        "ordinary_surgery_gate_status",
        "pair_count",
        "pairs",
        "does_not_prove",
        "blocked_high_claims",
    }
    missing = sorted(field for field in required if field not in artifact)
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "proof_claim_allowed",
            "presentation_equivalence_claim_allowed",
            "decorated_kirby_move_proof_claim_allowed",
            "closed_4_manifold_claim_allowed",
            "exotic_detection_claim_allowed",
        )
    )
    pairs = artifact.get("pairs", [])
    pair_list_ok = isinstance(pairs, list) and all(
        _pair_metadata_is_valid(pair) for pair in pairs
    )
    does_not_prove = artifact.get("does_not_prove", [])
    does_not_prove_ok = isinstance(does_not_prove, list) and all(
        item in does_not_prove
        for item in (
            "presentation equivalence",
            "Kirby move proof",
            "closed invariant",
            "exotic claims",
        )
    )
    return {
        "valid": (
            not missing
            and artifact.get("claim_level") == CLAIM_LEVEL
            and blocked_claims_ok
            and pair_list_ok
            and does_not_prove_ok
        ),
        "missing_required_fields": missing,
        "blocked_claims_ok": blocked_claims_ok,
        "pair_list_ok": pair_list_ok,
        "does_not_prove_ok": does_not_prove_ok,
        "scope": "presentation-pair dry-run metadata only; no Kirby move proof",
    }


def stable_presentation_pair_registry_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n45 registry artifact deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _pair_artifact(
    spec: PresentationPairSpec,
    *,
    cases_by_id: Mapping[str, Mapping[str, object]],
) -> dict[str, object]:
    left_case = _case_for_id(spec.left_case_id, cases_by_id)
    right_case = _case_for_id(spec.right_case_id, cases_by_id)
    artifact: dict[str, object] = {
        "pair_id": spec.pair_id,
        "left": _side_payload("left", left_case),
        "right": _side_payload("right", right_case),
        "relation_type": spec.relation_type,
        "relation_status": RELATION_STATUS,
        "component_lineage": {
            "status": spec.component_lineage_status,
            "left_to_right": dict(sorted(spec.component_lineage.items())),
        },
        "basis_map": {
            "status": spec.basis_map_status,
            "claim_certified": False,
            "matrix": None,
        },
        "decorated_core_case_refs": [spec.left_case_id, spec.right_case_id],
        "decorated_core_cases": [
            _decorated_case_summary(left_case),
            _decorated_case_summary(right_case),
        ],
        "claim_level": CLAIM_LEVEL,
        "source_status": spec.source_status,
        "does_not_prove": list(DOES_NOT_PROVE),
        "n50_required_fields_present": True,
    }
    stable_json = stable_presentation_pair_registry_json(artifact)
    artifact["stable_json_roundtrip"] = json.loads(stable_json) == artifact
    artifact["exact_json_no_float_markers"] = ".0" not in stable_json
    return artifact


def _side_payload(role: str, case: Mapping[str, object]) -> dict[str, object]:
    return {
        "role": role,
        "fixture_path": case["fixture_path"],
        "diagram_id": case["diagram_id"],
        "decorated_core_case_id": case["case_id"],
        "component_ids": case["diagram_component_ids"],
        "finite_group_id": case["finite_group_id"],
        "decoration_by_component": case["decoration_by_component"],
        "zero_decoration": case["zero_decoration"],
        "component_sector_ids": case["component_sector_ids"],
    }


def _decorated_case_summary(case: Mapping[str, object]) -> dict[str, object]:
    return {
        "case_id": case["case_id"],
        "fixture_path": case["fixture_path"],
        "diagram_id": case["diagram_id"],
        "finite_group_id": case["finite_group_id"],
        "decoration_by_component": case["decoration_by_component"],
        "zero_decoration": case["zero_decoration"],
        "component_sector_ids": case["component_sector_ids"],
        "claim_level": case["claim_level"],
        "source_status": case["source_status"],
        "metadata_validation": case["metadata_validation"],
    }


def _pair_metadata_is_valid(pair: object) -> bool:
    if not isinstance(pair, dict):
        return False
    required = {
        "pair_id",
        "left",
        "right",
        "relation_type",
        "relation_status",
        "component_lineage",
        "basis_map",
        "decorated_core_case_refs",
        "decorated_core_cases",
        "claim_level",
        "source_status",
        "does_not_prove",
    }
    if any(field not in pair for field in required):
        return False
    if pair.get("relation_status") != RELATION_STATUS:
        return False
    if pair.get("claim_level") != CLAIM_LEVEL:
        return False
    does_not_prove = pair.get("does_not_prove")
    return isinstance(does_not_prove, list) and all(
        item in does_not_prove
        for item in (
            "presentation equivalence",
            "Kirby move proof",
            "closed invariant",
            "exotic claims",
        )
    )


def _case_for_id(
    case_id: str,
    cases_by_id: Mapping[str, Mapping[str, object]],
) -> Mapping[str, object]:
    try:
        return cases_by_id[case_id]
    except KeyError as exc:
        raise ValueError(f"unknown decorated-core case id: {case_id}") from exc


__all__ = [
    "BLOCKED_HIGH_CLAIMS",
    "CLAIM_LEVEL",
    "DEFAULT_PAIR_SPECS",
    "DOES_NOT_PROVE",
    "PRESENTATION_PAIR_REGISTRY_SCHEMA",
    "PresentationPairSpec",
    "presentation_pair_registry_artifact",
    "stable_presentation_pair_registry_json",
    "validate_presentation_pair_registry_metadata",
]
