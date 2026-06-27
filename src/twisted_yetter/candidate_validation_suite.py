"""Many-case candidate validation suite scaffold for n36.

This module builds deterministic summaries of decorated-core input artifacts
over several toy diagrams and Z/2 decoration cases.  It is metadata validation
only: no link evaluation, no Kirby sum, no decorated Kirby-move proof, no
closed invariant, and no exotic-smooth claim.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Final, Mapping, Sequence

from twisted_yetter.decorated_core import (
    decorated_core_input_artifact,
    stable_decorated_core_json,
    validate_decorated_core_artifact_metadata,
)
from twisted_yetter.finite_groups import TRIVIAL_GROUP, Z2_GROUP, FiniteAbelianGroup
from twisted_yetter.link_diagram import LinkDiagram
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate

CANDIDATE_VALIDATION_SUITE_SCHEMA: Final = (
    "twisted-yetter.many-case-candidate-validation-suite.v1"
)
CANDIDATE_VALIDATION_SUITE_NOTE: Final = (
    "wiki/understandings/many-case-candidate-validation-suite.org"
)

CLAIM_LEVEL: Final = "computed evidence scaffold"
SOURCE_STATUS: Final = (
    "n36 deterministic decorated-core metadata validation suite; consumes n35 "
    "artifacts and remains candidate/computed evidence only"
)

DEFAULT_TOY_FIXTURE_DIR: Final = Path("experiments/inputs/toy-diagrams")
DEFAULT_BASIS_ID: Final = "toy-kirby-component-order"
DEFAULT_BASIS_STATUS: Final = "Kirby component order only"
DEFAULT_BASIS_SOURCE_STATUS: Final = "schema-test-safe / not certified H2 marking"

DOES_NOT_COMPUTE: Final = (
    "link evaluation",
    "Kirby color sum",
    "decorated Kirby move proof",
    "closed invariant",
    "exotic detection",
)

BLOCKED_HIGH_CLAIMS: Final = (
    "decorated/twisted formula theorem",
    "claim-supporting closed 4D invariant",
    "exotic detection claim",
    "Reutter escape/no-go conclusion",
)


@dataclass(frozen=True)
class CandidateValidationCaseSpec:
    """A fixed toy case for n36 decorated-core metadata validation."""

    case_id: str
    fixture_path: str
    group: FiniteAbelianGroup
    decoration_by_component: Mapping[str, tuple[int, ...]]
    basis_id: str = DEFAULT_BASIS_ID
    basis_status: str = DEFAULT_BASIS_STATUS
    basis_source_status: str = DEFAULT_BASIS_SOURCE_STATUS


DEFAULT_CASE_SPECS: Final[tuple[CandidateValidationCaseSpec, ...]] = (
    CandidateValidationCaseSpec(
        case_id="s4-trivial-zero",
        fixture_path="s4-empty.json",
        group=TRIVIAL_GROUP,
        decoration_by_component={},
    ),
    CandidateValidationCaseSpec(
        case_id="cp2-z2-zero",
        fixture_path="cp2-plus-one-framed-unknot.json",
        group=Z2_GROUP,
        decoration_by_component={"cp2_h": (0,)},
    ),
    CandidateValidationCaseSpec(
        case_id="cp2-z2-nonzero",
        fixture_path="cp2-plus-one-framed-unknot.json",
        group=Z2_GROUP,
        decoration_by_component={"cp2_h": (1,)},
    ),
    CandidateValidationCaseSpec(
        case_id="s2xs2-hopf-z2-mixed-10",
        fixture_path="s2x-s2-hopf-zero-framed.json",
        group=Z2_GROUP,
        decoration_by_component={"s2_a": (1,), "s2_b": (0,)},
    ),
    CandidateValidationCaseSpec(
        case_id="s2xs2-hopf-z2-mixed-01",
        fixture_path="s2x-s2-hopf-zero-framed.json",
        group=Z2_GROUP,
        decoration_by_component={"s2_a": (0,), "s2_b": (1,)},
    ),
    CandidateValidationCaseSpec(
        case_id="unlink-two-component-z2-zero",
        fixture_path="unlink-two-component.json",
        group=Z2_GROUP,
        decoration_by_component={"u1": (0,), "u2": (0,)},
    ),
    CandidateValidationCaseSpec(
        case_id="unlink-two-component-z2-mixed",
        fixture_path="unlink-two-component.json",
        group=Z2_GROUP,
        decoration_by_component={"u1": (1,), "u2": (0,)},
    ),
    CandidateValidationCaseSpec(
        case_id="unlink-two-component-z2-nonzero",
        fixture_path="unlink-two-component.json",
        group=Z2_GROUP,
        decoration_by_component={"u1": (1,), "u2": (1,)},
    ),
)


def many_case_candidate_validation_suite_artifact(
    *,
    fixture_dir: Path = DEFAULT_TOY_FIXTURE_DIR,
    case_specs: Sequence[CandidateValidationCaseSpec] = DEFAULT_CASE_SPECS,
) -> dict[str, object]:
    """Return deterministic n36 validation-suite summary metadata."""

    n24 = ordinary_surgery_gate_certificate()
    cases = [
        _case_summary(spec, fixture_dir=fixture_dir)
        for spec in sorted(case_specs, key=lambda item: item.case_id)
    ]
    artifact: dict[str, object] = {
        "schema": CANDIDATE_VALIDATION_SUITE_SCHEMA,
        "status": "pass",
        "node_id": "n36-many-case-candidate-validation-suite",
        "claim_level": CLAIM_LEVEL,
        "source_status": SOURCE_STATUS,
        "ordinary_surgery_gate_status": n24["status"],
        "ordinary_surgery_gate_status_explanation": (
            "n36 validates deterministic decorated-core metadata only and "
            "inherits the blocked n24 ordinary surgery gate"
        ),
        "upstream_nodes": [
            "n24-ordinary-surgery-gate",
            "n33-omega-a-implementation",
            "n34-h2-label-and-basis-schema",
            "n35-twisted-decorated-core",
        ],
        "case_count": len(cases),
        "cases": cases,
        "all_cases_pass_metadata_validation": all(
            case["metadata_validation"]["valid"] is True for case in cases
        ),
        "all_cases_json_stable": all(case["stable_json_roundtrip"] is True for case in cases),
        "all_cases_exact_json_no_float_markers": all(
            case["exact_json_no_float_markers"] is True for case in cases
        ),
        "proof_claim_allowed": False,
        "closed_4_manifold_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "decorated_kirby_move_proof_claim_allowed": False,
        "does_not_compute": list(DOES_NOT_COMPUTE),
        "blocked_high_claims": list(BLOCKED_HIGH_CLAIMS),
        "claim_boundary": (
            "passing this suite is computed evidence for n35/n33 metadata "
            "consistency only; it is not proof of a formula or invariant"
        ),
        "ledger_note": CANDIDATE_VALIDATION_SUITE_NOTE,
    }
    artifact["metadata_validation"] = validate_candidate_validation_suite_metadata(
        artifact
    )
    return artifact


def validate_candidate_validation_suite_metadata(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Check required n36 suite metadata without interpreting topology."""

    required = {
        "claim_level",
        "source_status",
        "ordinary_surgery_gate_status",
        "case_count",
        "cases",
        "does_not_compute",
        "blocked_high_claims",
    }
    missing = sorted(field for field in required if field not in artifact)
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "proof_claim_allowed",
            "closed_4_manifold_claim_allowed",
            "exotic_detection_claim_allowed",
            "decorated_kirby_move_proof_claim_allowed",
        )
    )
    cases = artifact.get("cases", [])
    case_list_ok = isinstance(cases, list) and all(
        _case_metadata_is_valid(case) for case in cases
    )
    return {
        "valid": (
            not missing
            and artifact.get("claim_level") == CLAIM_LEVEL
            and blocked_claims_ok
            and case_list_ok
        ),
        "missing_required_fields": missing,
        "blocked_claims_ok": blocked_claims_ok,
        "case_list_ok": case_list_ok,
        "scope": "suite metadata validation only; no link evaluation",
    }


def stable_candidate_validation_suite_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n36 validation-suite artifact deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _case_summary(
    spec: CandidateValidationCaseSpec,
    *,
    fixture_dir: Path,
) -> dict[str, object]:
    diagram = _load_fixture(fixture_dir / spec.fixture_path)
    core_artifact = decorated_core_input_artifact(
        diagram,
        spec.group,
        basis_id=spec.basis_id,
        basis_status=spec.basis_status,
        basis_source_status=spec.basis_source_status,
        decoration_by_component=spec.decoration_by_component,
    )
    stable_json = stable_decorated_core_json(core_artifact)
    return {
        "case_id": spec.case_id,
        "fixture_path": str(DEFAULT_TOY_FIXTURE_DIR / spec.fixture_path),
        "diagram_id": core_artifact["diagram_id"],
        "diagram_component_ids": core_artifact["component_ids"],
        "finite_group_id": core_artifact["finite_group_id"],
        "decoration_by_component": core_artifact["decoration_by_component"],
        "zero_decoration": core_artifact["zero_decoration"],
        "component_sector_ids": [
            item["candidate_sector_id"]
            for item in core_artifact["component_sector_metadata"]
        ],
        "component_sector_metadata": [
            {
                "component_id": item["component_id"],
                "decoration_element_id": item["decoration_element_id"],
                "candidate_sector_id": item["candidate_sector_id"],
            }
            for item in core_artifact["component_sector_metadata"]
        ],
        "metadata_validation": validate_decorated_core_artifact_metadata(core_artifact),
        "claim_level": core_artifact["claim_level"],
        "source_status": core_artifact["source_status"],
        "ordinary_surgery_gate_status": core_artifact["ordinary_surgery_gate_status"],
        "stable_json_roundtrip": json.loads(stable_json) == core_artifact,
        "stable_json_sha256": _sha256_hex(stable_json),
        "exact_json_no_float_markers": ".0" not in stable_json,
        "does_not_compute": core_artifact["does_not_compute"],
    }


def _case_metadata_is_valid(case: object) -> bool:
    if not isinstance(case, dict):
        return False
    required = {
        "case_id",
        "fixture_path",
        "diagram_id",
        "finite_group_id",
        "decoration_by_component",
        "zero_decoration",
        "component_sector_ids",
        "metadata_validation",
        "claim_level",
        "source_status",
    }
    if any(field not in case for field in required):
        return False
    metadata_validation = case["metadata_validation"]
    return (
        isinstance(metadata_validation, dict)
        and metadata_validation.get("valid") is True
        and case.get("claim_level") == CLAIM_LEVEL
    )


def _load_fixture(path: Path) -> LinkDiagram:
    payload = json.loads(path.read_text())
    return LinkDiagram.from_json(payload)


def _sha256_hex(payload: str) -> str:
    import hashlib

    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


__all__ = [
    "BLOCKED_HIGH_CLAIMS",
    "CANDIDATE_VALIDATION_SUITE_SCHEMA",
    "CLAIM_LEVEL",
    "DEFAULT_CASE_SPECS",
    "DOES_NOT_COMPUTE",
    "SOURCE_STATUS",
    "CandidateValidationCaseSpec",
    "many_case_candidate_validation_suite_artifact",
    "stable_candidate_validation_suite_json",
    "validate_candidate_validation_suite_metadata",
]
