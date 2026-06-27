"""Candidate finite-A Omega_a coefficient metadata.

This n33 module implements only the experimental coefficient scaffold

    Omega_a = sum_i d_i lambda_i(a) X_i

for the currently supported finite character data: the trivial group and Z/2.
It produces deterministic exact metadata certificates.  It is not a theorem,
not a link evaluator, not a decorated Kirby formula, and not a closed
4-manifold invariant calculator.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Final, Mapping

from twisted_yetter.artifacts import (
    default_tool_versions,
    dumps_certificate,
    git_metadata,
    hash_json,
    make_certificate,
)
from twisted_yetter.finite_groups import (
    TRIVIAL_GROUP,
    Z2_GROUP,
    CharacterLabel,
    FiniteAbelianGroup,
    GroupElement,
    certificate_payload as finite_group_certificate_payload,
    character_value,
    validate_character_table,
)
from twisted_yetter.omega_a_contract import (
    OMEGA_A_CANDIDATE_FORMULA_ID,
    validate_omega_a_candidate_artifact_metadata,
)
from twisted_yetter.ordinary_kirby_color import (
    KIRBY_COLOR_CONVENTION,
    omega_coefficients,
)
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate
from twisted_yetter.su2_level2 import SIMPLE_LABELS

OMEGA_A_SCHEMA: Final = "twisted-yetter.omega-a-candidate-coefficients.v1"
OMEGA_A_IMPLEMENTATION_NOTE: Final = (
    "wiki/understandings/omega-a-implementation.org"
)
OMEGA_A_ARTIFACT: Final = (
    "experiments/results/omega-a-candidate/n33-candidate-coefficients.json"
)
CLAIM_LEVEL: Final = "candidate-experimental"
SOURCE_STATUS: Final = "candidate-experimental / NOT PROVED IN REPO / SOURCE NEEDED"
CATEGORY_ID: Final = "SU(2)_2-local-certificate"

CHARACTER_TABLE_SOURCES: Final[dict[tuple[int, ...], str]] = {
    (): "twisted_yetter.finite_groups:TRIVIAL_GROUP",
    (2,): "twisted_yetter.finite_groups:Z2_GROUP",
}

LABEL_CHARACTER_ASSIGNMENT_SOURCE_STATUS: Final = (
    "candidate/local assignment; not sourced as a Yetter theorem"
)

DEFAULT_Z2_LABEL_CHARACTER_ASSIGNMENT: Final[dict[str, CharacterLabel]] = {
    "0": (0,),
    "1": (1,),
    "2": (0,),
}

BLOCKED_HIGH_CLAIMS: Final = (
    "decorated/twisted formula theorem",
    "claim-supporting closed 4D invariant",
    "exotic detection claim",
    "Reutter escape/no-go conclusion",
)

DOES_NOT_COMPUTE: Final = (
    "colored framed link evaluation",
    "Kirby color sum over diagrams",
    "decorated Kirby move proof",
    "closed 4-manifold invariant",
    "exotic smooth-structure detection evidence",
)


def omega_a_candidate_certificate(
    group: FiniteAbelianGroup,
    *,
    label_character_assignment: Mapping[str, CharacterLabel] | None = None,
) -> dict[str, object]:
    """Return deterministic exact candidate coefficient metadata for a group.

    The result contains one sector for each group element ``a``.  Coefficients
    are the exact products ``d_i * lambda_i(a)`` where ``d_i`` are the current
    experimental ordinary omega coefficients for SU(2)_2.
    """

    validate_character_table(group)
    if group not in (TRIVIAL_GROUP, Z2_GROUP):
        raise ValueError(f"unsupported n33 finite group: {group.name}")

    assignment = _normalized_assignment(group, label_character_assignment)
    n24 = ordinary_surgery_gate_certificate()
    artifact: dict[str, object] = {
        "schema": OMEGA_A_SCHEMA,
        "status": "pass",
        "node_id": "n33-omega-a-implementation",
        "claim_level": CLAIM_LEVEL,
        "source_status": SOURCE_STATUS,
        "candidate_formula_id": OMEGA_A_CANDIDATE_FORMULA_ID,
        "candidate_formula_display": "Omega_a = sum_i d_i lambda_i(a) X_i",
        "finite_group_id": _finite_group_id(group),
        "character_table_source": _character_table_source(group),
        "character_data_source_status": (
            "exact finite character table inherited from n11; "
            "label-to-character assignment remains candidate/local"
        ),
        "character_table_certificate": finite_group_certificate_payload(group),
        "character_orthogonality_status": "pass/exact inherited from n11",
        "marking_basis_status": (
            "not-in-scope: coefficient-sector metadata only; no H2 basis, "
            "basis-change action, or closed marking comparison is computed"
        ),
        "category_id": CATEGORY_ID,
        "simple_labels": list(SIMPLE_LABELS),
        "ordinary_kirby_color_convention": KIRBY_COLOR_CONVENTION,
        "ordinary_omega_coefficients": {
            label: omega_coefficients()[label].to_jsonable()
            for label in SIMPLE_LABELS
        },
        "label_character_assignment": _assignment_payload(group, assignment),
        "ordinary_surgery_gate_status": n24["status"],
        "ordinary_surgery_gate_status_explanation": (
            "n33 is coefficient metadata only and inherits the blocked n24 "
            "ordinary surgery gate; no closed invariant claim is allowed"
        ),
        "closed_4_manifold_claim_allowed": False,
        "theorem_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "sectors": [
            _sector_payload(group, element, assignment)
            for element in group.elements
        ],
        "does_not_compute": list(DOES_NOT_COMPUTE),
        "blocked_high_claims": list(BLOCKED_HIGH_CLAIMS),
        "ledger_note": OMEGA_A_IMPLEMENTATION_NOTE,
    }
    artifact["metadata_validation"] = validate_omega_a_candidate_artifact_metadata(
        artifact
    )
    return artifact


def stable_omega_a_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n33 candidate coefficient certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def omega_a_candidate_artifact_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible artifact envelope for supported n33 data."""

    root = Path(repo_root)
    exact_output = {
        "schema": "twisted-yetter.omega-a-candidate-artifact-bundle.v1",
        "status": "pass",
        "node_id": "n33-omega-a-implementation",
        "claim_level": CLAIM_LEVEL,
        "source_status": SOURCE_STATUS,
        "candidate_formula_id": OMEGA_A_CANDIDATE_FORMULA_ID,
        "ordinary_surgery_gate_status": "blocked",
        "groups": {
            "trivial": omega_a_candidate_certificate(TRIVIAL_GROUP),
            "Z/2": omega_a_candidate_certificate(Z2_GROUP),
        },
        "claim_boundary": (
            "candidate coefficient scaffold only; no decorated Kirby/link "
            "values, no closed invariant, no exotic comparison, and no "
            "Reutter conclusion"
        ),
    }
    return make_certificate(
        status="pass",
        command=(
            "PYTHONPATH=src uv run python -m twisted_yetter.omega_a "
            f"--write {OMEGA_A_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.omega_a",
            "--write",
            OMEGA_A_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": "n33-omega-a-implementation",
                "formula_id": OMEGA_A_CANDIDATE_FORMULA_ID,
                "supported_groups": ["trivial", "Z/2"],
                "z2_assignment": DEFAULT_Z2_LABEL_CHARACTER_ASSIGNMENT,
                "ordinary_surgery_gate_status": "blocked",
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/omega_a.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m twisted_yetter.omega_a "
            "--write experiments/results/omega-a-candidate/n33-candidate-coefficients.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n33 is candidate coefficient metadata only.",
            "ordinary_surgery_gate_status remains blocked; no closed 4D invariant claim is made.",
        ],
    )


def _normalized_assignment(
    group: FiniteAbelianGroup,
    label_character_assignment: Mapping[str, CharacterLabel] | None,
) -> dict[str, CharacterLabel]:
    if label_character_assignment is None:
        if group == TRIVIAL_GROUP:
            label_character_assignment = {label: () for label in SIMPLE_LABELS}
        elif group == Z2_GROUP:
            label_character_assignment = DEFAULT_Z2_LABEL_CHARACTER_ASSIGNMENT

    if label_character_assignment is None:
        raise ValueError(f"missing label-to-character assignment for {group.name}")

    assignment = {
        label: tuple(label_character_assignment[label])
        for label in SIMPLE_LABELS
    }
    if set(assignment) != set(SIMPLE_LABELS):
        raise ValueError("label-to-character assignment must cover all simple labels")
    for character in assignment.values():
        if character not in group.characters:
            raise ValueError(
                f"label-to-character assignment uses unknown character {character!r}"
            )
    return assignment


def _sector_payload(
    group: FiniteAbelianGroup,
    element: GroupElement,
    assignment: Mapping[str, CharacterLabel],
) -> dict[str, object]:
    return {
        "sector_id": _element_label(element),
        "element": _coordinates_payload(element),
        "coefficients": [
            _coefficient_payload(group, element, label, assignment[label])
            for label in SIMPLE_LABELS
        ],
    }


def _coefficient_payload(
    group: FiniteAbelianGroup,
    element: GroupElement,
    label: str,
    character: CharacterLabel,
) -> dict[str, object]:
    ordinary_coefficient = omega_coefficients()[label]
    exact_character_value = character_value(group, character, element)
    candidate_coefficient = ordinary_coefficient * exact_character_value
    return {
        "label": label,
        "ordinary_dimension_coefficient": ordinary_coefficient.to_jsonable(),
        "character_label": _character_label(character),
        "character_value": _exact_integer_payload(exact_character_value),
        "candidate_coefficient": candidate_coefficient.to_jsonable(),
        "coefficient_formula": "d_i * lambda_i(a)",
    }


def _assignment_payload(
    group: FiniteAbelianGroup,
    assignment: Mapping[str, CharacterLabel],
) -> dict[str, object]:
    return {
        "status": "candidate/local",
        "source_status": LABEL_CHARACTER_ASSIGNMENT_SOURCE_STATUS,
        "finite_group_id": _finite_group_id(group),
        "assignment": {
            label: _character_label(assignment[label]) for label in SIMPLE_LABELS
        },
        "interpretation": (
            "For Z/2 this local scaffold assigns the middle SU(2)_2 label 1 "
            "to the sign character and labels 0,2 to the trivial character; "
            "this realizes the sign-weighted theta-style target only as a "
            "candidate/local convention."
        ),
    }


def _finite_group_id(group: FiniteAbelianGroup) -> str:
    if group == TRIVIAL_GROUP:
        return "trivial"
    if group == Z2_GROUP:
        return "Z/2"
    raise ValueError(f"unsupported n33 finite group: {group.name}")


def _character_table_source(group: FiniteAbelianGroup) -> str:
    try:
        return CHARACTER_TABLE_SOURCES[group.invariant_factors]
    except KeyError as exc:
        raise ValueError(f"unsupported n33 finite group: {group.name}") from exc


def _coordinates_payload(coordinates: tuple[int, ...]) -> list[int]:
    return list(coordinates)


def _element_label(element: GroupElement) -> str:
    if element == ():
        return "e"
    return ",".join(str(coordinate) for coordinate in element)


def _character_label(character: CharacterLabel) -> str:
    if character == ():
        return "trivial"
    if all(coordinate == 0 for coordinate in character):
        return "chi_0"
    return "chi_" + "_".join(str(coordinate) for coordinate in character)


def _exact_integer_payload(value: object) -> dict[str, str]:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError("current n33 character values must be exact integers")
    return {"type": "integer", "value": str(value)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Emit the n33 candidate Omega_a coefficient artifact."
    )
    parser.add_argument("--write", type=Path, help="write certificate JSON to this path")
    args = parser.parse_args(argv)

    certificate = omega_a_candidate_artifact_certificate()
    encoded = dumps_certificate(certificate)
    if args.write is None:
        print(encoded, end="")
        return 0

    args.write.parent.mkdir(parents=True, exist_ok=True)
    args.write.write_text(encoded)
    return 0


__all__ = [
    "BLOCKED_HIGH_CLAIMS",
    "CATEGORY_ID",
    "CLAIM_LEVEL",
    "DEFAULT_Z2_LABEL_CHARACTER_ASSIGNMENT",
    "DOES_NOT_COMPUTE",
    "LABEL_CHARACTER_ASSIGNMENT_SOURCE_STATUS",
    "OMEGA_A_ARTIFACT",
    "OMEGA_A_IMPLEMENTATION_NOTE",
    "OMEGA_A_SCHEMA",
    "SOURCE_STATUS",
    "omega_a_candidate_artifact_certificate",
    "omega_a_candidate_certificate",
    "stable_omega_a_json",
]


if __name__ == "__main__":
    raise SystemExit(main())
