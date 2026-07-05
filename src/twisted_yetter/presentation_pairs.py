"""Deterministic Kirby presentation-pair fixture registry for n45.

This module records toy presentation-pair metadata for later decorated Kirby
move gates.  It deliberately keeps separate trust levels:

* diagram/decorated-core pairs are registry metadata only;
* matrix-level pairs may certify a GL(n,Z) basis change of the recorded
  intersection form;
* no entry certifies a link-diagram Kirby move, closed 4-manifold invariant, or
  exotic-smooth claim.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Final, Mapping, Sequence

from twisted_yetter.artifacts import (
    default_tool_versions,
    dumps_certificate,
    git_metadata,
    hash_json,
    make_certificate,
)
from twisted_yetter.candidate_validation_suite import (
    many_case_candidate_validation_suite_artifact,
)
from twisted_yetter.legacy_prose import legacy_prose_member_ref
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate
from twisted_yetter.presentation_moves import (
    PresentationPair,
    small_presentation_pairs,
)

PRESENTATION_PAIR_REGISTRY_SCHEMA: Final = (
    "twisted-yetter.kirby-presentation-pair-registry.v2"
)
PRESENTATION_PAIR_NOTE: Final = (
    legacy_prose_member_ref(
        "wiki/understandings/kirby-presentation-pair-generator.org"
    )
)
PRESENTATION_PAIR_ARTIFACT: Final = (
    "experiments/results/presentation-pairs/n45-presentation-pair-generator.json"
)

CLAIM_LEVEL: Final = "computed evidence scaffold"
SOURCE_STATUS: Final = (
    "n45 deterministic Kirby/link presentation-pair registry; diagram pairs are "
    "candidate metadata, while matrix pairs certify only recorded GL(n,Z) "
    "basis changes"
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

PAIR_KIND_CLAIM_BOUNDARIES: Final[dict[str, str]] = {
    "diagram-equivalence-toy-pair": (
        "toy diagram/decorated-core pair metadata only; not a certified Kirby "
        "diagram move or closed 4-manifold equivalence"
    ),
    "presentation-sanity-pair": (
        "same-fixture presentation sanity metadata only; useful for plumbing "
        "downstream comparisons but not a closed invariant claim"
    ),
    "component-relabel-dry-run": (
        "component lineage/relabel shape metadata only; the right side is not "
        "a generated transformed diagram"
    ),
    "matrix-basis-change-pair": (
        "machine-checkable matrix-level GL(n,Z) basis-change fixture only; not "
        "a link-diagram handle-slide proof or closed invariant"
    ),
}


@dataclass(frozen=True)
class PresentationPairSpec:
    """A fixed n45 dry-run pair assembled from n36 case summaries."""

    pair_id: str
    left_case_id: str
    right_case_id: str
    pair_kind: str
    relation_type: str
    component_lineage: Mapping[str, str]
    move_metadata: Mapping[str, object]
    component_lineage_status: str = DEFAULT_LINEAGE_STATUS
    basis_map_status: str = DEFAULT_BASIS_MAP_STATUS
    source_status: str = "schema/test-safe dry-run fixture metadata"


DEFAULT_PAIR_SPECS: Final[tuple[PresentationPairSpec, ...]] = (
    PresentationPairSpec(
        pair_id="identity-s4-trivial-zero",
        left_case_id="s4-trivial-zero",
        right_case_id="s4-trivial-zero",
        pair_kind="presentation-sanity-pair",
        relation_type="identity",
        component_lineage={},
        move_metadata={"move_class": "identity", "operation_count": 0},
        component_lineage_status=(
            "identity on the empty component set; still not a closed invariant claim"
        ),
        basis_map_status="empty identity placeholder; no H2 marking is certified",
    ),
    PresentationPairSpec(
        pair_id="identity-cp2-z2-zero",
        left_case_id="cp2-z2-zero",
        right_case_id="cp2-z2-zero",
        pair_kind="presentation-sanity-pair",
        relation_type="identity/zero-decoration",
        component_lineage={"cp2_h": "cp2_h"},
        move_metadata={"move_class": "identity", "operation_count": 0},
        component_lineage_status="identity component lineage placeholder",
        basis_map_status="1x1 identity placeholder; not a Kirby proof",
    ),
    PresentationPairSpec(
        pair_id="identity-cp2-z2-nonzero",
        left_case_id="cp2-z2-nonzero",
        right_case_id="cp2-z2-nonzero",
        pair_kind="presentation-sanity-pair",
        relation_type="identity/nonzero-Z2-decoration",
        component_lineage={"cp2_h": "cp2_h"},
        move_metadata={"move_class": "identity", "operation_count": 0},
        component_lineage_status="identity component lineage placeholder",
        basis_map_status="1x1 identity placeholder; not a Kirby proof",
    ),
    PresentationPairSpec(
        pair_id="component-order-unlink-z2-mixed-dry-run",
        left_case_id="unlink-two-component-z2-mixed",
        right_case_id="unlink-two-component-z2-mixed",
        pair_kind="component-relabel-dry-run",
        relation_type="component-order-placeholder",
        component_lineage={"u1": "u2", "u2": "u1"},
        move_metadata={
            "move_class": "component-order-placeholder",
            "operation_count": 0,
            "lineage_shape": "swap",
        },
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
    PresentationPairSpec(
        pair_id="component-relabel-s2xs2-hopf-z2-mixed-swap-dry-run",
        left_case_id="s2xs2-hopf-z2-mixed-10",
        right_case_id="s2xs2-hopf-z2-mixed-01",
        pair_kind="component-relabel-dry-run",
        relation_type="component-relabel-placeholder",
        component_lineage={"s2_a": "s2_b", "s2_b": "s2_a"},
        move_metadata={
            "move_class": "component-relabel-placeholder",
            "operation_count": 0,
            "lineage_shape": "swap",
            "decoration_shape": "Z/2 labels exchanged across component names",
        },
        component_lineage_status=(
            "recorded swap-shaped lineage between two existing n36 cases; no "
            "diagram relabel operation is generated or certified"
        ),
        basis_map_status=(
            "swap-shaped placeholder; no H2 marking, GL(n,Z), or diagram "
            "operation is certified"
        ),
        source_status=(
            "schema/test-safe relabel dry-run across two n36 Hopf cases; not "
            "a handle-slide, closed-equivalence, or exotic certificate"
        ),
    ),
)


def presentation_pair_registry_artifact(
    *,
    pair_specs: Sequence[PresentationPairSpec] = DEFAULT_PAIR_SPECS,
    matrix_pairs: Sequence[PresentationPair] = small_presentation_pairs(),
) -> dict[str, object]:
    """Return deterministic n45 presentation-pair registry metadata."""

    n24 = ordinary_surgery_gate_certificate()
    suite = many_case_candidate_validation_suite_artifact()
    cases_by_id = {str(case["case_id"]): case for case in suite["cases"]}  # type: ignore[index]
    pairs = [
        _pair_artifact(spec, cases_by_id=cases_by_id)
        for spec in sorted(pair_specs, key=lambda item: item.pair_id)
    ]
    matrix_pair_payloads = [
        _matrix_pair_artifact(pair)
        for pair in sorted(matrix_pairs, key=lambda item: item.name)
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
        "diagram_pair_count": len(pairs),
        "matrix_pair_count": len(matrix_pair_payloads),
        "pairs": pairs,
        "matrix_presentation_pairs": matrix_pair_payloads,
        "pair_kinds": sorted(
            {str(pair["pair_kind"]) for pair in pairs}
            | {str(pair["pair_kind"]) for pair in matrix_pair_payloads}
        ),
        "all_pairs_relation_status": RELATION_STATUS,
        "all_pairs_json_stable": all(pair["stable_json_roundtrip"] is True for pair in pairs),
        "all_pairs_exact_json_no_float_markers": all(
            pair["exact_json_no_float_markers"] is True for pair in pairs
        ),
        "all_matrix_pairs_machine_checked": all(
            pair["machine_checked_matrix_equivalence"] is True
            for pair in matrix_pair_payloads
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


def presentation_pair_registry_artifact_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible artifact envelope for the n45 registry."""

    root = Path(repo_root)
    exact_output = presentation_pair_registry_artifact()
    return make_certificate(
        status="pass",
        command=(
            "PYTHONPATH=src uv run python -m twisted_yetter.presentation_pairs "
            f"--write {PRESENTATION_PAIR_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.presentation_pairs",
            "--write",
            PRESENTATION_PAIR_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": "n45-kirby-presentation-pair-generator",
                "pair_specs": [
                    {
                        "pair_id": spec.pair_id,
                        "left_case_id": spec.left_case_id,
                        "right_case_id": spec.right_case_id,
                        "pair_kind": spec.pair_kind,
                        "relation_type": spec.relation_type,
                        "component_lineage": dict(sorted(spec.component_lineage.items())),
                    }
                    for spec in DEFAULT_PAIR_SPECS
                ],
                "matrix_pairs": [pair.name for pair in small_presentation_pairs()],
                "ordinary_surgery_gate_status": "blocked",
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/presentation_pairs.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m twisted_yetter.presentation_pairs "
            "--write experiments/results/presentation-pairs/"
            "n45-presentation-pair-generator.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n45 records deterministic presentation-pair fixture metadata for n50.",
            "Diagram/decorated-core pairs are candidate dry-run metadata only.",
            "Matrix pairs certify only GL(n,Z) matrix-level basis changes, not link-diagram Kirby moves.",
            "ordinary_surgery_gate_status remains blocked; no closed invariant or exotic claim is made.",
        ],
    )


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
        "matrix_presentation_pairs",
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
    matrix_pairs = artifact.get("matrix_presentation_pairs", [])
    matrix_pair_list_ok = isinstance(matrix_pairs, list) and all(
        _matrix_pair_metadata_is_valid(pair) for pair in matrix_pairs
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
            and matrix_pair_list_ok
            and does_not_prove_ok
        ),
        "missing_required_fields": missing,
        "blocked_claims_ok": blocked_claims_ok,
        "pair_list_ok": pair_list_ok,
        "matrix_pair_list_ok": matrix_pair_list_ok,
        "does_not_prove_ok": does_not_prove_ok,
        "scope": (
            "presentation-pair registry metadata plus matrix-level basis-change "
            "fixtures only; no link-diagram Kirby move proof"
        ),
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
        "pair_kind": spec.pair_kind,
        "relation_type": spec.relation_type,
        "relation_status": RELATION_STATUS,
        "component_lineage": {
            "status": spec.component_lineage_status,
            "left_to_right": dict(sorted(spec.component_lineage.items())),
        },
        "move_metadata": dict(sorted(spec.move_metadata.items())),
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
        "claim_boundary": PAIR_KIND_CLAIM_BOUNDARIES[spec.pair_kind],
        "source_status": spec.source_status,
        "does_not_prove": list(DOES_NOT_PROVE),
        "n50_required_fields_present": True,
    }
    stable_json = stable_presentation_pair_registry_json(artifact)
    artifact["stable_json_roundtrip"] = json.loads(stable_json) == artifact
    artifact["exact_json_no_float_markers"] = ".0" not in stable_json
    return artifact


def _matrix_pair_artifact(pair: PresentationPair) -> dict[str, object]:
    pair.assert_valid()
    artifact: dict[str, object] = {
        "pair_id": pair.name,
        "pair_kind": "matrix-basis-change-pair",
        "relation_type": pair.metadata.get("move", "basis change"),
        "relation_status": "matrix-level-certified",
        "source": _matrix_side_payload(pair.source),
        "target": _matrix_side_payload(pair.target),
        "component_lineage": {
            "status": "component ids recorded from source to target matrix bases",
            "left_to_right": {
                source_id: target_id
                for source_id, target_id in zip(
                    pair.source.component_ids,
                    pair.target.component_ids,
                    strict=True,
                )
            },
        },
        "basis_map": {
            "status": "exact GL(n,Z) basis matrix for matrix presentation only",
            "claim_certified": True,
            "matrix": _rows_to_lists(pair.basis_matrix),
            "inverse_matrix": _rows_to_lists(pair.inverse_basis_matrix),
            "determinant_abs": 1,
        },
        "decoration_transform_mod2": _rows_to_lists(pair.decoration_transform_mod2),
        "transformed_decorations_mod2": _rows_to_lists(
            pair.transformed_decorations_mod2()
        ),
        "metadata": dict(sorted(pair.metadata.items())),
        "machine_checked_matrix_equivalence": True,
        "claim_level": CLAIM_LEVEL,
        "claim_boundary": PAIR_KIND_CLAIM_BOUNDARIES["matrix-basis-change-pair"],
        "source_status": (
            "presentation_moves.py matrix-level GL(n,Z) fixture; not a "
            "machine-readable link-diagram move"
        ),
        "does_not_prove": list(DOES_NOT_PROVE),
    }
    stable_json = stable_presentation_pair_registry_json(artifact)
    artifact["stable_json_roundtrip"] = json.loads(stable_json) == artifact
    artifact["exact_json_no_float_markers"] = ".0" not in stable_json
    return artifact


def _matrix_side_payload(presentation: object) -> dict[str, object]:
    return {
        "matrix": _rows_to_lists(presentation.matrix),  # type: ignore[attr-defined]
        "component_ids": list(presentation.component_ids),  # type: ignore[attr-defined]
        "decorations_mod2": _rows_to_lists(presentation.decorations_mod2),  # type: ignore[attr-defined]
        "rank": presentation.rank,  # type: ignore[attr-defined]
        "determinant": presentation.determinant,  # type: ignore[attr-defined]
        "signature_triple": list(presentation.signature_triple),  # type: ignore[attr-defined]
        "parity": presentation.parity,  # type: ignore[attr-defined]
    }


def _rows_to_lists(rows: Sequence[Sequence[int]]) -> list[list[int]]:
    return [list(row) for row in rows]


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
        "pair_kind",
        "move_metadata",
        "claim_boundary",
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


def _matrix_pair_metadata_is_valid(pair: object) -> bool:
    if not isinstance(pair, dict):
        return False
    required = {
        "pair_id",
        "pair_kind",
        "relation_type",
        "relation_status",
        "source",
        "target",
        "component_lineage",
        "basis_map",
        "decoration_transform_mod2",
        "machine_checked_matrix_equivalence",
        "claim_boundary",
        "does_not_prove",
    }
    if any(field not in pair for field in required):
        return False
    basis_map = pair.get("basis_map")
    return (
        pair.get("pair_kind") == "matrix-basis-change-pair"
        and pair.get("relation_status") == "matrix-level-certified"
        and pair.get("machine_checked_matrix_equivalence") is True
        and isinstance(basis_map, dict)
        and basis_map.get("claim_certified") is True
    )


def _case_for_id(
    case_id: str,
    cases_by_id: Mapping[str, Mapping[str, object]],
) -> Mapping[str, object]:
    try:
        return cases_by_id[case_id]
    except KeyError as exc:
        raise ValueError(f"unknown decorated-core case id: {case_id}") from exc


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Emit the n45 Kirby presentation-pair registry artifact."
    )
    parser.add_argument("--write", type=Path, help="write certificate JSON to this path")
    args = parser.parse_args(argv)

    certificate = presentation_pair_registry_artifact_certificate()
    encoded = dumps_certificate(certificate)
    if args.write is None:
        print(encoded, end="")
        return 0

    args.write.parent.mkdir(parents=True, exist_ok=True)
    args.write.write_text(encoded)
    return 0


__all__ = [
    "BLOCKED_HIGH_CLAIMS",
    "CLAIM_LEVEL",
    "DEFAULT_PAIR_SPECS",
    "DOES_NOT_PROVE",
    "PAIR_KIND_CLAIM_BOUNDARIES",
    "PRESENTATION_PAIR_ARTIFACT",
    "PRESENTATION_PAIR_REGISTRY_SCHEMA",
    "PresentationPairSpec",
    "presentation_pair_registry_artifact_certificate",
    "presentation_pair_registry_artifact",
    "stable_presentation_pair_registry_json",
    "validate_presentation_pair_registry_metadata",
]


if __name__ == "__main__":
    raise SystemExit(main())
