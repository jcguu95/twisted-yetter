from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "dotted-boundary-h2-descent-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def test_artifact_is_content_addressed_and_kernel_checked() -> None:
    artifact = load_artifact()
    assert artifact["schema"] == (
        "twisted-yetter.dotted-boundary-h2-descent.v1"
    )
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["checks"]["targeted_axiom_audit"]["returncode"] == 0
    assert artifact["checks"]["umbrella_build"]["returncode"] == 0


def test_proof_chain_reaches_actual_h2_and_closed_manifolds() -> None:
    artifact = load_artifact()
    stages = {entry["stage"]: entry for entry in artifact["proved_chain"]}
    assert stages["all_boundaries_actual_h2_descent"]["status"] == "PROVED"
    assert stages["eight_local_kirby_moves"]["status"] == (
        "PROVED_RELATIVE_TO_VISIBLE_INPUTS"
    )
    assert stages["closed_four_manifold_oriented_diffeomorphism"][
        "status"
    ] == "PROVED_RELATIVE_TO_VISIBLE_INPUTS"


def test_retired_global_descent_input_cannot_reappear_silently() -> None:
    artifact = load_artifact()
    guards = artifact["checks"]["source_guards"]
    assert guards["proof_holes"] == []
    assert guards["actual_h2_quotient_descent"] is True
    assert guards["final_theorem_derives_representative_independence"] is True
    assert guards["retired_global_graphical_descent_absent"] is True
    assert artifact["axiom_audit"]["retired_inputs_absent"] == [
        "tham_dualBoundaryGraphicalRealization",
        "baerenzBarrett_labelIndexedSlidingMovies",
        "standardDottedDiskGeometry",
    ]


def test_geometry_population_is_closed_by_named_literature_boundary() -> None:
    artifact = load_artifact()
    remaining = artifact["remaining_topology_side_obligation"]
    assert remaining["status"] == (
        "CLOSED_BY_CERTIFIED_STANDARD_DOTTED_PRESENTATION_DOMAIN"
    )
    assert "presentation domain" in remaining["description"]
    guards = artifact["checks"]["source_guards"]
    assert guards[
        "final_theorem_uses_certified_standard_dotted_domain"
    ] is True
    assert guards[
        "caller_supplied_geometry_absent_from_terminal_surface"
    ] is True
    assert guards["overbroad_global_geometry_axiom_absent"] is True
    nonclaims = "\n".join(artifact["explicit_nonclaims"])
    assert "does not provide an executable parser" in nonclaims
    assert "does not establish the premodular case" in nonclaims


def test_all_input_hashes_are_well_formed() -> None:
    artifact = load_artifact()
    for group in ("source_files", "reference_records"):
        for relative, metadata in artifact["inputs"][group].items():
            assert relative
            assert metadata["bytes"] > 0
            assert len(metadata["sha256"]) == 64
