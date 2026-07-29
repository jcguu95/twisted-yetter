from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/frozen-semantic-conformance-gate-v1.json"
)
INDEPENDENT = (
    ROOT / "lean/TwistedYetter/Kirby/Final/Semantics/Independent"
)
GATE_SOURCE = (
    ROOT
    / "lean/TwistedYetter/Kirby/Final/Semantics/"
    "CompleteSemanticConformance.lean"
)
CURRENT_EVALUATOR = (
    ROOT / "lean/TwistedYetter/Kirby/RoleAwarePremodularEvaluator.lean"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def test_gate_is_fail_closed_until_a_complete_certificate_exists() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == (
        "BLOCKED_CURRENT_IMPLEMENTATION_NOT_YET_ADMITTED"
    )
    assert artifact["root_blocker"]["id"] == (
        "PRIMAL_DUAL_HOMOLOGY_CONVENTION_MISMATCH"
    )
    assert set(artifact["admission"].values()) >= {False}
    assert artifact["admission"]["current_implementation_formally_conforms"] is False
    assert (
        artifact["gate"]["final_evaluator_equality_is_certificate_field"]
        is False
    )
    assert artifact["gate"]["boolean_or_hash_can_create_admission"] is False


def test_frozen_semantic_files_are_byte_identical() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    observed = {
        path.name: hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(INDEPENDENT.glob("*.lean"))
    }
    assert observed == artifact["frozen_semantics_sha256"]


def test_gate_exposes_primitives_and_derives_the_final_equality() -> None:
    gate = GATE_SOURCE.read_text()
    evaluator = CURRENT_EVALUATOR.read_text()
    assert "structure ExactSourceBinding" in gate
    assert "structure MarkingBinding" in gate
    assert "structure AlgebraBinding" in gate
    assert "structure EvaluatorBinding" in gate
    assert "structure FrozenConformanceCertificate" in gate
    assert "abbrev FormalAdmission" in gate
    assert "theorem weightConformance_of_primitive_bindings" in gate
    assert "theorem roleAwareCycleEval_eq_frozenEvaluateCycle" in gate
    assert "theorem sound" in gate
    assert "roleAwareRawNumerator_eq_sum_roleAwareSummand" in evaluator
    assert "sorry" not in gate
    assert re.search(r"\badmit\b", gate) is None


def test_known_primal_dual_regression_remains_visible() -> None:
    regression = (
        ROOT
        / "lean/TwistedYetter/Kirby/CycleRepresentativeCounterexample.lean"
    ).read_text()
    assert "theorem no_naive_representative_descent" in regression
    assert "wrong adapter" in regression
