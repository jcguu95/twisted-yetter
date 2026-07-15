"""Fail-closed gates for low-rank ribbon scan evidence.

This module is deliberately about admission, not computation.  It prevents
mutable aliases, authored readiness flags, incomplete ribbon refinements, and
provisional/formula outputs from becoming formal low-rank scan evidence.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any, Final


FORMAL_ADMISSION_POLICY_SCHEMA: Final = (
    "twisted-yetter.foundation-safety.formal-admission-policy.v1"
)
LOW_RANK_RIBBON_CATALOG_SCHEMA: Final = (
    "twisted-yetter.low-rank-ribbon-realization-catalog.v1"
)
FORMAL_SCAN_READINESS_SCHEMA: Final = (
    "twisted-yetter.low-rank-formal-scan-readiness.v1"
)

FOUNDATION_STATUS: Final = "FOUNDATION_ESTABLISHED"
RIBBON_CATALOG_ESTABLISHED: Final = "LOW_RANK_RIBBON_CLASSIFICATION_ESTABLISHED"
RIBBON_CATALOG_BLOCKED: Final = "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"

EVIDENCE_KIND_ALLOWLIST: Final = (
    "ribbon_realization_snapshot",
    "scan_plan",
    "scan_case_result",
    "scan_aggregate",
)
FORMAL_CLAIM_LEVELS: Final = (
    "formal-low-rank-category-evidence",
    "formal-low-rank-scan-evidence",
)
REJECTED_SOURCE_STATUSES: Final = (
    "formula-preflight",
    "provisional-low-confidence",
    "candidate-experimental",
    "legacy-fr-only",
    "historical-negative-control",
)
TERMINAL_RIBBON_ROW_STATUSES: Final = (
    "RESOLVED_RIBBON_REALIZATION",
    "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE",
)
EXPECTED_MODULAR_BRAIDED_COUNTS: Final = {
    2: 6,
    3: 16,
    4: 33,
    5: 22,
}
FORBIDDEN_AUTHORED_READY_LITERAL: Final = "READY_FOR_SIGNAL_SCAN"


class FoundationSafetyError(ValueError):
    """Raised when an artifact tries to cross a fail-closed boundary."""


def stable_content_hash(value: Any) -> str:
    """Return a content-addressed sha256 identifier for JSON-compatible data."""

    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def add_content_hash(payload: dict[str, Any]) -> dict[str, Any]:
    """Return a shallow copy with ``content_hash`` bound to the other fields."""

    body = dict(payload)
    body.pop("content_hash", None)
    body["content_hash"] = stable_content_hash(body)
    return body


def validate_formal_admission_policy(policy: dict[str, Any]) -> None:
    """Validate the v1 policy that decides formal low-rank evidence admission."""

    _require_schema(policy, FORMAL_ADMISSION_POLICY_SCHEMA)
    _require_equal(policy, "foundation_status", FOUNDATION_STATUS)
    _require_equal(policy, "policy_status", "ACTIVE_FAIL_CLOSED")
    if tuple(policy.get("formal_evidence_kind_allowlist", ())) != EVIDENCE_KIND_ALLOWLIST:
        raise FoundationSafetyError("policy evidence kind allowlist changed")
    flags = _require_object(policy, "policy_flags")
    for field in (
        "derived_readiness_only",
        "mutable_aliases_are_not_formal_evidence",
        "formal_evidence_requires_content_hash",
        "classification_must_be_ribbon_level",
        "formula_preflight_is_not_formal_evidence",
    ):
        if flags.get(field) is not True:
            raise FoundationSafetyError(f"policy flag {field!r} is not enabled")
    required_hashes = _require_object(policy, "required_pinned_hash_fields")
    for kind in EVIDENCE_KIND_ALLOWLIST:
        if kind not in required_hashes or not required_hashes[kind]:
            raise FoundationSafetyError(f"policy lacks required hashes for {kind}")


def validate_formal_evidence(
    evidence: dict[str, Any],
    *,
    policy: dict[str, Any] | None = None,
) -> None:
    """Validate one candidate formal evidence object.

    The caller may pass the policy explicitly.  If omitted, the same hard-coded
    v1 allowlist is used; this keeps tests and small tools deterministic.
    """

    if policy is not None:
        validate_formal_admission_policy(policy)
    _reject_authored_ready(evidence)

    kind = evidence.get("evidence_kind")
    if kind not in EVIDENCE_KIND_ALLOWLIST:
        raise FoundationSafetyError(f"unsupported formal evidence kind: {kind!r}")
    if evidence.get("claim_level") not in FORMAL_CLAIM_LEVELS:
        raise FoundationSafetyError("formal evidence has a non-formal claim level")
    if evidence.get("source_status") in REJECTED_SOURCE_STATUSES:
        raise FoundationSafetyError("rejected source status cannot be formal evidence")
    if evidence.get("mutable_alias_inputs"):
        raise FoundationSafetyError("formal evidence cannot depend on mutable aliases")

    expected_hash = evidence.get("content_hash")
    if not _is_sha256_id(expected_hash):
        raise FoundationSafetyError("formal evidence needs a content_hash")
    body = dict(evidence)
    body.pop("content_hash", None)
    if expected_hash != stable_content_hash(body):
        raise FoundationSafetyError("formal evidence content_hash is stale")

    if kind == "ribbon_realization_snapshot":
        _validate_ribbon_realization_snapshot(evidence)
    elif kind == "scan_plan":
        _validate_scan_plan(evidence)
    elif kind == "scan_case_result":
        _validate_scan_case_result(evidence)
    elif kind == "scan_aggregate":
        _validate_scan_aggregate(evidence)


def validate_low_rank_ribbon_catalog(catalog: dict[str, Any]) -> None:
    """Validate the rank 2-5 ribbon refinement catalog or blocker ledger."""

    _require_schema(catalog, LOW_RANK_RIBBON_CATALOG_SCHEMA)
    status = catalog.get("status")
    if status not in (RIBBON_CATALOG_ESTABLISHED, RIBBON_CATALOG_BLOCKED):
        raise FoundationSafetyError(f"unsupported catalog status: {status!r}")
    coverage = catalog.get("coverage_by_rank")
    if not isinstance(coverage, list):
        raise FoundationSafetyError("catalog coverage_by_rank must be a list")
    counts = {
        int(item["rank"]): int(item["modular_braided_class_count"])
        for item in coverage
    }
    if counts != EXPECTED_MODULAR_BRAIDED_COUNTS:
        raise FoundationSafetyError("catalog braided rank counts changed")
    if catalog.get("ribbon_denominator_copied_from_braided") is not False:
        raise FoundationSafetyError("ribbon denominator must not copy braided counts")

    rows = catalog.get("families")
    if not isinstance(rows, list) or not rows:
        raise FoundationSafetyError("catalog needs nonempty family rows")
    per_rank = {rank: 0 for rank in EXPECTED_MODULAR_BRAIDED_COUNTS}
    blocked = 0
    resolved = 0
    for row in rows:
        _validate_catalog_row(row)
        rank = int(row["rank"])
        per_rank[rank] += int(row["modular_braided_class_count"])
        if row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE":
            blocked += 1
        else:
            resolved += 1
    if per_rank != EXPECTED_MODULAR_BRAIDED_COUNTS:
        raise FoundationSafetyError("catalog family rows do not match braided counts")

    if status == RIBBON_CATALOG_ESTABLISHED:
        if blocked:
            raise FoundationSafetyError("established catalog contains blocked rows")
        if catalog.get("formal_scan_plan_allowed") is not True:
            raise FoundationSafetyError("established catalog must allow scan plans")
        _require_object(catalog, "ribbon_denominator_by_rank")
    else:
        if blocked == 0:
            raise FoundationSafetyError("blocked catalog needs at least one blocker")
        if resolved != 0:
            raise FoundationSafetyError("mixed blocked/resolved v1 catalog is unsupported")
        if catalog.get("formal_scan_plan_allowed") is not False:
            raise FoundationSafetyError("blocked catalog cannot allow scan plans")
        if catalog.get("ribbon_denominator_by_rank") not in ({}, None):
            raise FoundationSafetyError("blocked catalog cannot publish ribbon denominators")


def validate_formal_scan_readiness(
    readiness: dict[str, Any],
    *,
    catalog: dict[str, Any],
) -> None:
    """Validate the aggregate readiness decision for formal scan generation."""

    _require_schema(readiness, FORMAL_SCAN_READINESS_SCHEMA)
    validate_low_rank_ribbon_catalog(catalog)
    _require_equal(readiness, "foundation_status", FOUNDATION_STATUS)
    if catalog["status"] == RIBBON_CATALOG_ESTABLISHED:
        _require_equal(readiness, "status", "READY_TO_GENERATE_FORMAL_SCAN_PLAN")
        if readiness.get("scan_plan_generation_allowed") is not True:
            raise FoundationSafetyError("established catalog must enable scan planning")
    else:
        _require_equal(readiness, "status", "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG")
        if readiness.get("scan_plan_generation_allowed") is not False:
            raise FoundationSafetyError("blocked catalog cannot generate scan plans")
        if readiness.get("formal_scan_plan_id") is not None:
            raise FoundationSafetyError("blocked readiness cannot name a scan plan")


def _validate_catalog_row(row: Any) -> None:
    if not isinstance(row, dict):
        raise FoundationSafetyError("catalog row must be an object")
    for field in (
        "family_id",
        "rank",
        "modular_braided_class_count",
        "fusion_level",
        "braided_level",
        "spherical_level",
        "pivotal_level",
        "ribbon_level",
        "terminal_status",
        "formal_admission_allowed",
    ):
        if field not in row:
            raise FoundationSafetyError(f"catalog row missing {field}")
    if row["terminal_status"] not in TERMINAL_RIBBON_ROW_STATUSES:
        raise FoundationSafetyError("catalog row has non-terminal status")
    rank = int(row["rank"])
    if rank not in EXPECTED_MODULAR_BRAIDED_COUNTS:
        raise FoundationSafetyError("catalog row rank outside scope")

    if row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE":
        if row["formal_admission_allowed"] is not False:
            raise FoundationSafetyError("blocked row cannot be admitted")
        if not row.get("blocker_ids"):
            raise FoundationSafetyError("blocked row needs blocker_ids")
        if not row.get("missing_evidence"):
            raise FoundationSafetyError("blocked row needs missing_evidence")
        if row.get("ribbon_realization_snapshot_hash") is not None:
            raise FoundationSafetyError("blocked row cannot have a snapshot hash")
    else:
        if row["formal_admission_allowed"] is not True:
            raise FoundationSafetyError("resolved row must be admissible")
        if not _is_sha256_id(row.get("ribbon_realization_snapshot_hash")):
            raise FoundationSafetyError("resolved row needs a snapshot hash")


def _validate_ribbon_realization_snapshot(evidence: dict[str, Any]) -> None:
    _require_equal(evidence, "category_contract", "RibbonFusionCategoryV2")
    _require_sha256(evidence, "category_data_hash")
    _require_object(evidence, "pinned_payload_hashes")
    certificates = _require_object(evidence, "certificates")
    _require_certificate_pass(certificates, "producer_exact_coherence")
    _require_certificate_pass(certificates, "consumer_runtime_coherence")
    _require_certificate_pass(certificates, "ribbon_pivotal_compatibility")
    checks = _require_object(evidence, "structural_checks")
    for field in (
        "pentagon",
        "hexagon",
        "rigidity",
        "duality_involution",
        "fusion_pairing_invertible",
        "r_inverse",
        "balancing",
        "ribbon_pivotal_compatibility",
    ):
        if checks.get(field) != "PASS":
            raise FoundationSafetyError(f"ribbon snapshot failed {field}")


def _validate_scan_plan(evidence: dict[str, Any]) -> None:
    _require_equal(evidence, "classification_catalog_status", RIBBON_CATALOG_ESTABLISHED)
    _require_equal(evidence, "audit_snapshot_state", "current-pinned")
    _require_sha256(evidence, "audit_snapshot_hash")
    _require_sha256(evidence, "classification_catalog_hash")
    pinned = _require_object(evidence, "pinned_hashes")
    for field in (
        "category_catalog",
        "manifold_catalog",
        "character_assignment_catalog",
        "evaluator_profile",
        "numeric_policy",
        "execution_semantics",
    ):
        if not _is_sha256_id(pinned.get(field)):
            raise FoundationSafetyError(f"scan plan missing pinned hash {field}")
    if not evidence.get("scan_case_ids"):
        raise FoundationSafetyError("scan plan needs scan_case_ids")


def _validate_scan_case_result(evidence: dict[str, Any]) -> None:
    _require_sha256(evidence, "scan_plan_hash")
    if not isinstance(evidence.get("scan_case_id"), str) or not evidence["scan_case_id"]:
        raise FoundationSafetyError("scan case result needs scan_case_id")
    if evidence.get("worker_revalidated_hashes") is not True:
        raise FoundationSafetyError("worker did not revalidate pinned hashes")
    input_hashes = _require_object(evidence, "input_hashes")
    for key, value in input_hashes.items():
        if not _is_sha256_id(value):
            raise FoundationSafetyError(f"scan case input hash {key} is invalid")
    if evidence.get("chunk_status") not in ("PASS", "FAIL", "INCONCLUSIVE"):
        raise FoundationSafetyError("scan case has unsupported chunk_status")


def _validate_scan_aggregate(evidence: dict[str, Any]) -> None:
    _require_sha256(evidence, "scan_plan_hash")
    enum = _require_object(evidence, "enumerator_certificate")
    if enum.get("status") != "PASS_COMPLETE_DENOMINATOR":
        raise FoundationSafetyError("aggregate lacks complete denominator certificate")
    expected = evidence.get("expected_case_count")
    actual = evidence.get("actual_case_count")
    if not isinstance(expected, int) or not isinstance(actual, int) or expected != actual:
        raise FoundationSafetyError("aggregate case count is incomplete")
    if evidence.get("aggregate_claim") == "global-no-go-theorem":
        raise FoundationSafetyError("aggregate cannot claim a global no-go theorem")


def _reject_authored_ready(value: Any) -> None:
    if isinstance(value, dict):
        for key, item in value.items():
            if key in {"ready", "readiness", "ready_status"}:
                raise FoundationSafetyError("readiness must be derived, not authored")
            _reject_authored_ready(item)
    elif isinstance(value, list):
        for item in value:
            _reject_authored_ready(item)
    elif value == FORBIDDEN_AUTHORED_READY_LITERAL:
        raise FoundationSafetyError("authored READY_FOR_SIGNAL_SCAN is forbidden")


def _require_schema(payload: dict[str, Any], schema: str) -> None:
    _require_equal(payload, "schema", schema)


def _require_equal(payload: dict[str, Any], field: str, expected: Any) -> None:
    if payload.get(field) != expected:
        raise FoundationSafetyError(
            f"{field} must be {expected!r}, got {payload.get(field)!r}"
        )


def _require_object(payload: dict[str, Any], field: str) -> dict[str, Any]:
    value = payload.get(field)
    if not isinstance(value, dict):
        raise FoundationSafetyError(f"{field} must be an object")
    return value


def _require_sha256(payload: dict[str, Any], field: str) -> None:
    if not _is_sha256_id(payload.get(field)):
        raise FoundationSafetyError(f"{field} must be a sha256 id")


def _require_certificate_pass(payload: dict[str, Any], field: str) -> None:
    certificate = payload.get(field)
    if not isinstance(certificate, dict) or certificate.get("status") != "PASS":
        raise FoundationSafetyError(f"certificate {field} did not pass")
    if not _is_sha256_id(certificate.get("content_hash")):
        raise FoundationSafetyError(f"certificate {field} lacks content hash")


def _is_sha256_id(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    if not value.startswith("sha256:") or len(value) != len("sha256:") + 64:
        return False
    hexdigest = value.removeprefix("sha256:")
    return all(char in "0123456789abcdef" for char in hexdigest)


__all__ = [
    "EVIDENCE_KIND_ALLOWLIST",
    "EXPECTED_MODULAR_BRAIDED_COUNTS",
    "FORMAL_ADMISSION_POLICY_SCHEMA",
    "FORMAL_SCAN_READINESS_SCHEMA",
    "FOUNDATION_STATUS",
    "FoundationSafetyError",
    "LOW_RANK_RIBBON_CATALOG_SCHEMA",
    "REJECTED_SOURCE_STATUSES",
    "RIBBON_CATALOG_BLOCKED",
    "RIBBON_CATALOG_ESTABLISHED",
    "TERMINAL_RIBBON_ROW_STATUSES",
    "add_content_hash",
    "stable_content_hash",
    "validate_formal_admission_policy",
    "validate_formal_evidence",
    "validate_formal_scan_readiness",
    "validate_low_rank_ribbon_catalog",
]
