"""Fail-closed R13 package for the complete Lean Kirby route."""

from __future__ import annotations

from collections import OrderedDict
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess
from typing import Any, Mapping

from twisted_yetter.computation_artifact_import_v1 import (
    KNOWN_BLOCKERS,
    validate_computation_import_runtime,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST_PATH = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "final-formalization-package-manifest-v1.json"
)
OBLIGATION_MATRIX_PATH = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "final-formalization-package-obligation-matrix-v1.json"
)
EXPECTED_MANIFEST_SHA256 = (
    "sha256:"
    "bcf53d4090508471bc296d52849a615d0ba49a81117751f1eb8157e27209356d"
)
EXPECTED_OBLIGATION_MATRIX_SHA256 = (
    "sha256:"
    "79522f2a52c08e5232c302bdb1016507905241ec40c59c9b7fd5c1c831ccae22"
)
RUNTIME_SCHEMA = "twisted-yetter.final-formalization-package-runtime.v1"
RUNTIME_STATUS = (
    "PASS_R13_FORMALIZATION_ROUTE_TERMINAL_WITH_EXPLICIT_FIGURE21_BLOCKERS"
)
ROADMAP_STATUS = (
    "R13_TERMINAL_FORMALIZATION_ROUTE_COMPLETE_RELATIVE_TO_EXPLICIT_BOUNDARIES"
)
EXPECTED_MILESTONE_IDS = (
    "R0",
    "R1",
    "R2_R4",
    "R5",
    "R6",
    "R7",
    "R8",
    "R9",
    "R10",
    "R11",
    "R12",
)
TRUSTED_INPUT_FIELDS = (
    "trusted_inputs",
    "trusted_input_boundary",
    "inherited_trusted_input_boundary",
    "trusted_topology_inputs",
)


def canonical_hash(payload: Mapping[str, Any]) -> str:
    """Hash a JSON object while omitting its own content hash."""

    body = deepcopy(dict(payload))
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def file_sha256(path: Path) -> str:
    """Hash exact file bytes with a tagged SHA-256 digest."""

    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def _payload_hash(payload: Any) -> str:
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _bytes_hash(data: bytes) -> str:
    return f"sha256:{hashlib.sha256(data).hexdigest()}"


def _tagged_sha256(value: str) -> str:
    return value if value.startswith("sha256:") else f"sha256:{value}"


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _read_json(path: Path) -> dict[str, Any]:
    _require(path.is_file(), f"missing JSON input: {path}")
    payload = json.loads(path.read_text())
    _require(isinstance(payload, dict), f"JSON input is not an object: {path}")
    return payload


def _repo_path(relative: str) -> Path:
    path = (REPO_ROOT / relative).resolve()
    _require(
        path == REPO_ROOT or REPO_ROOT in path.parents,
        f"path escapes repository: {relative}",
    )
    return path


def _git_bytes(commit: str, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    _require(
        result.returncode == 0,
        f"historical source is not replayable: {commit}:{relative}",
    )
    return result.stdout


def _verify_frozen_input(
    path: Path,
    expected_hash: str,
    *,
    schema: str,
    status: str,
) -> dict[str, Any]:
    _require(file_sha256(path) == expected_hash, f"{path.name} hash changed")
    payload = _read_json(path)
    _require(payload.get("schema") == schema, f"{path.name} schema changed")
    _require(payload.get("status") == status, f"{path.name} status changed")
    return payload


def _audit_milestone(
    spec: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    milestone_id = str(spec["milestone_id"])
    path = _repo_path(str(spec["path"]))
    payload = _read_json(path)

    _require(
        file_sha256(path) == spec["file_sha256"],
        f"{milestone_id} artifact file hash changed",
    )
    _require(payload.get("schema") == spec["schema"], f"{milestone_id} schema changed")
    _require(
        payload.get("status") == spec["expected_status"],
        f"{milestone_id} status changed",
    )
    _require(
        payload.get("mathematical_status")
        == spec["expected_mathematical_status"],
        f"{milestone_id} mathematical status changed",
    )
    _require(
        payload.get("content_hash") == spec["content_hash"],
        f"{milestone_id} content binding changed",
    )
    _require(
        canonical_hash(payload) == spec["content_hash"],
        f"{milestone_id} canonical content hash is stale",
    )

    git = payload.get("git")
    _require(isinstance(git, dict), f"{milestone_id} git provenance missing")
    _require(git.get("dirty") is False, f"{milestone_id} source was dirty")
    _require(
        git.get("commit") == spec["source_commit"],
        f"{milestone_id} source commit changed",
    )
    if spec.get("source_scope_caveat_required"):
        _require(
            bool(payload.get("source_scope_warning")),
            f"{milestone_id} source-scope caveat disappeared",
        )

    source_files = payload.get("inputs", {}).get("source_files")
    _require(
        isinstance(source_files, dict),
        f"{milestone_id} historical source map missing",
    )
    _require(
        len(source_files) == spec["expected_source_file_count"],
        f"{milestone_id} historical source denominator changed",
    )
    replay_records: list[dict[str, Any]] = []
    replayed_bytes = 0
    for relative, metadata in sorted(source_files.items()):
        _require(
            isinstance(metadata, dict)
            and isinstance(metadata.get("bytes"), int)
            and isinstance(metadata.get("sha256"), str),
            f"{milestone_id} malformed source record: {relative}",
        )
        data = _git_bytes(str(spec["source_commit"]), relative)
        _require(
            len(data) == metadata["bytes"],
            f"{milestone_id} historical source byte count changed: {relative}",
        )
        _require(
            _bytes_hash(data) == _tagged_sha256(metadata["sha256"]),
            f"{milestone_id} historical source hash changed: {relative}",
        )
        replayed_bytes += len(data)
        replay_records.append(
            {
                "path": relative,
                "bytes": len(data),
                "sha256": _tagged_sha256(metadata["sha256"]),
                "status": "PASS_HISTORICAL_GIT_REPLAY",
            }
        )

    nonclaims = payload.get("explicit_non_claims")
    _require(
        isinstance(nonclaims, list)
        and all(isinstance(item, str) and item for item in nonclaims),
        f"{milestone_id} non-claim list missing",
    )

    audit = {
        "milestone_id": milestone_id,
        "path": spec["path"],
        "schema": spec["schema"],
        "status": payload["status"],
        "mathematical_status": payload["mathematical_status"],
        "file_sha256": spec["file_sha256"],
        "content_hash": spec["content_hash"],
        "source_commit": spec["source_commit"],
        "source_clean": True,
        "source_file_count": len(replay_records),
        "source_replay_manifest_hash": _payload_hash(replay_records),
        "source_replayed_bytes": replayed_bytes,
        "source_replays": replay_records,
        "explicit_nonclaim_count": len(nonclaims),
    }
    return audit, payload


def _reference_has_locator(reference: Mapping[str, Any]) -> bool:
    if reference.get("locator"):
        return True
    locators = reference.get("locators")
    if isinstance(locators, list) and locators:
        return all(
            isinstance(locator, dict) and bool(locator.get("locator"))
            for locator in locators
        )
    byte_boundary = reference.get("exact_byte_capture")
    return (
        isinstance(byte_boundary, dict)
        and isinstance(byte_boundary.get("status"), str)
        and bool(byte_boundary.get("unsafe_interpretation"))
    )


def _capture_records(
    value: Any,
    *,
    ledger_path: str,
    output: list[dict[str, Any]],
) -> None:
    if isinstance(value, dict):
        if "capture_path_at_capture_time" in value:
            raw_hash = value.get("sha256")
            _require(
                isinstance(raw_hash, str) and raw_hash,
                f"external source capture has no hash: {ledger_path}",
            )
            tagged_hash = _tagged_sha256(raw_hash)
            output.append(
                {
                    "ledger_path": ledger_path,
                    "capture_path_at_capture_time": value[
                        "capture_path_at_capture_time"
                    ],
                    "sha256": tagged_hash,
                    "bytes": value.get("bytes"),
                    "repo_local_bytes": bool(value.get("repo_local_bytes", False)),
                    "required_for_r13_replay": False,
                }
            )
        for nested in value.values():
            _capture_records(nested, ledger_path=ledger_path, output=output)
    elif isinstance(value, list):
        for nested in value:
            _capture_records(nested, ledger_path=ledger_path, output=output)


def _audit_reference_ledger(
    spec: Mapping[str, Any],
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    relative = str(spec["path"])
    path = _repo_path(relative)
    payload = _read_json(path)
    _require(
        file_sha256(path) == spec["file_sha256"],
        f"reference ledger hash changed: {relative}",
    )
    _require(payload.get("schema") == spec["schema"], f"ledger schema changed: {relative}")
    _require(
        payload.get("status") == spec["expected_status"],
        f"ledger status changed: {relative}",
    )
    references = payload.get("references")
    _require(isinstance(references, list), f"ledger references missing: {relative}")
    _require(
        len(references) == spec["expected_reference_count"],
        f"ledger reference denominator changed: {relative}",
    )
    ref_ids: list[str] = []
    for reference in references:
        _require(
            isinstance(reference, dict)
            and isinstance(reference.get("ref_id"), str)
            and reference["ref_id"].startswith("ref:"),
            f"ledger reference identity missing: {relative}",
        )
        _require(
            _reference_has_locator(reference),
            f"ledger reference locator/boundary missing: {reference['ref_id']}",
        )
        ref_ids.append(reference["ref_id"])

    captures: list[dict[str, Any]] = []
    _capture_records(payload, ledger_path=relative, output=captures)
    return (
        {
            "path": relative,
            "schema": spec["schema"],
            "status": spec["expected_status"],
            "file_sha256": spec["file_sha256"],
            "reference_count": len(references),
            "reference_ids": ref_ids,
        },
        captures,
    )


def _trusted_input_key(record: Mapping[str, Any]) -> str:
    key = record.get("input_id", record.get("input"))
    _require(isinstance(key, str) and key, "trusted input has no stable identity")
    return key


def _audit_trusted_inputs(
    milestone_payloads: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    catalog: OrderedDict[str, dict[str, Any]] = OrderedDict()
    occurrence_count = 0
    for milestone_id, payload in milestone_payloads.items():
        populated = [
            field for field in TRUSTED_INPUT_FIELDS if field in payload
        ]
        _require(
            len(populated) <= 1,
            f"{milestone_id} has ambiguous trusted-input fields",
        )
        if not populated:
            continue
        field = populated[0]
        records = payload[field]
        _require(
            isinstance(records, list),
            f"{milestone_id} trusted-input list is malformed",
        )
        for record in records:
            _require(
                isinstance(record, dict),
                f"{milestone_id} trusted input is not an object",
            )
            occurrence_count += 1
            key = _trusted_input_key(record)
            inherited = field == "inherited_trusted_input_boundary"
            if key in catalog:
                _require(
                    catalog[key]["exact_record"] == record,
                    f"trusted input changed across milestones: {key}",
                )
                catalog[key]["origins"].append(
                    {"milestone_id": milestone_id, "inherited": inherited}
                )
            else:
                catalog[key] = {
                    "input_id": key,
                    "exact_record": deepcopy(record),
                    "origins": [
                        {"milestone_id": milestone_id, "inherited": inherited}
                    ],
                }
    return {
        "status": "PASS_ALL_TRUSTED_INPUTS_VISIBLE_AND_DEDUPLICATED",
        "occurrence_count": occurrence_count,
        "unique_count": len(catalog),
        "catalog": list(catalog.values()),
    }


def _build_runtime_uncached() -> dict[str, Any]:
    manifest = _verify_frozen_input(
        MANIFEST_PATH,
        EXPECTED_MANIFEST_SHA256,
        schema="twisted-yetter.final-formalization-package-manifest.v1",
        status="R13_FROZEN_DENOMINATOR",
    )
    obligations = _verify_frozen_input(
        OBLIGATION_MATRIX_PATH,
        EXPECTED_OBLIGATION_MATRIX_SHA256,
        schema=(
            "twisted-yetter.final-formalization-package-obligation-matrix.v1"
        ),
        status="R13_CONTRACT_FROZEN_PENDING_IMPLEMENTATION",
    )
    totals = manifest.get("expected_totals")
    _require(isinstance(totals, dict), "manifest expected totals missing")
    _require(
        len(obligations.get("obligations", [])) == 24,
        "R13 obligation denominator changed",
    )
    _require(
        len(obligations.get("explicit_non_claims", [])) == 10,
        "R13 explicit non-claim denominator changed",
    )

    specs = manifest.get("milestone_artifacts")
    _require(isinstance(specs, list), "milestone artifact manifest missing")
    milestone_ids = tuple(spec.get("milestone_id") for spec in specs)
    _require(
        milestone_ids == EXPECTED_MILESTONE_IDS,
        "milestone denominator/order changed",
    )
    _require(
        len(set(milestone_ids)) == len(milestone_ids),
        "duplicate milestone artifact",
    )

    milestone_audits: list[dict[str, Any]] = []
    milestone_payloads: OrderedDict[str, dict[str, Any]] = OrderedDict()
    for spec in specs:
        audit, payload = _audit_milestone(spec)
        milestone_audits.append(audit)
        milestone_payloads[audit["milestone_id"]] = payload

    replay_count = sum(
        audit["source_file_count"] for audit in milestone_audits
    )
    _require(
        replay_count == totals["historical_source_file_replay_count"],
        "historical source replay denominator changed",
    )

    ledger_specs = manifest.get("reference_ledgers")
    _require(isinstance(ledger_specs, list), "reference ledger manifest missing")
    ledger_audits: list[dict[str, Any]] = []
    source_captures: list[dict[str, Any]] = []
    for spec in ledger_specs:
        audit, captures = _audit_reference_ledger(spec)
        ledger_audits.append(audit)
        source_captures.extend(captures)
    reference_count = sum(
        ledger["reference_count"] for ledger in ledger_audits
    )
    _require(
        len(ledger_audits) == totals["reference_ledger_count"],
        "reference ledger denominator changed",
    )
    _require(
        reference_count == totals["reference_record_count"],
        "reference record denominator changed",
    )

    trusted_inputs = _audit_trusted_inputs(milestone_payloads)
    _require(
        trusted_inputs["unique_count"] == totals["unique_trusted_input_count"],
        "unique trusted-input denominator changed",
    )

    predecessor_nonclaims = [
        {
            "milestone_id": milestone_id,
            "nonclaims": deepcopy(payload["explicit_non_claims"]),
        }
        for milestone_id, payload in milestone_payloads.items()
    ]
    predecessor_nonclaim_count = sum(
        len(record["nonclaims"]) for record in predecessor_nonclaims
    )
    _require(
        predecessor_nonclaim_count
        == totals["predecessor_nonclaim_count"],
        "predecessor non-claim denominator changed",
    )

    layers = manifest.get("evidence_layers")
    _require(
        isinstance(layers, list)
        and len(layers) == totals["evidence_layer_count"],
        "evidence layer denominator changed",
    )
    layered_milestones = [
        milestone
        for layer in layers
        for milestone in layer.get("milestones", [])
    ]
    _require(
        tuple(layered_milestones) == EXPECTED_MILESTONE_IDS,
        "evidence layers omit or reorder milestones",
    )

    r12 = milestone_payloads["R12"]["runtime_certificate"]
    validate_computation_import_runtime(r12)
    r12_admission = r12["admission"]
    _require(
        tuple(r12_admission["blockers"]) == KNOWN_BLOCKERS,
        "R12 Figure 21 blockers changed",
    )
    _require(
        manifest["figure21_terminal_blockers"] == list(KNOWN_BLOCKERS),
        "R13 Figure 21 blocker denominator changed",
    )

    runtime: dict[str, Any] = {
        "schema": RUNTIME_SCHEMA,
        "status": RUNTIME_STATUS,
        "roadmap_status": ROADMAP_STATUS,
        "frozen_inputs": {
            "manifest_path": str(MANIFEST_PATH.relative_to(REPO_ROOT)),
            "manifest_file_sha256": EXPECTED_MANIFEST_SHA256,
            "obligation_matrix_path": str(
                OBLIGATION_MATRIX_PATH.relative_to(REPO_ROOT)
            ),
            "obligation_matrix_file_sha256": (
                EXPECTED_OBLIGATION_MATRIX_SHA256
            ),
            "obligation_count": len(obligations["obligations"]),
            "r13_explicit_nonclaims": deepcopy(
                obligations["explicit_non_claims"]
            ),
        },
        "evidence_layers": deepcopy(layers),
        "milestone_audit": {
            "status": "PASS_ALL_11_MILESTONES_CONTENT_AND_HISTORY_REPLAYED",
            "artifact_count": len(milestone_audits),
            "historical_source_file_replay_count": replay_count,
            "artifacts": milestone_audits,
        },
        "reference_audit": {
            "status": "PASS_ALL_8_REFERENCE_LEDGERS_HASH_BOUND",
            "ledger_count": len(ledger_audits),
            "reference_record_count": reference_count,
            "ledgers": ledger_audits,
        },
        "external_source_capture_boundary": {
            "status": "EXTERNAL_BYTES_NOT_REQUIRED_FOR_R13_REPLAY",
            "capture_metadata_occurrence_count": len(source_captures),
            "capture_metadata": source_captures,
            "source_byte_complete_archive": False,
            "unsafe_interpretation": (
                "Recorded external hashes and locators do not imply that all "
                "primary-source bytes are vendored in this repository."
            ),
        },
        "trusted_input_audit": trusted_inputs,
        "predecessor_nonclaim_audit": {
            "status": "PASS_ALL_PREDECESSOR_NONCLAIMS_PRESERVED_VERBATIM",
            "nonclaim_count": predecessor_nonclaim_count,
            "by_milestone": predecessor_nonclaims,
        },
        "terminal_boundary": {
            "formalization_route_terminal": True,
            "r11_conditional_invariant_established": True,
            "r12_exact_control_admitted": True,
            "figure21_structural_row_count": 15,
            "figure21_structural_denominators_complete": True,
            "figure21_terminal_blockers": list(KNOWN_BLOCKERS),
            "figure21_exact_value_admitted": False,
            "figure21_marked_comparison_admitted": False,
            "crane_yetter_identification_established": False,
            "all_imported_category_identities_reproved": False,
            "source_byte_complete_archive": False,
            "ctl_claim_admitted": False,
        },
        "explicit_non_claims": deepcopy(obligations["explicit_non_claims"]),
    }
    runtime["content_hash"] = canonical_hash(runtime)
    return runtime


@lru_cache(maxsize=1)
def _frozen_runtime_json() -> str:
    return json.dumps(
        _build_runtime_uncached(), sort_keys=True, separators=(",", ":")
    )


def build_final_formalization_runtime() -> dict[str, Any]:
    """Replay the complete frozen R0--R12 package."""

    return json.loads(_frozen_runtime_json())


def validate_final_formalization_runtime(
    payload: Mapping[str, Any],
) -> None:
    """Reject any package that differs from the frozen historical replay."""

    _require(
        payload.get("content_hash") == canonical_hash(payload),
        "R13 runtime content hash is stale",
    )
    _require(payload.get("schema") == RUNTIME_SCHEMA, "R13 runtime schema changed")
    _require(payload.get("status") == RUNTIME_STATUS, "R13 runtime status changed")
    milestone_audit = payload.get("milestone_audit", {})
    _require(
        milestone_audit.get("artifact_count") == 11,
        "R13 milestone denominator changed",
    )
    _require(
        milestone_audit.get("historical_source_file_replay_count") == 231,
        "R13 historical source replay denominator changed",
    )
    _require(
        payload.get("reference_audit", {}).get("ledger_count") == 8,
        "R13 reference ledger denominator changed",
    )
    _require(
        payload.get("trusted_input_audit", {}).get("unique_count") == 25,
        "R13 trusted-input denominator changed",
    )
    _require(
        payload.get("predecessor_nonclaim_audit", {}).get("nonclaim_count")
        == 64,
        "R13 predecessor non-claim denominator changed",
    )
    boundary = payload.get("terminal_boundary", {})
    _require(
        boundary.get("formalization_route_terminal") is True,
        "R13 formalization route is not terminal",
    )
    _require(
        boundary.get("figure21_terminal_blockers") == list(KNOWN_BLOCKERS),
        "R13 Figure 21 blocker denominator changed",
    )
    for field in (
        "figure21_exact_value_admitted",
        "figure21_marked_comparison_admitted",
        "crane_yetter_identification_established",
        "all_imported_category_identities_reproved",
        "source_byte_complete_archive",
        "ctl_claim_admitted",
    ):
        _require(
            boundary.get(field) is False,
            f"R13 forbidden promotion: {field}",
        )
    expected = json.loads(_frozen_runtime_json())
    _require(
        dict(payload) == expected,
        "R13 runtime differs from the frozen historical replay",
    )
