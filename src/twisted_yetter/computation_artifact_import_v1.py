"""Fail-closed R12 importer for exact and structural computation artifacts."""

from __future__ import annotations

from collections import Counter
from copy import deepcopy
import hashlib
import importlib
import json
from pathlib import Path
import sys
from typing import Any, Mapping

from twisted_yetter.homologically_twisted_invariant_v1 import (
    validate_invariant_runtime,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST_PATH = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "computation-artifact-import-manifest-v1.json"
)
EXPECTED_MANIFEST_SHA256 = (
    "sha256:"
    "192d23aa1d276d36ef5d44ae279ddebbc7bec0e95e6ff2c0bd2d6db3abedb4c2"
)
RUNTIME_SCHEMA = "twisted-yetter.computation-artifact-import-runtime.v1"
RUNTIME_STATUS = (
    "PASS_EXACT_CONTROL_AND_FIGURE21_STRUCTURAL_IMPORT_TERMINAL_BLOCKED"
)
EXACT_CONTROL_STATUS = "PASS_EXACT_R11_IMPORTER_CONTROL"
STRUCTURAL_STATUS = "PASS_FIGURE21_POINTED_STRUCTURAL_DENOMINATORS"
BLOCKED_STATUS = "TERMINAL_BLOCKED_FIGURE21_EXACT_INVARIANT_PROMOTION"
FIGURE21_INPUT_SHA256 = (
    "sha256:"
    "b6f8459547a7cec415eb6c70acb89a40c37ab4cabd364330206685d8e579cbc5"
)
FIGURE21_PROJECTED_IR_HASH = (
    "sha256:"
    "7b96de795e98bf8b521e33c9977c5eccbbde63e1d4296554ad388c609ff71695"
)
FIGURE21_COUPON_GRAPH_HASH = (
    "sha256:"
    "f66f1ef64661c432c389b6c1db726de605055ea0cabe74005fa649ebbd32a26c"
)
KNOWN_BLOCKERS = (
    "DIRTY_PROVENANCE_RECORDED",
    "DRAFT_FIGURE21_TRANSCRIPTION",
    "ROUNDED_COMPLEX_OUTPUT_WITHOUT_EXACT_CYCLOTOMIC_CERTIFICATE",
    "MISSING_CONCRETE_R11_SEMANTIC_BINDING",
    "UNSEALED_TRANSITIVE_EVALUATOR_SOURCE_CLOSURE",
    "MISSING_MARKED_H2_COMPARISON_CERTIFICATE",
)
EXPECTED_ROWS = {
    "rank2-cyclic-z2-semion-minus": (2, 2048),
    "rank2-cyclic-z2-semion-plus": (2, 2048),
    "rank3-cyclic-z3-minus": (3, 177147),
    "rank3-cyclic-z3-plus": (3, 177147),
    "rank4-pointed-z2xz2-q002": (4, 4194304),
    "rank4-pointed-z2xz2-q013": (4, 4194304),
    "rank4-pointed-z2xz2-q112": (4, 4194304),
    "rank4-pointed-z2xz2-q222": (4, 4194304),
    "rank4-pointed-z2xz2-q233": (4, 4194304),
    "rank4-pointed-z4-k1": (4, 4194304),
    "rank4-pointed-z4-k3": (4, 4194304),
    "rank4-pointed-z4-k5": (4, 4194304),
    "rank4-pointed-z4-k7": (4, 4194304),
    "rank5-su5-1-s1": (5, 48828125),
    "rank5-su5-1-s2": (5, 48828125),
}
EXPECTED_TOTAL_SECTORS = sum(count for _, count in EXPECTED_ROWS.values())
EXPECTED_CHUNK_ARTIFACTS = 1832


def canonical_hash(payload: Mapping[str, Any]) -> str:
    """Hash one runtime payload while omitting its own content hash."""

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


def _canonical_field_hash(
    payload: Mapping[str, Any],
    field: str,
    *,
    tagged: bool,
) -> str:
    body = deepcopy(dict(payload))
    body.pop(field, None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    digest = hashlib.sha256(encoded).hexdigest()
    return f"sha256:{digest}" if tagged else digest


def _payload_hash(payload: Any, *, tagged: bool = False) -> str:
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()
    digest = hashlib.sha256(encoded).hexdigest()
    return f"sha256:{digest}" if tagged else digest


def _is_sha256(value: object, *, tagged: bool = True) -> bool:
    if not isinstance(value, str):
        return False
    expected_length = 71 if tagged else 64
    digest = value[7:] if tagged and value.startswith("sha256:") else value
    return (
        len(value) == expected_length
        and len(digest) == 64
        and all(character in "0123456789abcdef" for character in digest)
    )


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _read_json(path: Path) -> dict[str, Any]:
    _require(path.is_file(), f"missing artifact: {path}")
    payload = json.loads(path.read_text())
    _require(isinstance(payload, dict), f"artifact is not an object: {path}")
    return payload


def _repo_path(relative: str) -> Path:
    path = (REPO_ROOT / relative).resolve()
    _require(
        path == REPO_ROOT or REPO_ROOT in path.parents,
        f"path escapes repository: {relative}",
    )
    return path


def _verify_file_binding(path: Path, expected: str, label: str) -> None:
    _require(_is_sha256(expected), f"{label} has malformed pinned SHA-256")
    _require(file_sha256(path) == expected, f"{label} file hash changed")


def _verify_content_hash(
    payload: Mapping[str, Any],
    field: str,
    label: str,
    *,
    tagged: bool,
) -> None:
    actual = payload.get(field)
    _require(
        _is_sha256(actual, tagged=tagged),
        f"{label} has malformed content hash",
    )
    expected = _canonical_field_hash(payload, field, tagged=tagged)
    _require(actual == expected, f"{label} content hash is stale")


def _sum_distribution(value: object, label: str) -> int:
    _require(isinstance(value, dict), f"{label} is not a distribution")
    _require(
        all(isinstance(count, int) and count >= 0 for count in value.values()),
        f"{label} has a non-natural count",
    )
    return sum(value.values())


def _chunk_bounds(total: int, count: int, chunk_id: int) -> tuple[int, int]:
    quotient, remainder = divmod(total, count)
    start = chunk_id * quotient + min(chunk_id, remainder)
    end = start + quotient + (1 if chunk_id < remainder else 0)
    return start, end


def _validate_snapshot(spec: Mapping[str, Any]) -> dict[str, Any]:
    path = _repo_path(str(spec["snapshot_path"]))
    snapshot = _read_json(path)
    _verify_content_hash(
        snapshot, "content_hash", str(spec["realization_id"]), tagged=True
    )
    _require(
        snapshot["content_hash"] == spec["snapshot_content_hash"],
        f"{spec['realization_id']} snapshot binding changed",
    )
    _require(
        snapshot.get("realization_id") == spec["realization_id"],
        f"{spec['realization_id']} snapshot identity mismatch",
    )
    _require(
        snapshot.get("status") == "RESOLVED_RIBBON_REALIZATION",
        f"{spec['realization_id']} snapshot is unresolved",
    )
    _require(
        snapshot["category_data_hash"]
        == _payload_hash(snapshot["category_data"], tagged=True),
        f"{spec['realization_id']} category-data hash is stale",
    )
    _require(
        snapshot["category_data_hash"] == spec["category_data_hash"],
        f"{spec['realization_id']} category hash mismatch",
    )
    _require(
        snapshot.get("mutable_alias_inputs") == [],
        f"{spec['realization_id']} snapshot uses a mutable alias",
    )

    structural = snapshot.get("structural_checks")
    _require(
        isinstance(structural, dict)
        and structural
        and set(structural.values()) == {"PASS"},
        f"{spec['realization_id']} structural checks are incomplete",
    )
    certificates = snapshot.get("certificates")
    expected_certificate_names = {
        "producer_exact_coherence",
        "consumer_runtime_coherence",
        "ribbon_pivotal_compatibility",
    }
    _require(
        isinstance(certificates, dict)
        and set(certificates) == expected_certificate_names,
        f"{spec['realization_id']} certificate denominator changed",
    )
    certificate_hashes: dict[str, str] = {}
    for name, certificate in certificates.items():
        _require(
            certificate.get("status") == "PASS",
            f"{spec['realization_id']} {name} did not pass",
        )
        _require(
            certificate.get("category_data_hash")
            == snapshot["category_data_hash"],
            f"{spec['realization_id']} {name} category binding changed",
        )
        _verify_content_hash(
            certificate,
            "content_hash",
            f"{spec['realization_id']} {name}",
            tagged=True,
        )
        certificate_hashes[name] = certificate["content_hash"]

    pinned_values = set(snapshot.get("pinned_payload_hashes", {}).values())
    _require(
        snapshot["category_data_hash"] in pinned_values,
        f"{spec['realization_id']} category payload is not pinned",
    )
    _require(
        set(certificate_hashes.values()).issubset(pinned_values),
        f"{spec['realization_id']} certificates are not all pinned",
    )
    git = snapshot.get("git")
    _require(
        isinstance(git, dict)
        and isinstance(git.get("dirty"), bool)
        and isinstance(git.get("commit"), str),
        f"{spec['realization_id']} snapshot provenance is malformed",
    )
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "file_sha256": file_sha256(path),
        "content_hash": snapshot["content_hash"],
        "category_data_hash": snapshot["category_data_hash"],
        "certificate_hashes": certificate_hashes,
        "structural_check_count": len(structural),
        "mutable_alias_count": 0,
        "source_commit": git["commit"],
        "recorded_dirty": git["dirty"],
    }


def _validate_aggregate_row(
    spec: Mapping[str, Any],
    batch_row: Mapping[str, Any],
) -> dict[str, Any]:
    realization_id = str(spec["realization_id"])
    path = _repo_path(str(spec["source_path"]))
    aggregate = _read_json(path)
    _verify_file_binding(path, str(spec["source_sha256"]), realization_id)
    _verify_content_hash(
        aggregate, "content_sha256", realization_id, tagged=False
    )
    _require(
        aggregate.get("status") == "PASS_AGGREGATE_COMPLETE",
        f"{realization_id} aggregate is incomplete",
    )
    expected = int(spec["expected_sector_count"])
    for key, value in (
        ("realization_id", realization_id),
        ("rank", spec["rank"]),
        ("snapshot_content_hash", spec["snapshot_content_hash"]),
        ("category_data_hash", spec["category_data_hash"]),
        ("expected_sector_count", expected),
        ("observed_sector_count", expected),
    ):
        _require(
            aggregate.get(key) == value,
            f"{realization_id} aggregate {key} mismatch",
        )
    _require(
        batch_row.get("aggregate_sha256") == spec["source_sha256"],
        f"{realization_id} batch aggregate hash mismatch",
    )
    for key in (
        "value_distribution",
        "status_distribution",
        "projector_rank_distribution",
    ):
        _require(
            _sum_distribution(aggregate.get(key), f"{realization_id} {key}")
            == expected,
            f"{realization_id} {key} denominator is incomplete",
        )
        if key in batch_row:
            _require(
                aggregate[key] == batch_row[key],
                f"{realization_id} batch {key} differs from aggregate",
            )

    chunk_count = aggregate.get("chunk_count")
    _require(
        isinstance(chunk_count, int) and chunk_count > 0,
        f"{realization_id} chunk count is invalid",
    )
    _require(
        chunk_count == batch_row.get("chunk_count"),
        f"{realization_id} batch chunk count mismatch",
    )
    hashes = aggregate.get("chunk_hashes")
    _require(
        isinstance(hashes, list) and len(hashes) == chunk_count,
        f"{realization_id} chunk hash denominator changed",
    )
    chunk_paths = sorted(path.parent.glob("chunk-*.json"))
    _require(
        len(chunk_paths) == chunk_count,
        f"{realization_id} missing or extra chunk files",
    )

    accumulated_value: Counter[str] = Counter()
    accumulated_status: Counter[str] = Counter()
    accumulated_projector: Counter[str] = Counter()
    chunk_records: list[dict[str, Any]] = []
    previous_end = 0
    for chunk_id, chunk_path in enumerate(chunk_paths):
        chunk = _read_json(chunk_path)
        _verify_content_hash(
            chunk,
            "content_sha256",
            f"{realization_id} chunk {chunk_id}",
            tagged=False,
        )
        _require(
            chunk["content_sha256"] == hashes[chunk_id],
            f"{realization_id} chunk {chunk_id} hash not in aggregate",
        )
        start, end = _chunk_bounds(expected, chunk_count, chunk_id)
        required = {
            "schema": "twisted-yetter.figure21-pointed-category-chunk.v1",
            "status": "PASS_CHUNK_COMPLETE",
            "realization_id": realization_id,
            "rank": spec["rank"],
            "snapshot_content_hash": spec["snapshot_content_hash"],
            "category_data_hash": spec["category_data_hash"],
            "chunk_id": chunk_id,
            "chunk_count": chunk_count,
            "start_sector_id": start,
            "end_sector_id_exclusive": end,
            "sector_count": end - start,
            "full_sector_count": expected,
            "figure21_projected_ir_hash": FIGURE21_PROJECTED_IR_HASH,
            "figure21_coupon_graph_hash": FIGURE21_COUPON_GRAPH_HASH,
        }
        for key, value in required.items():
            _require(
                chunk.get(key) == value,
                f"{realization_id} chunk {chunk_id} {key} mismatch",
            )
        _require(
            start == previous_end,
            f"{realization_id} chunk ranges have a gap or overlap",
        )
        previous_end = end
        for key, counter in (
            ("value_distribution", accumulated_value),
            ("status_distribution", accumulated_status),
            ("projector_rank_distribution", accumulated_projector),
        ):
            _require(
                _sum_distribution(
                    chunk.get(key), f"{realization_id} chunk {chunk_id} {key}"
                )
                == end - start,
                f"{realization_id} chunk {chunk_id} {key} is incomplete",
            )
            counter.update(chunk[key])
        chunk_records.append(
            {
                "chunk_id": chunk_id,
                "path": str(chunk_path.relative_to(REPO_ROOT)),
                "content_sha256": chunk["content_sha256"],
                "start_sector_id": start,
                "end_sector_id_exclusive": end,
                "sector_count": end - start,
                "recorded_dirty": bool(chunk.get("git_dirty")),
            }
        )
    _require(
        previous_end == expected,
        f"{realization_id} chunk ranges do not reach the denominator",
    )
    _require(
        dict(sorted(accumulated_value.items()))
        == aggregate["value_distribution"],
        f"{realization_id} value aggregate is not the chunk sum",
    )
    _require(
        dict(sorted(accumulated_status.items()))
        == aggregate["status_distribution"],
        f"{realization_id} status aggregate is not the chunk sum",
    )
    _require(
        dict(sorted(accumulated_projector.items()))
        == aggregate["projector_rank_distribution"],
        f"{realization_id} projector aggregate is not the chunk sum",
    )
    return {
        "source_kind": "aggregate",
        "source_path": str(path.relative_to(REPO_ROOT)),
        "source_file_sha256": file_sha256(path),
        "source_content_sha256": aggregate["content_sha256"],
        "source_commit": aggregate["git_commit"],
        "recorded_dirty": bool(aggregate["git_dirty"]),
        "source_snapshot_content_hash": aggregate[
            "snapshot_content_hash"
        ],
        "source_category_data_hash": aggregate["category_data_hash"],
        "expected_sector_count": expected,
        "observed_sector_count": expected,
        "value_distribution": aggregate["value_distribution"],
        "status_distribution": aggregate["status_distribution"],
        "projector_rank_distribution": aggregate[
            "projector_rank_distribution"
        ],
        "chunk_count": chunk_count,
        "chunk_records": chunk_records,
    }


def _validate_rank2_row(
    spec: Mapping[str, Any],
    batch_row: Mapping[str, Any],
    source: Mapping[str, Any],
) -> dict[str, Any]:
    realization_id = str(spec["realization_id"])
    branch = realization_id.rsplit("-", 1)[-1]
    result = source["results"][branch]
    expected = int(spec["expected_sector_count"])
    _require(
        result.get("category_id") == realization_id,
        f"{realization_id} category identity mismatch",
    )
    _require(
        result.get("sector_count") == expected
        and result.get("full_sector_count") == expected,
        f"{realization_id} sector denominator is incomplete",
    )
    _require(
        result.get("all_modular_values_equal_pointed_values") is True
        and result.get("max_modular_pointed_abs_error") == 0.0,
        f"{realization_id} modular/pointed control failed",
    )
    _require(
        result.get("snapshot", {}).get("content_hash")
        == spec["snapshot_content_hash"]
        and result.get("snapshot", {}).get("category_data_hash")
        == spec["category_data_hash"],
        f"{realization_id} evaluator/snapshot binding changed",
    )
    records = result.get("sector_records")
    _require(
        isinstance(records, list) and len(records) == expected,
        f"{realization_id} sector records are incomplete",
    )
    _require(
        result.get("sector_records_sha256") == _payload_hash(records),
        f"{realization_id} sector-record hash is stale",
    )
    _require(
        [record.get("sector_id") for record in records]
        == list(range(expected)),
        f"{realization_id} sector IDs are not complete and ordered",
    )
    for key in (
        "value_distribution",
        "value_status_distribution",
        "projector_rank_distribution",
    ):
        _require(
            _sum_distribution(result.get(key), f"{realization_id} {key}")
            == expected,
            f"{realization_id} {key} denominator is incomplete",
        )
    _require(
        result["value_distribution"] == batch_row.get("value_distribution")
        or "value_distribution" not in batch_row,
        f"{realization_id} batch value distribution differs",
    )
    return {
        "source_kind": "rank2_full_evaluation",
        "source_path": str(spec["source_path"]),
        "source_file_sha256": str(spec["source_sha256"]),
        "source_commit": source["git_commit"],
        "recorded_dirty": bool(source["git_dirty"]),
        "source_snapshot_content_hash": spec["snapshot_content_hash"],
        "source_category_data_hash": spec["category_data_hash"],
        "expected_sector_count": expected,
        "observed_sector_count": expected,
        "value_distribution": result["value_distribution"],
        "status_distribution": result["value_status_distribution"],
        "projector_rank_distribution": result[
            "projector_rank_distribution"
        ],
        "chunk_count": 0,
        "chunk_records": [],
        "sector_records_sha256": result["sector_records_sha256"],
        "modular_pointed_max_abs_error": 0.0,
    }


def _validate_exact_control(spec: Mapping[str, Any]) -> dict[str, Any]:
    path = _repo_path(str(spec["path"]))
    payload = _read_json(path)
    _verify_file_binding(path, str(spec["file_sha256"]), "R11 exact control")
    _verify_content_hash(
        payload, "content_hash", "R11 exact control", tagged=True
    )
    _require(
        payload.get("content_hash") == spec["content_hash"],
        "R11 exact-control content binding changed",
    )
    _require(
        payload.get("status") == spec["expected_status"],
        "R11 exact-control status changed",
    )
    _require(
        payload.get("git", {}).get("dirty") is False
        and payload.get("git", {}).get("commit") == spec["source_commit"],
        "R11 exact-control provenance is not clean and pinned",
    )
    runtime = payload.get("runtime_certificate")
    validate_invariant_runtime(runtime)
    cases = runtime["marked_pair_system"]["cases"]
    _require(len(cases) == 4, "R11 exact-control alpha denominator changed")
    _require(
        all(case["chosen_value"] == case["target_value"] for case in cases),
        "R11 exact-control output is not target-bound",
    )
    return {
        "status": EXACT_CONTROL_STATUS,
        "path": str(path.relative_to(REPO_ROOT)),
        "file_sha256": file_sha256(path),
        "content_hash": payload["content_hash"],
        "source_commit": payload["git"]["commit"],
        "source_clean": True,
        "mutable_alias_count": 0,
        "inconclusive_count": 0,
        "arithmetic_mode": "EXACT_RATIONAL",
        "r11_semantic_binding": True,
        "marked_class_count": 4,
        "exact_value": cases[0]["chosen_value"],
        "claim_boundary": (
            "Importer plumbing control under the R11 toy/runtime fixture; "
            "not a concrete category evaluation."
        ),
    }


def _validate_figure21_identity(spec: Mapping[str, Any]) -> dict[str, Any]:
    path = _repo_path(str(spec["diagram_path"]))
    payload = _read_json(path)
    _verify_file_binding(
        path, str(spec["diagram_file_sha256"]), "Figure 21 input"
    )
    _require(
        payload.get("status") == spec["source_status"],
        "Figure 21 source-status binding changed",
    )
    if str(REPO_ROOT) not in sys.path:
        sys.path.insert(0, str(REPO_ROOT))
    figure21_sweep = importlib.import_module(
        "experiments.scripts."
        "run_figure21_standard_pointed_modular_sweep_v1"
    )
    from experiments.scripts.special_dotted_morphism import stable_json_hash

    context = figure21_sweep._load_figure21()
    projected_ir_hash = stable_json_hash(context["ir"])
    coupon_graph_hash = context["graph"]["graph_hash"]
    _require(
        projected_ir_hash == spec["projected_ir_hash"]
        == FIGURE21_PROJECTED_IR_HASH,
        "Figure 21 projected IR hash changed",
    )
    _require(
        coupon_graph_hash == spec["coupon_graph_hash"]
        == FIGURE21_COUPON_GRAPH_HASH,
        "Figure 21 coupon graph hash changed",
    )
    return {
        "diagram_path": str(path.relative_to(REPO_ROOT)),
        "diagram_file_sha256": file_sha256(path),
        "source_status": payload["status"],
        "projected_ir_hash": projected_ir_hash,
        "coupon_graph_hash": coupon_graph_hash,
        "diagram_certified_against_printed_source": False,
    }


def _validate_comparisons(
    specs: list[Mapping[str, Any]],
) -> dict[str, Any]:
    records: list[dict[str, Any]] = []
    for spec in specs:
        path = _repo_path(str(spec["path"]))
        payload = _read_json(path)
        _verify_file_binding(path, str(spec["file_sha256"]), str(path))
        _verify_content_hash(
            payload, "content_hash", str(path), tagged=True
        )
        _require(
            payload.get("content_hash") == spec["content_hash"]
            and payload.get("status") == spec["expected_status"],
            f"{path} comparison binding changed",
        )
        _require(
            payload.get("git_dirty") is True,
            f"{path} no longer carries the recorded dirty blocker",
        )
        nonclaims = "\n".join(payload.get("non_claims", []))
        records.append(
            {
                "path": str(path.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(path),
                "content_hash": payload["content_hash"],
                "status": payload["status"],
                "recorded_dirty": True,
                "marked_h2_certified": False,
                "source_explicitly_names_marked_h2_nonclaim": (
                    "marked H2" in nonclaims
                ),
            }
        )
    return {
        "status": "PASS_THREE_UNMARKED_DISTRIBUTION_COMPARISONS_IMPORTED",
        "artifact_count": len(records),
        "records": records,
        "marked_h2_comparison_ready": False,
    }


def _validate_entry_points(
    specs: list[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    records = []
    for spec in specs:
        path = _repo_path(str(spec["path"]))
        _verify_file_binding(path, str(spec["file_sha256"]), str(path))
        records.append(
            {
                "path": str(path.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(path),
                "scope": spec["scope"],
            }
        )
    return records


def build_computation_import_runtime(
    manifest_path: Path = MANIFEST_PATH,
) -> dict[str, Any]:
    """Rehash and structurally replay every R12 input artifact."""

    _require(
        manifest_path.resolve() == MANIFEST_PATH.resolve(),
        "R12 importer refuses a mutable manifest alias",
    )
    _verify_file_binding(
        manifest_path, EXPECTED_MANIFEST_SHA256, "R12 manifest"
    )
    manifest = _read_json(manifest_path)
    _require(
        manifest.get("schema")
        == "twisted-yetter.computation-artifact-import-manifest.v1"
        and manifest.get("status") == "R12_IMPORT_MANIFEST_FROZEN",
        "R12 manifest schema or status changed",
    )
    rows = manifest.get("figure21_rows")
    _require(
        isinstance(rows, list)
        and len(rows) == len(EXPECTED_ROWS)
        and {row.get("realization_id") for row in rows}
        == set(EXPECTED_ROWS),
        "Figure 21 row denominator changed",
    )

    exact_control = _validate_exact_control(manifest["exact_control"])
    figure21 = _validate_figure21_identity(manifest["figure21"])
    batch_spec = manifest["figure21_pointed_batch"]
    batch_path = _repo_path(str(batch_spec["path"]))
    batch = _read_json(batch_path)
    _verify_file_binding(
        batch_path, str(batch_spec["file_sha256"]), "Figure 21 pointed batch"
    )
    _verify_content_hash(
        batch, "content_hash", "Figure 21 pointed batch", tagged=True
    )
    _require(
        batch.get("content_hash") == batch_spec["content_hash"]
        and batch.get("status") == batch_spec["expected_status"]
        and batch.get("complete_row_count") == len(EXPECTED_ROWS)
        and batch.get("blocked_row_count") == 0,
        "Figure 21 pointed-batch binding changed",
    )
    batch_rows = {
        row["realization_id"]: row for row in batch.get("rows", [])
    }
    _require(
        set(batch_rows) == set(EXPECTED_ROWS),
        "Figure 21 batch silently lost or added a row",
    )

    rank2_path = _repo_path(str(rows[0]["source_path"]))
    rank2_source = _read_json(rank2_path)
    _verify_file_binding(
        rank2_path, str(rows[0]["source_sha256"]), "rank-2 source"
    )
    _require(
        rank2_source.get("status")
        == "PASS_FIGURE21_RANK2_SEMION_MODULAR_FULL_SECTOR_EVALUATION",
        "rank-2 full evaluator source is not terminal pass",
    )

    imported_rows: list[dict[str, Any]] = []
    for spec in rows:
        realization_id = str(spec["realization_id"])
        expected_rank, expected_sectors = EXPECTED_ROWS[realization_id]
        _require(
            spec.get("rank") == expected_rank
            and spec.get("expected_sector_count") == expected_sectors,
            f"{realization_id} rank or denominator changed",
        )
        snapshot = _validate_snapshot(spec)
        if spec["source_kind"] == "aggregate":
            source = _validate_aggregate_row(
                spec, batch_rows[realization_id]
            )
        elif spec["source_kind"] == "rank2_full_evaluation":
            source = _validate_rank2_row(
                spec, batch_rows[realization_id], rank2_source
            )
        else:
            raise ValueError(
                f"{realization_id} has unknown source kind "
                f"{spec['source_kind']!r}"
            )
        imported_rows.append(
            {
                "realization_id": realization_id,
                "rank": expected_rank,
                "snapshot": snapshot,
                **source,
            }
        )

    imported_rows.sort(key=lambda row: (row["rank"], row["realization_id"]))
    chunk_count = sum(row["chunk_count"] for row in imported_rows)
    sector_count = sum(
        row["observed_sector_count"] for row in imported_rows
    )
    _require(
        chunk_count == EXPECTED_CHUNK_ARTIFACTS,
        "Figure 21 chunk artifact denominator changed",
    )
    _require(
        sector_count == EXPECTED_TOTAL_SECTORS,
        "Figure 21 total sector denominator changed",
    )
    _require(
        any(row["recorded_dirty"] for row in imported_rows)
        and all(row["snapshot"]["recorded_dirty"] for row in imported_rows),
        "Figure 21 dirty provenance blocker was hidden",
    )

    comparisons = _validate_comparisons(
        manifest["comparison_artifacts"]
    )
    entry_points = _validate_entry_points(
        manifest["pointed_evaluator_entry_points"]
    )
    _require(
        tuple(manifest.get("known_blockers", ())) == KNOWN_BLOCKERS,
        "R12 blocker denominator changed",
    )
    payload: dict[str, Any] = {
        "schema": RUNTIME_SCHEMA,
        "status": RUNTIME_STATUS,
        "manifest_file_sha256": EXPECTED_MANIFEST_SHA256,
        "exact_control": exact_control,
        "figure21_identity": figure21,
        "figure21_structural_batch": {
            "status": STRUCTURAL_STATUS,
            "batch_path": str(batch_path.relative_to(REPO_ROOT)),
            "batch_file_sha256": file_sha256(batch_path),
            "batch_content_hash": batch["content_hash"],
            "row_count": len(imported_rows),
            "expected_total_sector_count": EXPECTED_TOTAL_SECTORS,
            "observed_total_sector_count": sector_count,
            "chunk_artifact_count": chunk_count,
            "arithmetic_mode": "ROUNDED_COMPLEX",
            "source_provenance_clean": False,
            "evaluator_source_closure_sealed": False,
            "concrete_r11_semantic_binding": False,
            "mutable_alias_count": 0,
            "rows": imported_rows,
        },
        "comparison_import": comparisons,
        "evaluator_entry_points": entry_points,
        "admission": {
            "exact_control_disposition": "ADMITTED_EXACT_CONTROL_ONLY",
            "figure21_disposition": BLOCKED_STATUS,
            "figure21_exact_value_admitted": False,
            "figure21_exoticness_comparison_admitted": False,
            "blockers": list(KNOWN_BLOCKERS),
        },
        "claim_boundary": {
            "established": (
                "The R12 importer works; the R11 exact fixture is admitted; "
                "all 15 Figure 21 pointed denominator packages are "
                "content-addressed and structurally complete."
            ),
            "not_established": (
                "No Figure 21 output is promoted to an exact R11 invariant "
                "value or a marked exotic-vs-standard comparison."
            ),
        },
    }
    payload["content_hash"] = canonical_hash(payload)
    validate_computation_import_runtime(payload)
    return payload


def validate_computation_import_runtime(payload: Mapping[str, Any]) -> None:
    """Validate an already materialized R12 runtime certificate."""

    expected_keys = {
        "schema",
        "status",
        "manifest_file_sha256",
        "exact_control",
        "figure21_identity",
        "figure21_structural_batch",
        "comparison_import",
        "evaluator_entry_points",
        "admission",
        "claim_boundary",
        "content_hash",
    }
    _require(set(payload) == expected_keys, "R12 runtime schema mismatch")
    _require(
        payload.get("content_hash") == canonical_hash(payload),
        "R12 runtime content hash is stale",
    )
    _require(
        payload.get("schema") == RUNTIME_SCHEMA
        and payload.get("status") == RUNTIME_STATUS,
        "R12 runtime status mismatch",
    )
    _require(
        payload.get("manifest_file_sha256") == EXPECTED_MANIFEST_SHA256,
        "R12 runtime manifest binding changed",
    )

    exact = payload["exact_control"]
    _require(
        exact.get("status") == EXACT_CONTROL_STATUS
        and exact.get("source_clean") is True
        and exact.get("mutable_alias_count") == 0
        and exact.get("inconclusive_count") == 0
        and exact.get("arithmetic_mode") == "EXACT_RATIONAL"
        and exact.get("r11_semantic_binding") is True
        and exact.get("marked_class_count") == 4,
        "R12 exact-control admission requirements failed",
    )
    _require(
        exact.get("exact_value") == {"numerator": 101, "denominator": 450},
        "R12 exact-control value binding changed",
    )
    for key in ("file_sha256", "content_hash"):
        _require(_is_sha256(exact.get(key)), f"R12 exact {key} malformed")

    figure = payload["figure21_identity"]
    _require(
        figure.get("diagram_file_sha256") == FIGURE21_INPUT_SHA256
        and figure.get("projected_ir_hash") == FIGURE21_PROJECTED_IR_HASH
        and figure.get("coupon_graph_hash") == FIGURE21_COUPON_GRAPH_HASH
        and figure.get("source_status")
        == "DRAFT_USER_TRANSCRIPTION_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM"
        and figure.get("diagram_certified_against_printed_source") is False,
        "R12 Figure 21 identity or draft blocker changed",
    )

    batch = payload["figure21_structural_batch"]
    _require(
        batch.get("status") == STRUCTURAL_STATUS
        and batch.get("row_count") == len(EXPECTED_ROWS)
        and batch.get("expected_total_sector_count")
        == EXPECTED_TOTAL_SECTORS
        and batch.get("observed_total_sector_count")
        == EXPECTED_TOTAL_SECTORS
        and batch.get("chunk_artifact_count")
        == EXPECTED_CHUNK_ARTIFACTS
        and batch.get("arithmetic_mode") == "ROUNDED_COMPLEX"
        and batch.get("source_provenance_clean") is False
        and batch.get("evaluator_source_closure_sealed") is False
        and batch.get("concrete_r11_semantic_binding") is False
        and batch.get("mutable_alias_count") == 0,
        "R12 Figure 21 structural boundary changed",
    )
    rows = batch.get("rows")
    _require(
        isinstance(rows, list)
        and {row.get("realization_id") for row in rows}
        == set(EXPECTED_ROWS),
        "R12 Figure 21 row denominator is incomplete",
    )
    observed_total = 0
    observed_chunks = 0
    snapshot_hashes: set[str] = set()
    category_hashes: set[str] = set()
    for row in rows:
        realization_id = row["realization_id"]
        rank, expected = EXPECTED_ROWS[realization_id]
        _require(
            row.get("rank") == rank
            and row.get("expected_sector_count") == expected
            and row.get("observed_sector_count") == expected,
            f"{realization_id} runtime denominator mismatch",
        )
        for key in (
            "value_distribution",
            "status_distribution",
            "projector_rank_distribution",
        ):
            _require(
                _sum_distribution(row.get(key), f"{realization_id} {key}")
                == expected,
                f"{realization_id} runtime {key} is incomplete",
            )
        snapshot = row.get("snapshot")
        _require(
            snapshot.get("mutable_alias_count") == 0
            and snapshot.get("recorded_dirty") is True,
            f"{realization_id} snapshot provenance boundary changed",
        )
        snapshot_hash = snapshot.get("content_hash")
        category_hash = snapshot.get("category_data_hash")
        _require(
            _is_sha256(snapshot_hash) and _is_sha256(category_hash),
            f"{realization_id} snapshot hash malformed",
        )
        _require(
            snapshot_hash not in snapshot_hashes
            and category_hash not in category_hashes,
            f"{realization_id} duplicate category identity",
        )
        snapshot_hashes.add(snapshot_hash)
        category_hashes.add(category_hash)
        _require(
            row.get("source_snapshot_content_hash") == snapshot_hash
            and row.get("source_category_data_hash") == category_hash,
            f"{realization_id} source/snapshot binding changed",
        )
        chunks = row.get("chunk_records")
        chunk_count = row.get("chunk_count")
        _require(
            isinstance(chunks, list)
            and isinstance(chunk_count, int)
            and len(chunks) == chunk_count,
            f"{realization_id} runtime chunk denominator changed",
        )
        if row.get("source_kind") == "aggregate":
            _require(
                chunk_count > 0,
                f"{realization_id} aggregate has no chunks",
            )
            previous_end = 0
            for chunk_id, chunk in enumerate(chunks):
                start, end = _chunk_bounds(expected, chunk_count, chunk_id)
                _require(
                    chunk.get("chunk_id") == chunk_id
                    and chunk.get("start_sector_id") == start
                    and chunk.get("end_sector_id_exclusive") == end
                    and chunk.get("sector_count") == end - start
                    and start == previous_end
                    and _is_sha256(
                        chunk.get("content_sha256"), tagged=False
                    ),
                    f"{realization_id} runtime chunk range/hash mismatch",
                )
                previous_end = end
            _require(
                previous_end == expected,
                f"{realization_id} runtime chunks do not cover denominator",
            )
        elif row.get("source_kind") == "rank2_full_evaluation":
            _require(
                chunk_count == 0
                and chunks == []
                and _is_sha256(
                    row.get("sector_records_sha256"), tagged=False
                )
                and row.get("modular_pointed_max_abs_error") == 0.0,
                f"{realization_id} rank-2 full record binding changed",
            )
        else:
            raise ValueError(f"{realization_id} runtime source kind invalid")
        observed_total += expected
        observed_chunks += chunk_count
    _require(
        observed_total == EXPECTED_TOTAL_SECTORS
        and observed_chunks == EXPECTED_CHUNK_ARTIFACTS,
        "R12 aggregate denominator totals changed",
    )

    comparison = payload["comparison_import"]
    _require(
        comparison.get("artifact_count") == 3
        and len(comparison.get("records", [])) == 3
        and comparison.get("marked_h2_comparison_ready") is False,
        "R12 comparison boundary changed",
    )
    admission = payload["admission"]
    _require(
        admission.get("exact_control_disposition")
        == "ADMITTED_EXACT_CONTROL_ONLY"
        and admission.get("figure21_disposition") == BLOCKED_STATUS
        and admission.get("figure21_exact_value_admitted") is False
        and admission.get("figure21_exoticness_comparison_admitted") is False
        and tuple(admission.get("blockers", ())) == KNOWN_BLOCKERS,
        "R12 Figure 21 exact-admission blockers changed",
    )


__all__ = [
    "BLOCKED_STATUS",
    "EXPECTED_CHUNK_ARTIFACTS",
    "EXPECTED_ROWS",
    "EXPECTED_TOTAL_SECTORS",
    "KNOWN_BLOCKERS",
    "RUNTIME_SCHEMA",
    "RUNTIME_STATUS",
    "build_computation_import_runtime",
    "canonical_hash",
    "file_sha256",
    "validate_computation_import_runtime",
]
