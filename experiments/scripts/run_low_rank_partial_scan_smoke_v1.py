#!/usr/bin/env python3
"""Run the smallest nontrivial universal-character partial-scan smoke probe.

This is a runtime probe, not formal scan evidence.  It uses only the admitted
rank2 cyclic Z2 pointed semion snapshots and tiny toy diagrams.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import (  # noqa: E402
    stable_content_hash,
    validate_formal_evidence,
)
from twisted_yetter.link_diagram import LinkDiagram  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
TOY_DIR = REPO_ROOT / "experiments" / "inputs" / "toy-diagrams"
RULE = OUT_DIR / "low-rank-nontrivial-partial-scan-rule-v1.json"

SMOKE_SNAPSHOTS = [
    SNAPSHOT_DIR / "rank2-cyclic-z2-semion-plus-snapshot-v1.json",
    SNAPSHOT_DIR / "rank2-cyclic-z2-semion-minus-snapshot-v1.json",
]
SMOKE_DIAGRAMS = [
    TOY_DIR / "s4-empty.json",
    TOY_DIR / "cp2-plus-one-framed-unknot.json",
    TOY_DIR / "hopf-link.json",
]


@dataclass(frozen=True)
class GI:
    real: int = 0
    imag: int = 0

    def __add__(self, other: "GI") -> "GI":
        return GI(self.real + other.real, self.imag + other.imag)

    def __mul__(self, other: "GI") -> "GI":
        return GI(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )

    def to_json(self) -> dict[str, int | str]:
        if self.imag == 0:
            display = str(self.real)
        elif self.real == 0:
            display = f"{self.imag}i"
        else:
            sign = "+" if self.imag > 0 else ""
            display = f"{self.real}{sign}{self.imag}i"
        return {"real": self.real, "imag": self.imag, "display": display}


ONE = GI(1, 0)
MINUS_ONE = GI(-1, 0)
I = GI(0, 1)
MINUS_I = GI(0, -1)


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def git_output(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def file_sha256_id(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def with_hash(payload: dict[str, Any]) -> dict[str, Any]:
    result = dict(payload)
    result.pop("content_hash", None)
    result["content_hash"] = stable_content_hash(result)
    return result


def artifact_record(path: Path, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    record = {"path": str(path.relative_to(REPO_ROOT)), "sha256": file_sha256_id(path)}
    if payload is not None:
        record["content_hash"] = payload.get("content_hash", stable_content_hash(payload))
        record["status"] = payload["status"]
    return record


def twist_value(snapshot: dict[str, Any], label: int) -> GI:
    if label == 0:
        return ONE
    value = snapshot["category_data"]["twists"]["1"]
    if value == "i":
        return I
    if value == "-i":
        return MINUS_I
    raise ValueError(f"unsupported Z2 twist value: {value!r}")


def gi_pow(value: GI, exponent: int) -> GI:
    if exponent < 0:
        if value == I:
            return gi_pow(MINUS_I, -exponent)
        if value == MINUS_I:
            return gi_pow(I, -exponent)
        if value == MINUS_ONE:
            return gi_pow(MINUS_ONE, -exponent)
        if value == ONE:
            return ONE
        raise ValueError("unsupported negative exponent")
    result = ONE
    for _ in range(exponent):
        result = result * value
    return result


def z2_character(label: int, character_power: int) -> GI:
    if character_power % 2 == 0:
        return ONE
    return MINUS_ONE if label == 1 else ONE


def labels(component_count: int) -> list[tuple[int, ...]]:
    if component_count == 0:
        return [()]
    out = [()]
    for _ in range(component_count):
        out = [prefix + (label,) for prefix in out for label in (0, 1)]
    return out


def linking_matrix(diagram: LinkDiagram) -> tuple[tuple[int, ...], ...]:
    return diagram.linking_matrix()


def evaluate_pointed_z2(
    *,
    snapshot: dict[str, Any],
    diagram: LinkDiagram,
    character_assignment: tuple[int, ...],
) -> dict[str, Any]:
    components = diagram.components
    matrix = linking_matrix(diagram)
    total = GI()
    sectors = []
    for label_tuple in labels(len(components)):
        term = ONE
        for idx, label in enumerate(label_tuple):
            term = term * gi_pow(twist_value(snapshot, label), components[idx].framing)
            term = term * z2_character(label, character_assignment[idx])
        for i in range(len(label_tuple)):
            for j in range(i + 1, len(label_tuple)):
                if label_tuple[i] == 1 and label_tuple[j] == 1:
                    term = term * gi_pow(MINUS_ONE, matrix[i][j])
        total = total + term
        sectors.append(
            {
                "labels": list(label_tuple),
                "term": term.to_json(),
            }
        )
    return {
        "diagram_id": diagram.diagram_id,
        "component_ids": list(diagram.component_ids),
        "character_assignment": list(character_assignment),
        "sector_count": len(sectors),
        "linking_matrix": [list(row) for row in matrix],
        "total": total.to_json(),
        "sectors": sectors,
    }


def character_assignments(diagram: LinkDiagram) -> list[tuple[int, ...]]:
    count = len(diagram.components)
    if count == 0:
        return [()]
    zero = tuple(0 for _ in range(count))
    simplest_nontrivial = (1,) + tuple(0 for _ in range(count - 1))
    return [zero] if simplest_nontrivial == zero else [zero, simplest_nontrivial]


def case_id(case_payload: dict[str, Any]) -> str:
    return "partial-smoke-" + stable_content_hash(case_payload).removeprefix("sha256:")[:24]


def run_smoke(*, started_at_utc: str) -> dict[str, Any]:
    rule = load_json(RULE)
    if "rank2-cyclic-z2" not in rule["admitted_resolved_nontrivial_family_ids"]:
        raise RuntimeError("rank2-cyclic-z2 is not admitted by the partial rule")

    snapshots = [load_json(path) for path in SMOKE_SNAPSHOTS]
    for snapshot in snapshots:
        validate_formal_evidence(snapshot)
        if snapshot["family_id"] != "rank2-cyclic-z2":
            raise RuntimeError("smoke snapshot outside rank2-cyclic-z2")

    case_results = []
    t0 = time.perf_counter()
    for snapshot_path, snapshot in zip(SMOKE_SNAPSHOTS, snapshots, strict=True):
        for diagram_path in SMOKE_DIAGRAMS:
            diagram_payload = load_json(diagram_path)
            diagram = LinkDiagram.from_json(diagram_payload)
            for assignment in character_assignments(diagram):
                case_started = time.perf_counter()
                result = evaluate_pointed_z2(
                    snapshot=snapshot,
                    diagram=diagram,
                    character_assignment=assignment,
                )
                elapsed_ms = (time.perf_counter() - case_started) * 1000
                pinned_inputs = {
                    "category_snapshot": snapshot["content_hash"],
                    "category_snapshot_file": file_sha256_id(snapshot_path),
                    "diagram_file": file_sha256_id(diagram_path),
                    "character_assignment": stable_content_hash(
                        {"character_assignment": list(assignment)}
                    ),
                }
                body = {
                    "snapshot_id": snapshot["realization_id"],
                    "diagram_id": diagram.diagram_id,
                    "character_assignment": list(assignment),
                    "pinned_inputs": pinned_inputs,
                }
                case_results.append(
                    {
                        "case_id": case_id(body),
                        "status": "PASS_RUNTIME_SMOKE",
                        "elapsed_ms": elapsed_ms,
                        "input_hashes": pinned_inputs,
                        "result": result,
                    }
                )
    elapsed_total_ms = (time.perf_counter() - t0) * 1000

    max_elapsed_ms = max(item["elapsed_ms"] for item in case_results)
    checks = {
        "partial_rule_pinned": rule["content_hash"].startswith("sha256:"),
        "rank2_z2_only": all(
            item["result"]["diagram_id"] in {
                "s4-empty-kirby-diagram",
                "cp2-plus-one-framed-unknot",
                "hopf-linking-1",
            }
            for item in case_results
        ),
        "all_cases_passed": all(item["status"] == "PASS_RUNTIME_SMOKE" for item in case_results),
        "no_formal_scan_evidence_claimed": True,
    }
    if not all(checks.values()):
        raise RuntimeError(f"smoke checks failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.low-rank-nontrivial-partial-scan-smoke.v1",
            "status": "PASS_RUNTIME_SMOKE_FAST",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/run_low_rank_partial_scan_smoke_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/run_low_rank_partial_scan_smoke_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "claim_level": "runtime-smoke-preformal",
            "source_status": "preformal-runtime-smoke-not-formal-scan-evidence",
            "smoke_id": "low-rank-nontrivial-partial-scan-smoke-v1",
            "input_artifacts": {
                "partial_scan_rule": artifact_record(RULE, rule),
                "snapshots": [
                    artifact_record(path, snapshot)
                    for path, snapshot in zip(SMOKE_SNAPSHOTS, snapshots, strict=True)
                ],
                "diagrams": [artifact_record(path) for path in SMOKE_DIAGRAMS],
            },
            "scope": {
                "family_ids": ["rank2-cyclic-z2"],
                "snapshot_ids": [snapshot["realization_id"] for snapshot in snapshots],
                "diagram_ids": sorted({item["result"]["diagram_id"] for item in case_results}),
                "formal_partial_scan_plan_used": False,
                "formal_scan_case_result_produced": False,
            },
            "timing": {
                "case_count": len(case_results),
                "elapsed_total_ms": elapsed_total_ms,
                "max_case_elapsed_ms": max_elapsed_ms,
            },
            "case_results": case_results,
            "checks": checks,
            "explicit_non_claims": [
                "This smoke artifact is not a partial_scan_plan.",
                "This smoke artifact is not a scan_case_result.",
                "This smoke artifact is not a scan_aggregate.",
                "This smoke artifact does not claim no signal.",
                "This smoke artifact only probes the smallest rank2-cyclic-z2 toy cases.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "low-rank-nontrivial-partial-scan-smoke-v1.json": run_smoke(
            started_at_utc=started_at_utc
        )
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    artifacts = build_all()
    if args.write:
        for name, payload in artifacts.items():
            write_json(OUT_DIR / name, payload)
    else:
        print(json.dumps(artifacts, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
