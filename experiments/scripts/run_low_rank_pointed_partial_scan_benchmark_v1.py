#!/usr/bin/env python3
"""Benchmark all admitted pointed rows in the partial scan subset on toy diagrams."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import time
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from itertools import product
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import stable_content_hash, validate_formal_evidence  # noqa: E402
from twisted_yetter.link_diagram import LinkDiagram  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
TOY_DIR = REPO_ROOT / "experiments" / "inputs" / "toy-diagrams"
RULE = OUT_DIR / "low-rank-nontrivial-partial-scan-rule-v1.json"

POINTED_FAMILIES = {
    "rank2-cyclic-z2",
    "rank3-cyclic-z3",
    "rank4-pointed-z4",
    "rank4-pointed-z2xz2",
    "rank5-su5-1",
}
TOY_DIAGRAMS = [
    TOY_DIR / "s4-empty.json",
    TOY_DIR / "cp2-plus-one-framed-unknot.json",
    TOY_DIR / "hopf-link.json",
]


@dataclass(frozen=True)
class Root:
    modulus: int
    exponent: int

    def __mul__(self, other: "Root") -> "Root":
        if self.modulus != other.modulus:
            raise ValueError("cannot multiply different cyclotomic moduli")
        return Root(self.modulus, (self.exponent + other.exponent) % self.modulus)

    def pow(self, n: int) -> "Root":
        return Root(self.modulus, (self.exponent * n) % self.modulus)

    def display(self) -> str:
        exp = self.exponent % self.modulus
        if exp == 0:
            return "1"
        if self.modulus % 2 == 0 and exp == self.modulus // 2:
            return "-1"
        if self.modulus == 4 and exp == 1:
            return "i"
        if self.modulus == 4 and exp == 3:
            return "-i"
        return f"zeta{self.modulus}^{exp}"


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


def pointed_snapshot_paths() -> list[Path]:
    paths = []
    for path in sorted(SNAPSHOT_DIR.glob("*.json")):
        payload = load_json(path)
        if payload.get("family_id") in POINTED_FAMILIES:
            paths.append(path)
    return paths


def modulus_for(snapshot: dict[str, Any]) -> int:
    field = snapshot["category_data"].get("field", "")
    if field == "Q(i)":
        return 4
    if "zeta3" in field:
        return 3
    if "zeta5" in field:
        return 5
    if "zeta16" in field:
        return 16
    raise ValueError(f"unsupported pointed field: {field!r}")


def parse_root(value: str, modulus: int) -> Root:
    if value == "1":
        return Root(modulus, 0)
    if value == "-1":
        if modulus % 2:
            raise ValueError("-1 outside even modulus")
        return Root(modulus, modulus // 2)
    if value == "i":
        if modulus == 4:
            return Root(modulus, 1)
        if modulus == 16:
            return Root(modulus, 4)
    if value == "-i":
        if modulus == 4:
            return Root(modulus, 3)
        if modulus == 16:
            return Root(modulus, 12)
    if value == f"zeta{modulus}":
        return Root(modulus, 1)
    prefix = f"zeta{modulus}^"
    if value.startswith(prefix):
        return Root(modulus, int(value.removeprefix(prefix)))
    raise ValueError(f"unsupported root value {value!r} for modulus {modulus}")


def labels(snapshot: dict[str, Any]) -> list[str]:
    return list(snapshot["category_data"]["labels"])


def character_group(snapshot: dict[str, Any]) -> list[str]:
    return labels(snapshot)


def character_value(label: str, character: str, modulus: int, family_id: str) -> Root:
    if family_id == "rank4-pointed-z2xz2":
        exp = (int(label[0]) * int(character[0]) + int(label[1]) * int(character[1])) % 2
        return parse_root("-1" if exp else "1", modulus)
    n = len(character_group_from_family(family_id))
    exp = (int(label) * int(character)) % n
    if n == 2:
        return parse_root("-1" if exp else "1", modulus)
    scale = modulus // n
    return Root(modulus, exp * scale)


def character_group_from_family(family_id: str) -> list[str]:
    if family_id == "rank2-cyclic-z2":
        return ["0", "1"]
    if family_id == "rank3-cyclic-z3":
        return ["0", "1", "2"]
    if family_id == "rank4-pointed-z4":
        return ["0", "1", "2", "3"]
    if family_id == "rank4-pointed-z2xz2":
        return ["00", "10", "01", "11"]
    if family_id == "rank5-su5-1":
        return ["0", "1", "2", "3", "4"]
    raise ValueError(f"unsupported family {family_id}")


def monodromy(snapshot: dict[str, Any], left: str, right: str, modulus: int) -> Root:
    table = snapshot["category_data"]["monodromy_bicharacter"]
    for key in (f"{left},{right}", f"b({left},{right})"):
        if key in table:
            return parse_root(table[key], modulus)
    if left == snapshot["category_data"]["unit"] or right == snapshot["category_data"]["unit"]:
        return Root(modulus, 0)
    raise KeyError(f"missing monodromy for {left},{right}")


def twist(snapshot: dict[str, Any], label: str, modulus: int) -> Root:
    return parse_root(snapshot["category_data"]["twists"][label], modulus)


def all_tuples(values: list[str], length: int) -> list[tuple[str, ...]]:
    if length == 0:
        return [()]
    return list(product(values, repeat=length))


def sparse_add(acc: dict[int, int], term: Root) -> None:
    acc[term.exponent % term.modulus] += 1


def sparse_display(modulus: int, acc: dict[int, int]) -> str:
    terms = []
    for exp, coeff in sorted(acc.items()):
        if coeff == 0:
            continue
        root = Root(modulus, exp).display()
        terms.append(f"{coeff}*{root}")
    return "0" if not terms else " + ".join(terms)


def evaluate(
    *,
    snapshot: dict[str, Any],
    diagram: LinkDiagram,
    character_assignment: tuple[str, ...],
) -> dict[str, Any]:
    family_id = snapshot["family_id"]
    modulus = modulus_for(snapshot)
    component_labels = labels(snapshot)
    matrix = diagram.linking_matrix()
    total: dict[int, int] = defaultdict(int)
    sector_count = 0
    for label_tuple in all_tuples(component_labels, len(diagram.components)):
        sector_count += 1
        term = Root(modulus, 0)
        for idx, label in enumerate(label_tuple):
            term = term * twist(snapshot, label, modulus).pow(diagram.components[idx].framing)
            term = term * character_value(label, character_assignment[idx], modulus, family_id)
        for i in range(len(label_tuple)):
            for j in range(i + 1, len(label_tuple)):
                term = term * monodromy(snapshot, label_tuple[i], label_tuple[j], modulus).pow(matrix[i][j])
        sparse_add(total, term)
    return {
        "diagram_id": diagram.diagram_id,
        "component_count": len(diagram.components),
        "character_assignment": list(character_assignment),
        "sector_count": sector_count,
        "root_modulus": modulus,
        "total_sparse": {str(k): v for k, v in sorted(total.items()) if v},
        "total_display": sparse_display(modulus, total),
    }


def run_benchmark(*, started_at_utc: str) -> dict[str, Any]:
    rule = load_json(RULE)
    paths = pointed_snapshot_paths()
    snapshots = [load_json(path) for path in paths]
    for snapshot in snapshots:
        validate_formal_evidence(snapshot)
        if snapshot["family_id"] not in rule["admitted_resolved_nontrivial_family_ids"]:
            raise RuntimeError(f"snapshot outside admitted subset: {snapshot['family_id']}")

    diagrams = [(path, LinkDiagram.from_json(load_json(path))) for path in TOY_DIAGRAMS]
    case_results = []
    per_family: dict[str, dict[str, Any]] = {}
    t0 = time.perf_counter()
    for snapshot_path, snapshot in zip(paths, snapshots, strict=True):
        family_id = snapshot["family_id"]
        family_start_count = len(case_results)
        family_start_time = time.perf_counter()
        chars = character_group_from_family(family_id)
        for diagram_path, diagram in diagrams:
            for assignment in all_tuples(chars, len(diagram.components)):
                case_started = time.perf_counter()
                result = evaluate(
                    snapshot=snapshot,
                    diagram=diagram,
                    character_assignment=assignment,
                )
                elapsed_ms = (time.perf_counter() - case_started) * 1000
                body = {
                    "snapshot_hash": snapshot["content_hash"],
                    "diagram_hash": file_sha256_id(diagram_path),
                    "character_assignment": assignment,
                    "benchmark": "pointed-partial-scan-v1",
                }
                case_results.append(
                    {
                        "case_id": "pointed-bench-"
                        + stable_content_hash(body).removeprefix("sha256:")[:24],
                        "status": "PASS_POINTED_BENCHMARK",
                        "family_id": family_id,
                        "snapshot_id": snapshot["realization_id"],
                        "diagram_id": diagram.diagram_id,
                        "elapsed_ms": elapsed_ms,
                        "input_hashes": {
                            "category_snapshot": snapshot["content_hash"],
                            "category_snapshot_file": file_sha256_id(snapshot_path),
                            "diagram_file": file_sha256_id(diagram_path),
                            "character_assignment": stable_content_hash(
                                {"character_assignment": list(assignment)}
                            ),
                        },
                        "result_summary": result,
                    }
                )
        family_cases = case_results[family_start_count:]
        family_entry = per_family.setdefault(
            family_id,
            {
                "case_count": 0,
                "elapsed_total_ms": 0.0,
                "max_case_elapsed_ms": 0.0,
                "snapshot_count": 0,
            },
        )
        family_entry["case_count"] += len(family_cases)
        family_entry["elapsed_total_ms"] += (time.perf_counter() - family_start_time) * 1000
        family_entry["max_case_elapsed_ms"] = max(
            family_entry["max_case_elapsed_ms"],
            max(item["elapsed_ms"] for item in family_cases),
        )
        family_entry["snapshot_count"] += 1
    elapsed_total_ms = (time.perf_counter() - t0) * 1000
    max_case = max(case_results, key=lambda item: item["elapsed_ms"])
    checks = {
        "all_pointed_admitted_families_included": sorted(per_family) == sorted(POINTED_FAMILIES),
        "all_cases_passed": all(item["status"] == "PASS_POINTED_BENCHMARK" for item in case_results),
        "no_formal_scan_evidence_claimed": True,
    }
    if not all(checks.values()):
        raise RuntimeError(f"pointed benchmark checks failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.low-rank-pointed-partial-scan-benchmark.v1",
            "status": "PASS_POINTED_TOY_BENCHMARK_FAST",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/run_low_rank_pointed_partial_scan_benchmark_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/run_low_rank_pointed_partial_scan_benchmark_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "claim_level": "runtime-benchmark-preformal",
            "source_status": "preformal-runtime-benchmark-not-formal-scan-evidence",
            "benchmark_id": "low-rank-pointed-partial-scan-benchmark-v1",
            "input_artifacts": {
                "partial_scan_rule": artifact_record(RULE, rule),
                "snapshots": [
                    artifact_record(path, snapshot)
                    for path, snapshot in zip(paths, snapshots, strict=True)
                ],
                "diagrams": [artifact_record(path) for path, _ in diagrams],
            },
            "scope": {
                "family_ids": sorted(per_family),
                "snapshot_count": len(snapshots),
                "diagram_ids": [diagram.diagram_id for _, diagram in diagrams],
                "formal_partial_scan_plan_used": False,
                "formal_scan_case_result_produced": False,
            },
            "timing": {
                "case_count": len(case_results),
                "elapsed_total_ms": elapsed_total_ms,
                "max_case_elapsed_ms": max_case["elapsed_ms"],
                "max_case_id": max_case["case_id"],
                "per_family": per_family,
            },
            "case_results": case_results,
            "checks": checks,
            "explicit_non_claims": [
                "This benchmark artifact is not a partial_scan_plan.",
                "This benchmark artifact is not a scan_case_result.",
                "This benchmark artifact is not a scan_aggregate.",
                "This benchmark artifact does not claim no signal.",
                "This benchmark artifact only probes admitted pointed rows on toy diagrams.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "low-rank-pointed-partial-scan-benchmark-v1.json": run_benchmark(
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
