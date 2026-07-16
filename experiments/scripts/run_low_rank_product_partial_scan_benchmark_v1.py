#!/usr/bin/env python3
"""Benchmark the admitted Semion x Fib/Yang-Lee product row on toy diagrams.

This is still a preformal runtime benchmark, not a formal scan case result.
The evaluator is deliberately narrow: it supports only the current toy
diagrams with 0, 1, or 2 components, and only the pinned
rank4-semion-times-fibonacci Deligne product snapshots.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import re
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
PRODUCT_SURFACE_PROBE = OUT_DIR / "low-rank-product-partial-scan-surface-probe-v1.json"

PRODUCT_FAMILY = "rank4-semion-times-fibonacci"
PRODUCT_CHARACTER_GROUP = ["0", "1"]
TOY_DIAGRAMS = [
    TOY_DIR / "s4-empty.json",
    TOY_DIR / "cp2-plus-one-framed-unknot.json",
    TOY_DIR / "hopf-link.json",
]


@dataclass(frozen=True)
class CyclotomicSparse:
    """Sparse integer combination of powers of zeta_20."""

    terms: tuple[tuple[int, int], ...]

    @classmethod
    def zero(cls) -> "CyclotomicSparse":
        return cls(())

    @classmethod
    def one(cls) -> "CyclotomicSparse":
        return cls.monomial(0)

    @classmethod
    def monomial(cls, exponent: int, coefficient: int = 1) -> "CyclotomicSparse":
        return cls._normalize({exponent % 20: coefficient})

    @classmethod
    def _normalize(cls, raw: dict[int, int]) -> "CyclotomicSparse":
        return cls(tuple(sorted((exp % 20, coeff) for exp, coeff in raw.items() if coeff)))

    def __add__(self, other: "CyclotomicSparse") -> "CyclotomicSparse":
        raw: dict[int, int] = defaultdict(int)
        for exp, coeff in self.terms:
            raw[exp] += coeff
        for exp, coeff in other.terms:
            raw[exp] += coeff
        return CyclotomicSparse._normalize(raw)

    def __neg__(self) -> "CyclotomicSparse":
        return CyclotomicSparse(tuple((exp, -coeff) for exp, coeff in self.terms))

    def __sub__(self, other: "CyclotomicSparse") -> "CyclotomicSparse":
        return self + (-other)

    def __mul__(self, other: "CyclotomicSparse") -> "CyclotomicSparse":
        raw: dict[int, int] = defaultdict(int)
        for left_exp, left_coeff in self.terms:
            for right_exp, right_coeff in other.terms:
                raw[(left_exp + right_exp) % 20] += left_coeff * right_coeff
        return CyclotomicSparse._normalize(raw)

    def scale(self, coefficient: int) -> "CyclotomicSparse":
        return CyclotomicSparse(tuple((exp, coeff * coefficient) for exp, coeff in self.terms))

    def pow(self, exponent: int) -> "CyclotomicSparse":
        if exponent < 0:
            return self.inverse_monomial().pow(-exponent)
        result = CyclotomicSparse.one()
        base = self
        power = exponent
        while power:
            if power % 2:
                result = result * base
            base = base * base
            power //= 2
        return result

    def inverse_monomial(self) -> "CyclotomicSparse":
        if len(self.terms) != 1:
            raise ValueError(f"not a monomial unit: {self.display()}")
        exp, coeff = self.terms[0]
        if coeff == 1:
            return CyclotomicSparse.monomial(-exp)
        if coeff == -1:
            return CyclotomicSparse.monomial(-exp, -1)
        raise ValueError(f"not a +/- root-of-unity unit: {self.display()}")

    def display(self) -> str:
        if not self.terms:
            return "0"
        pieces = []
        for exp, coeff in self.terms:
            root = root_display(exp)
            if root == "1":
                atom = str(abs(coeff))
            elif abs(coeff) == 1:
                atom = root
            else:
                atom = f"{abs(coeff)}*{root}"
            sign = "-" if coeff < 0 else "+"
            pieces.append((sign, atom))
        first_sign, first_atom = pieces[0]
        rendered = first_atom if first_sign == "+" else f"-{first_atom}"
        for sign, atom in pieces[1:]:
            rendered += f" {sign} {atom}"
        return rendered

    def to_json(self) -> dict[str, int]:
        return {str(exp): coeff for exp, coeff in self.terms}


def root_display(exponent: int) -> str:
    exp = exponent % 20
    if exp == 0:
        return "1"
    if exp == 10:
        return "-1"
    if exp == 5:
        return "i"
    if exp == 15:
        return "-i"
    if exp % 2 == 0:
        return f"zeta10^{exp // 2}"
    return f"zeta20^{exp}"


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


def product_snapshot_paths() -> list[Path]:
    return sorted(SNAPSHOT_DIR.glob(f"{PRODUCT_FAMILY}-*.json"))


def all_tuples(values: list[str], length: int) -> list[tuple[str, ...]]:
    if length == 0:
        return [()]
    return list(product(values, repeat=length))


def split_top_level_sum(expr: str) -> list[tuple[int, str]]:
    compact = expr.replace(" ", "")
    if not compact:
        raise ValueError("empty expression")
    parts: list[tuple[int, str]] = []
    depth = 0
    sign = 1
    start = 0
    if compact[0] == "-":
        sign = -1
        start = 1
    elif compact[0] == "+":
        start = 1
    term_start = start
    for index in range(start, len(compact)):
        char = compact[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif depth == 0 and char in "+-":
            if term_start == index:
                raise ValueError(f"empty term in {expr!r}")
            parts.append((sign, compact[term_start:index]))
            sign = -1 if char == "-" else 1
            term_start = index + 1
    parts.append((sign, compact[term_start:]))
    return parts


def split_top_level_product(expr: str) -> list[str]:
    parts = []
    depth = 0
    start = 0
    index = 0
    while index < len(expr):
        char = expr[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif depth == 0 and char == "*":
            parts.append(expr[start:index])
            start = index + 1
        index += 1
    parts.append(expr[start:])
    return parts


def strip_wrapping_parentheses(expr: str) -> str:
    while expr.startswith("(") and expr.endswith(")"):
        depth = 0
        wraps = True
        for index, char in enumerate(expr):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(expr) - 1:
                    wraps = False
                    break
        if not wraps:
            return expr
        expr = expr[1:-1]
    return expr


def parse_expr(expr: str) -> CyclotomicSparse:
    expr = strip_wrapping_parentheses(expr.replace(" ", ""))
    sum_parts = split_top_level_sum(expr)
    if len(sum_parts) > 1:
        total = CyclotomicSparse.zero()
        for sign, term in sum_parts:
            total = total + parse_expr(term).scale(sign)
        return total
    sign, atom = sum_parts[0]
    product_parts = split_top_level_product(atom)
    if len(product_parts) > 1:
        total = CyclotomicSparse.one()
        for part in product_parts:
            total = total * parse_expr(part)
        return total.scale(sign)
    return parse_atom(atom).scale(sign)


def parse_atom(atom: str) -> CyclotomicSparse:
    atom = strip_wrapping_parentheses(atom)
    if atom == "1":
        return CyclotomicSparse.one()
    if atom == "i":
        return CyclotomicSparse.monomial(5)
    if atom == "-i":
        return CyclotomicSparse.monomial(5, -1)
    if atom == "-1":
        return CyclotomicSparse.monomial(0, -1)
    if atom == "zeta10":
        return CyclotomicSparse.monomial(2)
    match = re.fullmatch(r"zeta10\^(-?\d+)", atom)
    if match:
        return CyclotomicSparse.monomial(2 * int(match.group(1)))
    if atom == "zeta20":
        return CyclotomicSparse.monomial(1)
    match = re.fullmatch(r"zeta20\^(-?\d+)", atom)
    if match:
        return CyclotomicSparse.monomial(int(match.group(1)))
    raise ValueError(f"unsupported product-row expression atom: {atom!r}")


def row_disposition(rule: dict[str, Any], family_id: str) -> dict[str, Any]:
    rows = {item["family_id"]: item for item in rule["row_dispositions"]}
    return rows[family_id]


def character_projection_contract(snapshot: dict[str, Any]) -> dict[str, Any]:
    data = snapshot["category_data"]
    expected_labels = ["0|1", "0|x", "1|1", "1|x"]
    if data["labels"] != expected_labels:
        raise ValueError(f"unexpected product labels: {data['labels']!r}")
    if data["factor_family_ids"] != ["rank2-cyclic-z2", "rank2-fibonacci-yang-lee"]:
        raise ValueError("unexpected factor family order for product character projection")
    if data["basis_gauge"] != "lexicographic product basis with semion factor first":
        raise ValueError("product basis gauge does not pin semion factor first")
    payload = {
        "schema": "twisted-yetter.product-character-projection-contract.v1",
        "family_id": PRODUCT_FAMILY,
        "universal_group": "Z2",
        "character_group": PRODUCT_CHARACTER_GROUP,
        "projection_name": "semion_factor_first_coordinate",
        "label_to_degree": {
            "0|1": "0",
            "0|x": "0",
            "1|1": "1",
            "1|x": "1",
        },
        "factor_family_ids": data["factor_family_ids"],
        "factor_realization_ids": data["factor_realization_ids"],
        "factor_snapshot_hashes": data["factor_snapshot_hashes"],
        "basis_gauge": data["basis_gauge"],
        "proof_boundary": (
            "This contract is for the pinned Semion x Fib/Yang-Lee product row only; "
            "the worker must use this explicit table, not ad hoc label parsing."
        ),
    }
    payload["content_hash"] = stable_content_hash(payload)
    return payload


def character_value(contract: dict[str, Any], label: str, character: str) -> CyclotomicSparse:
    if character not in PRODUCT_CHARACTER_GROUP:
        raise ValueError(f"unsupported product character {character!r}")
    degree = contract["label_to_degree"][label]
    return CyclotomicSparse.monomial(0, -1) if degree == "1" and character == "1" else CyclotomicSparse.one()


def twist(snapshot: dict[str, Any], label: str) -> CyclotomicSparse:
    return parse_expr(snapshot["category_data"]["twists"][label])


def dimension(snapshot: dict[str, Any], label: str) -> CyclotomicSparse:
    return parse_expr(snapshot["category_data"]["dimensions"][label])


def channel_trace(
    *,
    snapshot: dict[str, Any],
    left: str,
    right: str,
    linking: int,
) -> CyclotomicSparse:
    if linking == 0:
        return dimension(snapshot, left) * dimension(snapshot, right)
    fusion = snapshot["category_data"]["fusion"][f"{left}*{right}"]
    left_twist_inv = twist(snapshot, left).inverse_monomial()
    right_twist_inv = twist(snapshot, right).inverse_monomial()
    total = CyclotomicSparse.zero()
    for channel, multiplicity in fusion.items():
        eigenvalue = twist(snapshot, channel) * left_twist_inv * right_twist_inv
        total = total + eigenvalue.pow(linking) * dimension(snapshot, channel).scale(multiplicity)
    return total


def evaluate_product_toy_case(
    *,
    snapshot: dict[str, Any],
    diagram: LinkDiagram,
    character_assignment: tuple[str, ...],
    projection_contract: dict[str, Any],
) -> dict[str, Any]:
    component_count = len(diagram.components)
    if component_count > 2:
        raise ValueError("product toy evaluator only supports at most two components")
    matrix = diagram.linking_matrix()
    labels = list(snapshot["category_data"]["labels"])
    total = CyclotomicSparse.zero()
    sector_count = 0
    for label_tuple in all_tuples(labels, component_count):
        sector_count += 1
        term = CyclotomicSparse.one()
        for idx, label in enumerate(label_tuple):
            term = term * twist(snapshot, label).pow(diagram.components[idx].framing)
            term = term * character_value(projection_contract, label, character_assignment[idx])
        if component_count == 0:
            pass
        elif component_count == 1:
            term = term * dimension(snapshot, label_tuple[0])
        else:
            term = term * channel_trace(
                snapshot=snapshot,
                left=label_tuple[0],
                right=label_tuple[1],
                linking=matrix[0][1],
            )
        total = total + term
    return {
        "diagram_id": diagram.diagram_id,
        "component_count": component_count,
        "character_assignment": list(character_assignment),
        "sector_count": sector_count,
        "cyclotomic_modulus": 20,
        "total_sparse_zeta20": total.to_json(),
        "total_display": total.display(),
        "evaluation_profile": (
            "toy-linking-matrix-product-row; empty/one-component/two-component-channel-trace-only"
        ),
        "character_projection_contract_hash": projection_contract["content_hash"],
    }


def run_benchmark(*, started_at_utc: str) -> dict[str, Any]:
    rule = load_json(RULE)
    surface_probe = load_json(PRODUCT_SURFACE_PROBE)
    disposition = row_disposition(rule, PRODUCT_FAMILY)
    if disposition["disposition"] != "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED":
        raise RuntimeError(f"{PRODUCT_FAMILY} is not admitted by the partial scan rule")
    paths = product_snapshot_paths()
    snapshots = [load_json(path) for path in paths]
    for snapshot in snapshots:
        validate_formal_evidence(snapshot)
        data = snapshot["category_data"]
        if snapshot["family_id"] != PRODUCT_FAMILY:
            raise RuntimeError(f"unexpected family {snapshot['family_id']}")
        if data["product_type"] != "Deligne product":
            raise RuntimeError(f"unexpected product type {data['product_type']!r}")
        if data["f_symbols"].get("construction") != "factorwise tensor product of pinned factor F-symbols":
            raise RuntimeError("product F-symbol construction is not factorwise pinned")
        if data["r_symbols"].get("construction") != "factorwise tensor product of pinned factor R-symbols":
            raise RuntimeError("product R-symbol construction is not factorwise pinned")

    diagrams = [(path, LinkDiagram.from_json(load_json(path))) for path in TOY_DIAGRAMS]
    case_results = []
    projection_contracts = {}
    t0 = time.perf_counter()
    for snapshot_path, snapshot in zip(paths, snapshots, strict=True):
        contract = character_projection_contract(snapshot)
        projection_contracts[snapshot["realization_id"]] = contract
        for diagram_path, diagram in diagrams:
            for assignment in all_tuples(PRODUCT_CHARACTER_GROUP, len(diagram.components)):
                case_started = time.perf_counter()
                result = evaluate_product_toy_case(
                    snapshot=snapshot,
                    diagram=diagram,
                    character_assignment=assignment,
                    projection_contract=contract,
                )
                elapsed_ms = (time.perf_counter() - case_started) * 1000
                body = {
                    "snapshot_hash": snapshot["content_hash"],
                    "diagram_hash": file_sha256_id(diagram_path),
                    "character_assignment": assignment,
                    "projection_contract_hash": contract["content_hash"],
                    "benchmark": "product-partial-scan-v1",
                }
                case_results.append(
                    {
                        "case_id": "product-bench-"
                        + stable_content_hash(body).removeprefix("sha256:")[:24],
                        "status": "PASS_PRODUCT_BENCHMARK",
                        "family_id": PRODUCT_FAMILY,
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
                            "character_projection_contract": contract["content_hash"],
                        },
                        "result_summary": result,
                    }
                )
    elapsed_total_ms = (time.perf_counter() - t0) * 1000
    max_case = max(case_results, key=lambda item: item["elapsed_ms"])
    contract_hashes = sorted({item["content_hash"] for item in projection_contracts.values()})
    checks = {
        "partial_rule_admits_product_family": True,
        "surface_probe_previously_recorded_bottleneck": surface_probe["status"]
        == "BLOCKED_PRODUCT_ROW_EXECUTABLE_SURFACE_NOT_READY",
        "all_product_snapshots_included": len(snapshots) == 8,
        "all_cases_passed": all(item["status"] == "PASS_PRODUCT_BENCHMARK" for item in case_results),
        "character_projection_contracts_bound": len(contract_hashes) == 8,
        "composite_field_expression_runtime_used": True,
        "no_formal_scan_evidence_claimed": True,
    }
    if not all(checks.values()):
        raise RuntimeError(f"product benchmark checks failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.low-rank-product-partial-scan-benchmark.v1",
            "status": "PASS_PRODUCT_TOY_BENCHMARK_FAST",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/run_low_rank_product_partial_scan_benchmark_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/run_low_rank_product_partial_scan_benchmark_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "claim_level": "runtime-benchmark-preformal",
            "source_status": "preformal-runtime-benchmark-not-formal-scan-evidence",
            "benchmark_id": "low-rank-product-partial-scan-benchmark-v1",
            "input_artifacts": {
                "partial_scan_rule": artifact_record(RULE, rule),
                "previous_surface_probe": artifact_record(PRODUCT_SURFACE_PROBE, surface_probe),
                "snapshots": [
                    artifact_record(path, snapshot)
                    for path, snapshot in zip(paths, snapshots, strict=True)
                ],
                "diagrams": [artifact_record(path) for path, _ in diagrams],
            },
            "scope": {
                "family_ids": [PRODUCT_FAMILY],
                "snapshot_count": len(snapshots),
                "diagram_ids": [diagram.diagram_id for _, diagram in diagrams],
                "formal_partial_scan_plan_used": False,
                "formal_scan_case_result_produced": False,
                "supported_component_counts": [0, 1, 2],
                "supported_row_types": ["pinned Semion x Fib/Yang-Lee Deligne product"],
            },
            "worker_contracts": {
                "character_projection_contracts": projection_contracts,
                "distinct_character_projection_contract_hashes": contract_hashes,
                "expression_runtime": {
                    "name": "sparse-integer-zeta20",
                    "supports": [
                        "i as zeta20^5",
                        "zeta10 as zeta20^2",
                        "Fibonacci/Yang-Lee dimension sums recorded in snapshots",
                        "product twists such as (i)*(zeta10^4)",
                    ],
                    "does_not_support": [
                        "arbitrary algebraic simplification",
                        "division by non-root dimension expressions",
                        "general planar RT recoupling graphs",
                    ],
                },
                "two_component_linking_profile": (
                    "fusion-channel trace sum_k N_ab^k (theta_k/(theta_a theta_b))^linking d_k"
                ),
            },
            "timing": {
                "case_count": len(case_results),
                "elapsed_total_ms": elapsed_total_ms,
                "max_case_elapsed_ms": max_case["elapsed_ms"],
                "max_case_id": max_case["case_id"],
                "per_family": {
                    PRODUCT_FAMILY: {
                        "case_count": len(case_results),
                        "elapsed_total_ms": elapsed_total_ms,
                        "max_case_elapsed_ms": max_case["elapsed_ms"],
                        "snapshot_count": len(snapshots),
                    }
                },
            },
            "case_results": case_results,
            "checks": checks,
            "explicit_non_claims": [
                "This benchmark artifact is not a partial_scan_plan.",
                "This benchmark artifact is not a scan_case_result.",
                "This benchmark artifact is not a scan_aggregate.",
                "This benchmark artifact does not claim no signal.",
                "This benchmark artifact only probes rank4-semion-times-fibonacci on toy diagrams.",
                "This benchmark artifact is not a general Deligne product evaluator.",
                "This benchmark artifact is not a general planar RT recoupling evaluator.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "low-rank-product-partial-scan-benchmark-v1.json": run_benchmark(
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
