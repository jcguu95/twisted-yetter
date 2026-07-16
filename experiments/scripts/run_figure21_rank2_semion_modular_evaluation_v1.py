#!/usr/bin/env python3
"""Run Figure 21 with rank-2 semion branches through the modular evaluator."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import subprocess
import time
from typing import Any

from experiments.sage.pointed_premodular_categories import (
    Rank2Z2SemionModularCategory,
    SEMION_PIVOTAL_PROFILE_PATH,
)
from experiments.sage.ribbon_graph_evaluator import (
    PointedVacuumProjectorEvaluator,
    RibbonGraphEvaluator,
)
from experiments.scripts.special_dotted_morphism import (
    build_vacuum_coupon_graph,
    compile_projected_morphism,
    stable_json_hash,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT_PATH = (
    REPO_ROOT
    / "experiments/inputs/akbulut-yasui/figure21-right-morse-draft-v1.json"
)
OUTPUT_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-right-rank2-semion-modular-evaluation-v1.json"
)
SNAPSHOT_ROOT = (
    REPO_ROOT
    / "experiments/results/foundation-v2-safety-substrate/"
    "ribbon-realization-snapshots"
)
SNAPSHOTS = {
    "plus": {
        "path": SNAPSHOT_ROOT
        / "rank2-cyclic-z2-semion-plus-snapshot-v1.json",
        "content_hash": (
            "sha256:b6e1fcedc002a8bad19e62ce667a79bc4592557f4ad2667ee53b40db2f23c3cb"
        ),
    },
    "minus": {
        "path": SNAPSHOT_ROOT
        / "rank2-cyclic-z2-semion-minus-snapshot-v1.json",
        "content_hash": (
            "sha256:e52647abd74604ca450085f9df7d063fb39d8eb43b43847278868c2b3de39ba1"
        ),
    },
}
EXPECTED_INPUT_SHA256 = (
    "b6f8459547a7cec415eb6c70acb89a40c37ab4cabd364330206685d8e579cbc5"
)
EXPECTED_GRAPH_HASH = (
    "sha256:f66f1ef64661c432c389b6c1db726de605055ea0cabe74005fa649ebbd32a26c"
)
TOLERANCE = 1e-10


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_path(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _complex_payload(value: complex) -> dict[str, float]:
    value = complex(value)
    return {"real": float(value.real), "imag": float(value.imag)}


def _complex_key(value: complex) -> str:
    value = complex(value)
    real = 0.0 if abs(value.real) < TOLERANCE else round(value.real, 12)
    imag = 0.0 if abs(value.imag) < TOLERANCE else round(value.imag, 12)
    return f"{real:+.12g}{imag:+.12g}i"


def _load_snapshot(branch: str) -> dict[str, Any]:
    spec = SNAPSHOTS[branch]
    payload = json.loads(spec["path"].read_text())
    expected_id = f"rank2-cyclic-z2-semion-{branch}"
    if payload.get("status") != "RESOLVED_RIBBON_REALIZATION":
        raise ValueError(f"{expected_id} snapshot is not resolved")
    if payload.get("realization_id") != expected_id:
        raise ValueError(f"{branch} snapshot realization id changed")
    if payload.get("content_hash") != spec["content_hash"]:
        raise ValueError(f"{branch} snapshot content hash changed")
    return {
        "path": str(spec["path"].relative_to(REPO_ROOT)),
        "file_sha256": _sha256_path(spec["path"]),
        "content_hash": payload["content_hash"],
        "category_data_hash": payload["category_data_hash"],
        "pinned_payload_hashes": payload["pinned_payload_hashes"],
        "structural_checks": payload["structural_checks"],
    }


def _load_figure21() -> dict[str, Any]:
    source_bytes = INPUT_PATH.read_bytes()
    input_sha256 = _sha256_bytes(source_bytes)
    if input_sha256 != EXPECTED_INPUT_SHA256:
        raise ValueError(
            "Figure 21 input hash changed: "
            f"expected {EXPECTED_INPUT_SHA256}, got {input_sha256}"
        )
    source = json.loads(source_bytes)
    forms = tuple(source["forms"])
    ir = compile_projected_morphism(
        forms,
        component_by_piece=source["component_by_piece"],
        special_components=source["special_components"],
        component_order=source["component_order"],
    )
    graph = build_vacuum_coupon_graph(forms, ir)
    if graph["graph_hash"] != EXPECTED_GRAPH_HASH:
        raise ValueError(
            "Figure 21 coupon graph hash changed: "
            f"expected {EXPECTED_GRAPH_HASH}, got {graph['graph_hash']}"
        )
    ordinary = tuple(
        component for component in source["component_order"] if component != "red"
    )
    if len(ordinary) != 11 or graph["coupon_input_count"] != 29:
        raise ValueError("Figure 21 rank2 semion contract changed")
    return {
        "source": source,
        "forms": forms,
        "ir": ir,
        "graph": graph,
        "ordinary": ordinary,
        "input_sha256": input_sha256,
    }


def _labels_from_sector(sector_id: int, width: int) -> tuple[int, ...]:
    bits = [0] * width
    value = sector_id
    for index in range(width - 1, -1, -1):
        value, bits[index] = divmod(value, 2)
    return tuple(bits)


def _evaluate_branch(
    *,
    branch: str,
    context: dict[str, Any],
    max_sectors: int | None,
) -> dict[str, Any]:
    category = Rank2Z2SemionModularCategory(branch=branch)
    modular = RibbonGraphEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )
    pointed = PointedVacuumProjectorEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )
    total_sectors = 2 ** len(context["ordinary"])
    sector_limit = total_sectors if max_sectors is None else min(max_sectors, total_sectors)
    records = []
    value_distribution: Counter[str] = Counter()
    projector_rank_distribution: Counter[str] = Counter()
    status_distribution: Counter[str] = Counter()
    max_error = 0.0
    worst_sector: int | None = None
    started = time.perf_counter()
    for sector_id in range(sector_limit):
        labels_tuple = _labels_from_sector(sector_id, len(context["ordinary"]))
        labels = dict(zip(context["ordinary"], labels_tuple, strict=True))
        modular_value, modular_stats = modular.fixed_label_value(context["graph"], labels)
        pointed_value, pointed_stats = pointed.fixed_label_value(context["graph"], labels)
        error = abs(modular_value - pointed_value)
        if error > max_error:
            max_error = error
            worst_sector = sector_id
        if error > TOLERANCE:
            raise AssertionError(
                f"{branch} sector {sector_id} modular/pointed mismatch: {error}"
            )
        status = (
            "ZERO"
            if abs(modular_value) <= TOLERANCE
            else "NONZERO"
        )
        value_distribution[_complex_key(modular_value)] += 1
        projector_rank_distribution[str(pointed_stats["projector_rank"])] += 1
        status_distribution[status] += 1
        records.append(
            {
                "sector_id": sector_id,
                "labels": {
                    component: label
                    for component, label in zip(
                        context["ordinary"], labels_tuple, strict=True
                    )
                },
                "modular_value": _complex_payload(modular_value),
                "pointed_value": _complex_payload(pointed_value),
                "modular_pointed_abs_error": error,
                "pointed_projector_rank": pointed_stats["projector_rank"],
                "pointed_status": pointed_stats["status"],
                "value_status": status,
                "modular_backend": modular_stats["backend"],
                "pointed_backend": pointed_stats["backend"],
            }
        )
    records_digest = _sha256_bytes(
        json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
    )
    return {
        "branch": branch,
        "category_id": category.category_id,
        "snapshot": _load_snapshot(branch),
        "sector_count": sector_limit,
        "full_sector_count": total_sectors,
        "elapsed_seconds": time.perf_counter() - started,
        "max_modular_pointed_abs_error": max_error,
        "worst_sector_id": worst_sector,
        "all_modular_values_equal_pointed_values": max_error <= TOLERANCE,
        "projector_rank_distribution": dict(sorted(projector_rank_distribution.items())),
        "value_status_distribution": dict(sorted(status_distribution.items())),
        "value_distribution": dict(sorted(value_distribution.items())),
        "sector_records_sha256": records_digest,
        "sector_records": records,
    }


def generate(*, max_sectors: int | None) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    context = _load_figure21()
    branches = [
        _evaluate_branch(branch=branch, context=context, max_sectors=max_sectors)
        for branch in ("plus", "minus")
    ]
    by_branch = {branch["branch"]: branch for branch in branches}
    compared_sectors = min(branch["sector_count"] for branch in branches)
    branch_delta = 0.0
    branch_delta_sector: int | None = None
    branch_equal_count = 0
    for sector_id in range(compared_sectors):
        plus = by_branch["plus"]["sector_records"][sector_id]["modular_value"]
        minus = by_branch["minus"]["sector_records"][sector_id]["modular_value"]
        delta = abs(
            complex(plus["real"], plus["imag"])
            - complex(minus["real"], minus["imag"])
        )
        if delta <= TOLERANCE:
            branch_equal_count += 1
        if delta > branch_delta:
            branch_delta = delta
            branch_delta_sector = sector_id
    full_run = all(
        branch["sector_count"] == branch["full_sector_count"] for branch in branches
    )
    checks = {
        "figure21_input_hash_pinned": context["input_sha256"] == EXPECTED_INPUT_SHA256,
        "coupon_graph_hash_pinned": context["graph"]["graph_hash"] == EXPECTED_GRAPH_HASH,
        "semion_snapshots_pinned": all(
            branch["snapshot"]["content_hash"] == SNAPSHOTS[branch["branch"]]["content_hash"]
            for branch in branches
        ),
        "modular_equals_pointed_for_each_branch": all(
            branch["all_modular_values_equal_pointed_values"] for branch in branches
        ),
        "full_rank2_z2_sector_space_evaluated": full_run,
    }
    if not all(value for key, value in checks.items() if key != "full_rank2_z2_sector_space_evaluated"):
        raise AssertionError(f"Figure 21 rank2 semion checks failed: {checks!r}")
    status = (
        "PASS_FIGURE21_RANK2_SEMION_MODULAR_FULL_SECTOR_EVALUATION"
        if full_run
        else "PASS_FIGURE21_RANK2_SEMION_MODULAR_PREFIX_EVALUATION"
    )
    finished = datetime.now(UTC)
    return {
        "schema": "twisted-yetter.figure21-rank2-semion-modular-evaluation.v1",
        "status": status,
        "mathematical_status": "NUMERIC_EVALUATOR_CONTROL_NOT_EXOTIC_PROOF",
        "purpose": (
            "Evaluate the Figure 21 right-side Morse input on the smallest "
            "rank-2 modular categories with nontrivial universal group, and "
            "cross-check the modular killing-loop evaluator against the pointed "
            "graph-level evaluator sector by sector."
        ),
        "generator_script": (
            "experiments/scripts/run_figure21_rank2_semion_modular_evaluation_v1.py"
        ),
        "argv": [],
        "reproduce_command": (
            "UV_CACHE_DIR=/tmp/uv-cache PYTHONPATH=. uv run python "
            "experiments/scripts/run_figure21_rank2_semion_modular_evaluation_v1.py"
        ),
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "input": {
            "path": str(INPUT_PATH.relative_to(REPO_ROOT)),
            "sha256": context["input_sha256"],
            "source_ref": context["source"]["source_ref"],
            "source_locator": context["source"]["source_locator"],
            "source_status": context["source"]["status"],
            "projected_ir_hash": stable_json_hash(context["ir"]),
            "coupon_graph_hash": context["graph"]["graph_hash"],
            "coupon_factor_count": context["graph"]["coupon_input_count"],
            "ordinary_component_order": list(context["ordinary"]),
            "framing_labels": context["source"]["framing_labels"],
        },
        "category_data": {
            "pivotal_profile": str(SEMION_PIVOTAL_PROFILE_PATH.relative_to(REPO_ROOT)),
            "pivotal_profile_sha256": _sha256_path(SEMION_PIVOTAL_PROFILE_PATH),
            "branches": [branch["category_id"] for branch in branches],
            "universal_group": "Z/2",
        },
        "checks": checks,
        "branch_comparison": {
            "compared_sector_count": compared_sectors,
            "plus_minus_equal_sector_count": branch_equal_count,
            "plus_minus_max_abs_delta": branch_delta,
            "worst_sector_id": branch_delta_sector,
            "interpretation": (
                "Recorded as a branch comparison only; plus/minus equality is "
                "not required for the evaluator contract."
            ),
        },
        "results": {branch["branch"]: branch for branch in branches},
        "claim_boundary": (
            "This proves only that this Figure 21 right-side modular evaluator "
            "run completes for the two rank-2 semion branches and agrees with "
            "the pointed evaluator on the evaluated sectors."
        ),
        "non_claims": [
            "This is not a formal low-rank scan aggregate.",
            "This is not a complete exotic-pair comparison; only the Figure 21 right-side input is evaluated.",
            "This does not certify the Figure 21 transcription against the printed paper.",
            "This does not evaluate nonpointed categories or categories with trivial universal group.",
            "This does not prove TCY or low-rank MTCs cannot detect exotic pairs."
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT_PATH)
    parser.add_argument("--max-sectors", type=int, default=None)
    args = parser.parse_args()
    result = generate(max_sectors=args.max_sectors)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
