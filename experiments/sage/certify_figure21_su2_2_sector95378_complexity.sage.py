#!/usr/bin/env python3
"""Certify the exact fusion-path dimensions of Figure 21 sector 95378."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import platform
import socket
import subprocess
import sys
import time

from sage.version import version as sage_version

from experiments.sage.figure21_su2_2_direct_side_projector import (
    build_context,
    decode_sector,
)
from experiments.sage.morse_fusion_evaluator import (
    right_comb_fusion_path_counts,
)
from experiments.scripts.special_dotted_morphism import replay_forms


REPO = Path(__file__).resolve().parents[2]
INPUT = REPO / "experiments/inputs/akbulut-yasui/figure21-right-morse-draft-v1.json"
DEFAULT_OUTPUT = (
    REPO
    / "experiments/results/akbulut-yasui"
    / "figure21-right-su2-2-sector95378-complexity-certificate-v1.json"
)
SECTOR_ID = 95_378
EXPECTED_PROJECTOR_COUNTS = {0: 2**13, 2: 2**13}
EXPECTED_ACTIVE_COUNTS = {0: 2**27, 2: 2**27}

DEPENDENCIES = (
    "experiments/inputs/akbulut-yasui/figure21-right-morse-draft-v1.json",
    "experiments/sage/certify_figure21_su2_2_sector95378_complexity.sage.py",
    "experiments/sage/figure21_su2_2_direct_side_projector.py",
    "experiments/sage/morse_category_registry.py",
    "experiments/sage/morse_fusion_evaluator.py",
    "experiments/sage/morse_projector_workload.py",
    "experiments/sage/su2k_fusion_braid_evaluator.sage.py",
    "experiments/scripts/morse_dsl.py",
    "experiments/scripts/morse_pl_lift.py",
    "experiments/scripts/special_dotted_morphism.py",
)


def _run_git(*args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=REPO,
        check=check,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _dependency_record(relative: str) -> dict:
    path = REPO / relative
    working_blob = _run_git("hash-object", relative)
    head_blob = _run_git("rev-parse", f"HEAD:{relative}", check=False)
    return {
        "path": relative,
        "bytes": path.stat().st_size,
        "sha256": _sha256(path),
        "git_blob": working_blob,
        "head_git_blob": head_blob or None,
        "matches_head": bool(head_blob) and working_blob == head_blob,
    }


def _oriented_labels(context: dict, strands: list[str], labels: dict[str, int]) -> list[int]:
    category = context["category"]
    component_by_token = context["lowered"]["semantic_component_by_token"]
    topology = context["topology"]
    result = []
    for strand in strands:
        label = labels[component_by_token[strand]]
        if topology.strand_orientation(strand) < 0:
            label = category.dual(label)
        result.append(label)
    return result


def _json_counts(counts: dict[int, int]) -> dict[str, int]:
    return {str(root): int(count) for root, count in sorted(counts.items())}


def build_certificate() -> dict:
    started = datetime.now(UTC)
    start_clock = time.monotonic()
    context = build_context()
    labels = dict(
        zip(
            context["ordinary"],
            decode_sector(SECTOR_ID, len(context["ordinary"])),
            strict=True,
        )
    )
    projector_event = next(
        entry
        for entry in replay_forms(context["lowered"]["forms"])
        if entry["form"]["kind"] == "vacuum-projector"
    )
    active_labels = _oriented_labels(
        context, projector_event["before_order"], labels
    )
    projector_labels = _oriented_labels(
        context, projector_event["form"]["strands"], labels
    )
    active_counts = right_comb_fusion_path_counts(
        context["category"], active_labels
    )
    projector_counts = right_comb_fusion_path_counts(
        context["category"], projector_labels
    )
    if projector_counts != EXPECTED_PROJECTOR_COUNTS:
        raise AssertionError(
            f"projector fusion counts changed: {projector_counts!r}"
        )
    if active_counts != EXPECTED_ACTIVE_COUNTS:
        raise AssertionError(f"active fusion counts changed: {active_counts!r}")

    dependencies = [_dependency_record(relative) for relative in DEPENDENCIES]
    finished = datetime.now(UTC)
    vacuum_dimension = int(active_counts[context["category"].unit])
    projector_rank = int(projector_counts[context["category"].unit])
    dense_entries = vacuum_dimension * vacuum_dimension
    return {
        "schema": "twisted-yetter.figure21-su2-2-hard-sector-complexity-certificate.v1",
        "status": "ESTABLISHED_EXACT_COMBINATORIAL_DIMENSION",
        "mathematical_status": "EXACT_INTEGER_FUSION_RULE_DYNAMIC_PROGRAMMING",
        "scope_warning": (
            "This certifies a barrier for the current full fusion-state backend; "
            "it is not a theorem that every possible algorithm is infeasible."
        ),
        "generator_script": DEPENDENCIES[1],
        "argv": list(sys.argv),
        "reproduce_command": (
            "DOT_SAGE=\"$PWD/.sage\" PYTHONPATH=. sage --python "
            "experiments/sage/"
            "certify_figure21_su2_2_sector95378_complexity.sage.py --write"
        ),
        "utc_start": started.isoformat(),
        "utc_finish": finished.isoformat(),
        "elapsed_seconds": time.monotonic() - start_clock,
        "repo_root": str(REPO),
        "git_commit": _run_git("rev-parse", "HEAD"),
        "git_dirty": bool(_run_git("status", "--porcelain")),
        "environment": {
            "hostname": socket.gethostname(),
            "platform": platform.platform(),
            "python": sys.version,
            "sage": sage_version,
        },
        "input": {
            "path": str(INPUT.relative_to(REPO)),
            "sha256": _sha256(INPUT),
            "presentation_subject": (
                "subject:twisted-yetter:presentation:"
                "akbulut-yasui-2008-figure21-e3prime"
            ),
            "presentation_status": "DRAFT_TRANSCRIPTION_NOT_PROVED_IDENTICAL_TO_SOURCE_FIGURE",
        },
        "category": {
            "category_id": context["category_id"],
            "subject": "subject:twisted-yetter:category-family:su2-k",
            "level": 2,
            "simple_labels": list(context["category"].labels),
            "unit": context["category"].unit,
        },
        "sector": {
            "sector_id": SECTOR_ID,
            "component_order": list(context["ordinary"]),
            "labels": labels,
            "hamming_weight": sum(label != 0 for label in labels.values()),
        },
        "projector_slice": {
            "morse_form_index": projector_event["form_index"],
            "active_strand_count": len(active_labels),
            "active_label_multiplicities": {
                str(label): count for label, count in sorted(Counter(active_labels).items())
            },
            "projector_factor_count": len(projector_labels),
            "projector_label_multiplicities": {
                str(label): count
                for label, count in sorted(Counter(projector_labels).items())
            },
            "projector_root_counts": _json_counts(projector_counts),
            "projector_vacuum_rank": projector_rank,
            "projector_vacuum_rank_power_of_two": 13,
            "active_root_counts": _json_counts(active_counts),
            "active_vacuum_fusion_dimension": vacuum_dimension,
            "active_vacuum_fusion_dimension_power_of_two": 27,
            "all_root_path_count": sum(active_counts.values()),
            "all_root_path_count_power_of_two": 28,
        },
        "dense_materialization_counterfactual": {
            "matrix_dimension": vacuum_dimension,
            "complex_entries": dense_entries,
            "complex_entries_power_of_two": 54,
            "complex128_bytes": dense_entries * 16,
            "complex128_bytes_power_of_two": 58,
            "warning": "The production evaluator is matrix-free; this is a scale illustration only.",
        },
        "method": {
            "kind": "exact fusion-rule dynamic programming",
            "enumerated_fusion_states": False,
            "recurrence": (
                "Starting from the tensor unit, propagate exact integer path "
                "multiplicities through fusion_outputs for each oriented label."
            ),
        },
        "dependencies": dependencies,
        "all_dependencies_match_head": all(
            record["matches_head"] for record in dependencies
        ),
        "sanity_checks": {
            "sector_decodes_to_expected_labels": labels
            == {
                "purple": 1,
                "mint": 1,
                "pink1": 2,
                "pink2": 1,
                "pink3": 1,
                "pink4": 2,
                "orange": 1,
                "blue": 1,
                "beige": 1,
                "green": 1,
                "black": 2,
            },
            "projector_rank_is_8192": projector_rank == 8192,
            "active_vacuum_dimension_is_2_power_27": vacuum_dimension == 2**27,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = build_certificate()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        temporary = args.output.with_suffix(args.output.suffix + ".tmp")
        temporary.write_text(rendered)
        temporary.replace(args.output)
        print(args.output)
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
