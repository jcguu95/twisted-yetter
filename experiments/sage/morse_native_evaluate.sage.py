"""Chunkable native Morse RT/Kirby-color evaluator.

The input is expanded Morse fundamental-form JSON, not PD/Gauss/braid data.
Supported category adapters are registered in ``morse_category_registry``.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import UTC, datetime
from itertools import islice, product
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

from sage.env import SAGE_VERSION

from experiments.sage.morse_category_registry import CATEGORY_CHOICES, build_category
from experiments.sage.morse_fusion_evaluator import MorseEvaluator, analyze_topology
from experiments.scripts.morse_singleton_workload import (
    FsyncJSONLWriter,
    atomic_write_json,
    file_sha256,
    payload_sha256,
    read_jsonl,
    recover_jsonl_checkpoint,
)


REPO_ROOT = Path(__file__).resolve().parents[2]


def command(argv):
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def complex_json(value):
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def complex_from_json(payload):
    return complex(float(payload["real"]), float(payload["imag"]))


def parse_assignment(raw: str | None, components, default=0):
    if raw is None:
        return {component: default for component in components}
    path = Path(raw)
    payload = json.loads(path.read_text()) if path.exists() else json.loads(raw)
    if isinstance(payload, list):
        if len(payload) != len(components):
            raise ValueError("assignment list length does not match component count")
        return dict(zip(components, payload, strict=True))
    return payload


def labels_at_index(labels, component_count, sector_index):
    labels = tuple(labels)
    base = len(labels)
    if not (0 <= sector_index < base**component_count):
        raise ValueError(f"sector index out of range: {sector_index}")
    digits = [0] * component_count
    value = int(sector_index)
    for position in range(component_count - 1, -1, -1):
        value, digit = divmod(value, base)
        digits[position] = digit
    return tuple(labels[digit] for digit in digits)


def read_sector_entries(path):
    entries = read_jsonl(path)
    indices = [int(entry["sector_index"]) for entry in entries]
    if len(indices) != len(set(indices)):
        raise ValueError("sector index file contains duplicates")
    return tuple(entries)


def sector_rows(category, components, start, count, index_file=None):
    if index_file is not None:
        entries = read_sector_entries(index_file)
        return (
            (
                int(entry["sector_index"]),
                labels_at_index(
                    category.labels, len(components), int(entry["sector_index"])
                ),
                entry,
            )
            for entry in entries
        ), entries
    iterator = product(category.labels, repeat=len(components))
    rows = enumerate(islice(iterator, start, None if count is None else start + count), start=start)
    return ((index, labels, None) for index, labels in rows), None


def memory_bytes():
    try:
        return int(os.sysconf("SC_PAGE_SIZE")) * int(os.sysconf("SC_PHYS_PAGES"))
    except (AttributeError, OSError, ValueError):
        return None


def environment_metadata():
    local_now = datetime.now().astimezone()
    offset = local_now.utcoffset()
    allowlist = (
        "DOT_SAGE",
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
        "MKL_NUM_THREADS",
        "PYTHONPATH",
    )
    return {
        "hostname": platform.node(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "python_executable": sys.executable,
        "python_version": sys.version,
        "sage_version": SAGE_VERSION,
        "cpu_count": os.cpu_count(),
        "total_memory_bytes": memory_bytes(),
        "timezone_name": local_now.tzname(),
        "timezone_utc_offset_seconds": (
            int(offset.total_seconds()) if offset is not None else None
        ),
        "environment_allowlist": {
            key: os.environ.get(key) for key in allowlist if key in os.environ
        },
    }


def singleton_path(output_dir: Path, sector_index: int) -> Path:
    return output_dir / f"sector-{sector_index:012d}.json"


def valid_completed_singleton(path: Path, identity_sha256: str, sector_index: int):
    try:
        payload = json.loads(path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return False
    return (
        payload.get("status") == "pass"
        and payload.get("evaluation_identity_sha256") == identity_sha256
        and int(payload.get("sector_index", -1)) == sector_index
    )


def compact_jsonl_singleton_payload(payload):
    stats = payload["evaluation_stats"]
    ranking = payload.get("ranking_metadata") or {}
    return {
        "schema": "twisted-yetter.native-morse-singleton-result.compact.v1",
        "status": payload["status"],
        "evaluation_identity_sha256": payload["evaluation_identity_sha256"],
        "sector_index": payload["sector_index"],
        "labels": payload["labels"],
        "coefficient": payload["coefficient"],
        "fixed_value": payload["fixed_value"],
        "weighted_value": payload["weighted_value"],
        "evaluation_stats": {
            key: stats[key]
            for key in (
                "cups",
                "caps",
                "kinks",
                "f_rotations",
                "leaf_r",
                "block_r",
                "max_active_strands",
                "max_state_support",
            )
        },
        "ranking_metadata": {
            key: ranking[key]
            for key in (
                "complexity_rank",
                "complexity_quantile",
                "estimated_work",
                "max_boundary_fusion_dimension",
            )
            if key in ranking
        },
        "utc_finish": payload["utc_finish"],
        "elapsed_seconds": payload["elapsed_seconds"],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--category", choices=CATEGORY_CHOICES, required=True)
    parser.add_argument("--level", type=int)
    parser.add_argument("--mode", choices=("fixed", "omega", "chunk"), default="fixed")
    parser.add_argument("--labels", help="JSON object/list or path for fixed component labels")
    parser.add_argument("--characters", help="JSON object/list or path; default is untwisted zero")
    parser.add_argument("--sector-start", type=int, default=0)
    parser.add_argument("--sector-count", type=int)
    parser.add_argument("--sector-index-file", type=Path)
    parser.add_argument(
        "--planner-mode", choices=("hybrid", "sequential"), default="hybrid"
    )
    parser.add_argument(
        "--reverse-orientation", action="append", default=[], metavar="COMPONENT"
    )
    parser.add_argument(
        "--group-components",
        help="comma-separated component names for grouped partial sums",
    )
    parser.add_argument(
        "--record-sector-values",
        action="store_true",
        help="record each fixed-label raw and weighted value in chunk output",
    )
    parser.add_argument(
        "--singleton-output-dir",
        type=Path,
        help="checkpoint directory for completed singleton results",
    )
    parser.add_argument(
        "--checkpoint-format",
        choices=("files", "jsonl"),
        default="files",
        help="one atomic JSON file per singleton, or one durable JSONL ledger per worker",
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        help="update the atomic progress sidecar every N completed singletons",
    )
    parser.add_argument("--run-id")
    parser.add_argument("--worker-id")
    parser.add_argument(
        "--resume",
        action="store_true",
        help="skip matching completed singleton checkpoint files",
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.singleton_output_dir and args.mode != "chunk":
        parser.error("--singleton-output-dir requires --mode chunk")
    if args.resume and not args.singleton_output_dir:
        parser.error("--resume requires --singleton-output-dir")
    if args.progress_every is not None and args.progress_every < 1:
        parser.error("--progress-every must be positive")
    progress_every = args.progress_every or (
        100 if args.checkpoint_format == "jsonl" else 1
    )

    started = datetime.now(UTC)
    wall_start = time.perf_counter()
    input_payload = json.loads(args.input.read_text())
    forms = tuple(input_payload["forms"])
    topology = analyze_topology(forms)
    category, display_name, category_id = build_category(args.category, args.level)
    evaluator = MorseEvaluator(
        category,
        planner_mode=args.planner_mode,
        reversed_orientation_components=args.reverse_orientation,
    )

    payload = {
        "schema": "twisted-yetter.native-morse-rt-evaluation.v1",
        "status": "running",
        "mathematical_status": "NUMERICAL_EVALUATION_OF_INPUT_WITH_INPUT_CAVEATS_INHERITED",
        "generator_script": "experiments/sage/morse_native_evaluate.sage.py",
        "argv": sys.argv,
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python " + " ".join(sys.argv),
        "input": str(args.input.resolve().relative_to(REPO_ROOT)),
        "input_status": input_payload.get("status"),
        "category": display_name,
        "category_id": category_id,
        "component_order": list(topology.component_order),
        "mode": args.mode,
        "utc_start": started.isoformat(),
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "dirty": bool(command(["git", "status", "--short"])),
        },
        "tool_versions": {
            "sage": SAGE_VERSION,
            "python": sys.version,
            "platform": platform.platform(),
        },
        "environment": environment_metadata(),
    }

    if args.mode == "fixed":
        labels = parse_assignment(args.labels, topology.component_order)
        value, stats = evaluator.fixed_label_value(forms, labels)
        payload.update({"fixed_labels": labels, "value": complex_json(value), "evaluation_stats": stats})
    else:
        group_components = tuple(
            component.strip()
            for component in (args.group_components or "").split(",")
            if component.strip()
        )
        unknown_group_components = set(group_components) - set(topology.component_order)
        if unknown_group_components:
            raise ValueError(
                f"unknown group components: {sorted(unknown_group_components)!r}"
            )
        grouped_sums = defaultdict(complex)
        grouped_counts = defaultdict(int)
        sector_value_rows = []
        characters = parse_assignment(args.characters, topology.component_order)
        start = args.sector_start if args.mode == "chunk" else 0
        count = args.sector_count if args.mode == "chunk" else None
        total = 0.0 + 0.0j
        evaluated = 0
        max_support = 0
        planner_summary = None
        rows, explicit_entries = sector_rows(
            category, topology.component_order, start, count, args.sector_index_file
        )
        evaluated_indices = []
        skipped_indices = []
        checkpoint_dir = args.singleton_output_dir.resolve() if args.singleton_output_dir else None
        evaluation_identity = {
            "schema": "twisted-yetter.native-morse-singleton-identity.v1",
            "input_sha256": file_sha256(args.input),
            "category_id": category_id,
            "level": args.level,
            "component_order": list(topology.component_order),
            "character_assignments": characters,
            "planner_mode": args.planner_mode,
            "reversed_orientation_components": sorted(args.reverse_orientation),
        }
        evaluation_identity_sha256 = payload_sha256(evaluation_identity)
        worker_context = None
        worker_context_sha256 = None
        progress_path = None
        ledger_path = None
        ledger_records = {}
        ledger_writer = None
        if checkpoint_dir:
            checkpoint_dir.mkdir(parents=True, exist_ok=True)
            worker_context = {
                "schema": "twisted-yetter.native-morse-singleton-worker-context.v1",
                "status": "running",
                "run_id": args.run_id,
                "worker_id": args.worker_id,
                "utc_start": started.isoformat(),
                "argv": sys.argv,
                "reproduce_command": payload["reproduce_command"],
                "evaluation_identity": evaluation_identity,
                "evaluation_identity_sha256": evaluation_identity_sha256,
                "sector_index_file": (
                    str(args.sector_index_file.resolve())
                    if args.sector_index_file
                    else None
                ),
                "sector_index_file_sha256": (
                    file_sha256(args.sector_index_file)
                    if args.sector_index_file
                    else None
                ),
                "repo": payload["repo"],
                "tool_versions": payload["tool_versions"],
                "environment": payload["environment"],
                "checkpoint_format": args.checkpoint_format,
                "progress_every": progress_every,
            }
            worker_context_sha256 = payload_sha256(worker_context)
            worker_context["worker_context_sha256"] = worker_context_sha256
            context_name = f"worker-context-{args.worker_id or 'unassigned'}.json"
            atomic_write_json(checkpoint_dir / context_name, worker_context)
            progress_path = checkpoint_dir / f"worker-progress-{args.worker_id or 'unassigned'}.json"
            if args.checkpoint_format == "jsonl":
                ledger_path = checkpoint_dir / f"singleton-ledger-{args.worker_id or 'unassigned'}.jsonl"
                if args.resume:
                    ledger_records = recover_jsonl_checkpoint(
                        ledger_path, evaluation_identity_sha256
                    )
                elif ledger_path.exists() and ledger_path.stat().st_size:
                    raise ValueError(
                        f"refusing to append to existing ledger without --resume: {ledger_path}"
                    )
                ledger_writer = FsyncJSONLWriter(ledger_path).__enter__()

        for sector_index, labels_tuple, ranking_metadata in rows:
            output_path = (
                singleton_path(checkpoint_dir, sector_index)
                if checkpoint_dir and args.checkpoint_format == "files"
                else None
            )
            completed_payload = None
            if args.resume and output_path and valid_completed_singleton(
                output_path, evaluation_identity_sha256, sector_index
            ):
                completed_payload = json.loads(output_path.read_text())
            elif args.resume and ledger_path and sector_index in ledger_records:
                completed_payload = ledger_records[sector_index]
            if completed_payload is not None:
                weighted = complex_from_json(completed_payload["weighted_value"])
                total += weighted
                labels = dict(
                    zip(topology.component_order, labels_tuple, strict=True)
                )
                if group_components:
                    group_key = tuple(
                        labels[component] for component in group_components
                    )
                    grouped_sums[group_key] += weighted
                    grouped_counts[group_key] += 1
                skipped_indices.append(sector_index)
                continue
            labels = dict(zip(topology.component_order, labels_tuple, strict=True))
            coefficient = 1.0 + 0.0j
            for component, label in labels.items():
                coefficient *= complex(category.dimension(label))
                coefficient *= complex(category.character(characters[component], label))
            singleton_started = datetime.now(UTC)
            singleton_clock = time.perf_counter()
            if progress_path and evaluated % progress_every == 0:
                atomic_write_json(
                    progress_path,
                    {
                        "schema": "twisted-yetter.native-morse-singleton-progress.v1",
                        "status": "evaluating",
                        "run_id": args.run_id,
                        "worker_id": args.worker_id,
                        "sector_index": sector_index,
                        "labels": list(labels_tuple),
                        "ranking_metadata": ranking_metadata,
                        "utc_start": singleton_started.isoformat(),
                        "completed_count_this_process": evaluated,
                        "skipped_count_this_process": len(skipped_indices),
                        "evaluation_identity_sha256": evaluation_identity_sha256,
                    },
                )
            value, stats = evaluator.fixed_label_value(forms, labels)
            singleton_finished = datetime.now(UTC)
            singleton_elapsed = time.perf_counter() - singleton_clock
            weighted = coefficient * value
            singleton_payload = {
                "schema": "twisted-yetter.native-morse-singleton-result.v1",
                "status": "pass",
                "mathematical_status": payload["mathematical_status"],
                "run_id": args.run_id,
                "worker_id": args.worker_id,
                "worker_context_sha256": worker_context_sha256,
                "evaluation_identity_sha256": evaluation_identity_sha256,
                "sector_index": sector_index,
                "labels": list(labels_tuple),
                "coefficient": complex_json(coefficient),
                "fixed_value": complex_json(value),
                "weighted_value": complex_json(weighted),
                "evaluation_stats": stats,
                "ranking_metadata": ranking_metadata,
                "utc_start": singleton_started.isoformat(),
                "utc_finish": singleton_finished.isoformat(),
                "elapsed_seconds": singleton_elapsed,
            }
            if output_path:
                atomic_write_json(output_path, singleton_payload)
            elif ledger_writer:
                ledger_writer.append(compact_jsonl_singleton_payload(singleton_payload))
            total += coefficient * value
            if args.record_sector_values:
                sector_value_rows.append(
                    {
                        "sector_index": sector_index,
                        "labels": list(labels_tuple),
                        "coefficient": complex_json(coefficient),
                        "fixed_value": complex_json(value),
                        "weighted_value": complex_json(weighted),
                        "elapsed_seconds": singleton_elapsed,
                    }
                )
            if group_components:
                group_key = tuple(labels[component] for component in group_components)
                grouped_sums[group_key] += coefficient * value
                grouped_counts[group_key] += 1
            evaluated += 1
            evaluated_indices.append(sector_index)
            max_support = max(max_support, stats["max_state_support"])
            if planner_summary is None:
                planner_summary = {
                    "f_rotations": stats["f_rotations"],
                    "leaf_r": stats["leaf_r"],
                    "block_r": stats["block_r"],
                    "max_active_strands": stats["max_active_strands"],
                    "planner_weights": stats["planner_weights"],
                    "plans": stats["plans"],
                }
            if progress_path and evaluated % progress_every == 0:
                atomic_write_json(
                    progress_path,
                    {
                        "schema": "twisted-yetter.native-morse-singleton-progress.v1",
                        "status": "idle-after-checkpoint",
                        "run_id": args.run_id,
                        "worker_id": args.worker_id,
                        "last_completed_sector_index": sector_index,
                        "last_completed_utc": singleton_finished.isoformat(),
                        "last_elapsed_seconds": singleton_elapsed,
                        "completed_count_this_process": evaluated,
                        "skipped_count_this_process": len(skipped_indices),
                        "evaluation_identity_sha256": evaluation_identity_sha256,
                    },
                )
        if ledger_writer:
            ledger_writer.__exit__(None, None, None)
        payload.update(
            {
                "character_assignments": characters,
                "sector_range": None if explicit_entries is not None else {"start": start, "count": evaluated},
                "sector_indices": evaluated_indices if explicit_entries is not None else None,
                "sector_index_file": str(args.sector_index_file) if args.sector_index_file else None,
                "sector_index_file_sha256": (
                    file_sha256(args.sector_index_file)
                    if args.sector_index_file
                    else None
                ),
                "evaluation_identity_sha256": evaluation_identity_sha256,
                "singleton_output_dir": str(checkpoint_dir) if checkpoint_dir else None,
                "checkpoint_format": args.checkpoint_format if checkpoint_dir else None,
                "progress_every": progress_every if checkpoint_dir else None,
                "singleton_ledger": str(ledger_path) if ledger_path else None,
                "completed_singleton_count": evaluated,
                "resumed_skipped_singleton_count": len(skipped_indices),
                "resumed_skipped_sector_indices": skipped_indices,
                "weighted_partial_sum": complex_json(total),
                "max_state_support": max_support,
                "planner_summary": planner_summary,
                "group_components": list(group_components),
                "grouped_weighted_partial_sums": [
                    {
                        "labels": list(key),
                        "sector_count": grouped_counts[key],
                        "weighted_partial_sum": complex_json(grouped_sums[key]),
                    }
                    for key in sorted(grouped_sums)
                ],
                "sector_values": sector_value_rows,
            }
        )

    finished = datetime.now(UTC)
    payload.update(
        {
            "status": "pass",
            "utc_finish": finished.isoformat(),
            "elapsed_seconds": time.perf_counter() - wall_start,
        }
    )
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(args.output.resolve())
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
