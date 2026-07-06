"""Yasui Figure 3 (a=1, R1-normalized) D(A4) untwisted singleton runner.

This script is a narrow preparation/profiling artifact.  It reuses the numeric
D(A4) FR-symbol braid evaluator from the a=3 chunked run, but changes the link
input to the audited R1-normalized a=1 braid payload.  Every sector is treated
as a singleton, and each computed singleton records reproducibility metadata.
"""

from __future__ import annotations

import argparse
import contextlib
from datetime import UTC, datetime
from itertools import product
import importlib.util
import io
import json
import math
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

import numpy as np
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
BASE_EVALUATOR_SCRIPT = (
    REPO_ROOT / "experiments" / "sage" / "yasui_figure3_a3_da4_untwisted_chunked.sage.py"
)
MTC_PATH = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "drinfeld-double-a4-omega0-mtc-fr-data-v1.json"
)
BRAID_PAYLOAD_PATH = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-braid-payload-v1.json"
)
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "yasui"
CHUNK_DIR = (
    RESULT_DIR
    / "figure3-a1-r1-normalized-da4-omega0-untwisted-singleton-chunks-v1"
)
MANIFEST_PATH = (
    RESULT_DIR
    / "figure3-a1-r1-normalized-da4-omega0-untwisted-singleton-manifest-v1.json"
)
PROBE_SUMMARY_PATH = (
    RESULT_DIR
    / "figure3-a1-r1-normalized-da4-omega0-untwisted-probe-v1.json"
)

ENV_ALLOWLIST = (
    "DOT_SAGE",
    "SAGE_ROOT",
    "SAGE_LOCAL",
    "PYTHONPATH",
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "MKL_NUM_THREADS",
)


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


base = load_module(BASE_EVALUATOR_SCRIPT, "da4_fr_braid_evaluator_for_yasui_a1")


def command(argv: list[str]) -> str:
    return subprocess.check_output(argv, cwd=REPO_ROOT, text=True).strip()


def optional_command(argv: list[str]) -> str | None:
    try:
        return command(argv)
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def read_json(path: Path):
    return json.loads(path.read_text())


def write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def relevant_status_lines(status_short: str | None) -> list[str]:
    if not status_short:
        return []
    lines = []
    for line in status_short.splitlines():
        path = line[3:] if len(line) > 3 else line
        if path == ".codex/" or path.startswith(".codex/"):
            continue
        lines.append(line)
    return lines


def repo_metadata() -> dict:
    status_short = optional_command(["git", "status", "--short"])
    relevant = relevant_status_lines(status_short)
    return {
        "root": str(REPO_ROOT),
        "git_commit": optional_command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(relevant),
        "dirty_ignoring_codex_app_metadata": bool(relevant),
        "status_short": status_short,
        "status_short_relevant": "\n".join(relevant),
        "ignored_dirty_prefixes": [".codex/"],
    }


def numpy_config_text() -> str:
    stream = io.StringIO()
    with contextlib.redirect_stdout(stream):
        try:
            np.__config__.show()
        except Exception as exc:  # pragma: no cover - metadata best effort
            print(f"numpy.__config__.show failed: {exc!r}")
    return stream.getvalue()


def total_memory_bytes() -> int | None:
    try:
        page_size = os.sysconf("SC_PAGE_SIZE")
        page_count = os.sysconf("SC_PHYS_PAGES")
        return int(page_size) * int(page_count)
    except (AttributeError, OSError, ValueError):
        return None


def environment_metadata() -> dict:
    local_now = datetime.now().astimezone()
    offset = local_now.utcoffset()
    return {
        "hostname": platform.node(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "processor": platform.processor(),
        "python_executable": sys.executable,
        "python_version": sys.version,
        "sage_version": SAGE_VERSION,
        "numpy_version": np.__version__,
        "sage_executable": shutil.which("sage"),
        "uname": list(os.uname()) if hasattr(os, "uname") else None,
        "pid": os.getpid(),
        "ppid": os.getppid(),
        "cpu_count": os.cpu_count(),
        "total_memory_bytes": total_memory_bytes(),
        "timezone_name": local_now.tzname(),
        "timezone_utc_offset_seconds": int(offset.total_seconds()) if offset else None,
        "env_allowlist": {key: os.environ.get(key) for key in ENV_ALLOWLIST if key in os.environ},
        "numpy_config": numpy_config_text(),
    }


def tool_versions() -> dict:
    return {
        "sage": SAGE_VERSION,
        "python": sys.version,
        "numpy": np.__version__,
    }


def chunk_path(index: int) -> Path:
    return CHUNK_DIR / f"chunk-{index:07d}-{index + 1:07d}.json"


def sector_labels(labels: tuple[str, ...], index: int) -> tuple[str, str, str]:
    total = len(labels) ** 3
    if index < 0 or index >= total:
        raise ValueError(f"sector index {index} outside [0, {total})")
    first = index // (len(labels) ** 2)
    second = (index // len(labels)) % len(labels)
    third = index % len(labels)
    return labels[first], labels[second], labels[third]


def all_sector_labels(labels: tuple[str, ...]):
    return product(labels, repeat=3)


def effective_problem(evaluator, braid: dict, fixed_labels: tuple[str, ...]) -> dict:
    n_strands = int(braid["n_strands"])
    braid_word = tuple(int(item) for item in braid["braid_word"])
    framings = tuple(int(item) for item in braid["framings_in_braid_order"])
    components, strand_to_component = evaluator.component_data(n_strands, braid_word)
    if len(fixed_labels) != len(components):
        raise ValueError("fixed label count does not match braid closure component count")

    if any(label == evaluator.unit for label in fixed_labels):
        nonunit_components = {
            index for index, label in enumerate(fixed_labels) if label != evaluator.unit
        }
        if not nonunit_components:
            return {
                "unit_pruned": True,
                "selected_component_count": 0,
                "selected_strand_count": 0,
                "subbraid_word_length": 0,
                "effective_n_strands": 0,
                "effective_braid_word": [],
                "effective_component_labels": [],
                "effective_framings": [],
            }
        selected_strands = {
            strand
            for strand, component_index in enumerate(strand_to_component)
            if component_index in nonunit_components
        }
        selected_strand_list = tuple(sorted(selected_strands))
        subword, selected_strand_count = evaluator.selected_subbraid_word(
            n_strands,
            braid_word,
            selected_strands,
        )
        sub_components, _ = evaluator.component_data(selected_strand_count, subword)
        sub_original_components = []
        for sub_component in sub_components:
            original_components = {
                strand_to_component[selected_strand_list[sub_strand]]
                for sub_strand in sub_component
            }
            if len(original_components) != 1:
                raise ValueError(f"selected subbraid mixes components: {sorted(original_components)}")
            sub_original_components.append(original_components.pop())
        return {
            "unit_pruned": True,
            "selected_component_count": len(nonunit_components),
            "selected_strand_count": selected_strand_count,
            "subbraid_word_length": len(subword),
            "effective_n_strands": selected_strand_count,
            "effective_braid_word": list(subword),
            "effective_component_labels": [fixed_labels[index] for index in sub_original_components],
            "effective_framings": [framings[index] for index in sub_original_components],
        }

    return {
        "unit_pruned": False,
        "selected_component_count": len(fixed_labels),
        "selected_strand_count": n_strands,
        "subbraid_word_length": len(braid_word),
        "effective_n_strands": n_strands,
        "effective_braid_word": list(braid_word),
        "effective_component_labels": list(fixed_labels),
        "effective_framings": list(framings),
    }


def path_profile(evaluator, effective: dict) -> dict:
    n_strands = int(effective["effective_n_strands"])
    braid_word = tuple(int(item) for item in effective["effective_braid_word"])
    component_labels = tuple(effective["effective_component_labels"])
    if n_strands == 0:
        return {
            "total_charge_count": 1,
            "max_basis_size": 1,
            "sum_basis_size": 1,
            "basis_sizes_by_total": {evaluator.unit: 1},
            "difficulty_score": 0,
            "max_state_size_proxy": 1,
        }

    _, strand_to_component = evaluator.component_data(n_strands, braid_word)
    strand_labels = tuple(component_labels[strand_to_component[strand]] for strand in range(n_strands))
    basis_sizes_by_total = {}
    for total_charge in evaluator.labels:
        size = len(evaluator.paths(strand_labels, total_charge))
        if size:
            basis_sizes_by_total[total_charge] = size
    max_basis_size = max(basis_sizes_by_total.values(), default=0)
    sum_basis_size = sum(basis_sizes_by_total.values())
    word_factor = max(1, int(effective["subbraid_word_length"]))
    return {
        "total_charge_count": len(basis_sizes_by_total),
        "max_basis_size": max_basis_size,
        "sum_basis_size": sum_basis_size,
        "basis_sizes_by_total": basis_sizes_by_total,
        "difficulty_score": (max_basis_size ** 2) * word_factor,
        "max_state_size_proxy": max_basis_size ** 2,
    }


def manifest_entry(evaluator, braid: dict, index: int, fixed_labels: tuple[str, ...]) -> dict:
    effective = effective_problem(evaluator, braid, fixed_labels)
    profile = path_profile(evaluator, effective)
    entry = {
        "sector_index": index,
        "fixed_component_labels": list(fixed_labels),
        "unit_pruned": effective["unit_pruned"],
        "selected_component_count": effective["selected_component_count"],
        "selected_strand_count": effective["selected_strand_count"],
        "subbraid_word_length": effective["subbraid_word_length"],
        "effective_component_labels": effective["effective_component_labels"],
        "effective_framings": effective["effective_framings"],
    }
    entry.update(profile)
    return entry


def write_manifest(args: argparse.Namespace) -> int:
    utc_start = datetime.now(UTC).isoformat()
    wall_start = time.monotonic()
    mtc = read_json(args.mtc)
    braid = read_json(args.braid_payload)
    evaluator = base.DA4FRBraidEvaluator(mtc)

    entries = [
        manifest_entry(evaluator, braid, index, tuple(labels))
        for index, labels in enumerate(all_sector_labels(evaluator.labels))
    ]
    entries.sort(
        key=lambda entry: (
            entry["difficulty_score"],
            entry["max_basis_size"],
            entry["sum_basis_size"],
            entry["subbraid_word_length"],
            entry["selected_strand_count"],
            entry["sector_index"],
        )
    )
    for rank, entry in enumerate(entries):
        entry["priority_rank"] = rank

    payload = {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-da4-untwisted-singleton-manifest.v1",
        "status": "manifest-complete",
        "generator_script": rel(Path(__file__)),
        "base_evaluator_script": rel(BASE_EVALUATOR_SCRIPT),
        "argv": sys.argv[1:],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage '
            "experiments/sage/yasui_figure3_a1_r1_normalized_da4_untwisted_singletons.sage.py "
            "--write-manifest"
        ),
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - wall_start,
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
        "environment": environment_metadata(),
        "source": {
            "mtc_artifact": rel(args.mtc),
            "mtc_sha256": base.file_sha256(args.mtc),
            "braid_payload": rel(args.braid_payload),
            "braid_payload_sha256": base.file_sha256(args.braid_payload),
            "n_strands": int(braid["n_strands"]),
            "braid_word_length": len(braid["braid_word"]),
            "component_order_in_braid": braid["component_order_in_braid"],
            "framings_in_braid_order": braid["framings_in_braid_order"],
        },
        "mtc_id": mtc["mtc_id"],
        "category_id": "omega0_untwisted_D_A4",
        "link_id": "yasui-figure3-a1-r1-normalized",
        "yetter_twist": "none",
        "sector_total": len(evaluator.labels) ** 3,
        "simple_labels": list(evaluator.labels),
        "priority_order_strategy": (
            "Sort by difficulty_score=max_basis_size^2*max(1,subbraid_word_length) "
            "after unit pruning, then max_basis_size, sum_basis_size, subbraid_word_length, "
            "selected_strand_count, sector_index. This is a heuristic scheduling order, not a proof."
        ),
        "entries": entries,
        "summary": {
            "unit_pruned_count": sum(1 for entry in entries if entry["unit_pruned"]),
            "max_basis_size": max(entry["max_basis_size"] for entry in entries),
            "max_sum_basis_size": max(entry["sum_basis_size"] for entry in entries),
            "max_difficulty_score": max(entry["difficulty_score"] for entry in entries),
            "p50_max_basis_size": sorted(entry["max_basis_size"] for entry in entries)[len(entries) // 2],
            "p90_max_basis_size": sorted(entry["max_basis_size"] for entry in entries)[int(len(entries) * 0.9)],
            "p99_max_basis_size": sorted(entry["max_basis_size"] for entry in entries)[int(len(entries) * 0.99)],
        },
        "claim_boundary": (
            "Numeric singleton scheduling/profile artifact for the untwisted D(A4) evaluator only; "
            "not a theorem-level invariant certificate."
        ),
    }
    write_json(args.manifest_output, payload)
    print(
        json.dumps(
            {
                "phase": "manifest-complete",
                "artifact": rel(args.manifest_output),
                "elapsed_seconds": payload["elapsed_seconds"],
                "sector_total": payload["sector_total"],
                "max_basis_size": payload["summary"]["max_basis_size"],
            },
            sort_keys=True,
        ),
        flush=True,
    )
    return 0


def load_manifest_entry(manifest_path: Path, index: int) -> dict | None:
    if not manifest_path.exists():
        return None
    manifest = read_json(manifest_path)
    for entry in manifest.get("entries", []):
        if int(entry["sector_index"]) == int(index):
            return entry
    return None


def compute_singleton(args: argparse.Namespace) -> dict:
    mtc = read_json(args.mtc)
    braid = read_json(args.braid_payload)
    evaluator = base.DA4FRBraidEvaluator(mtc)
    fixed_labels = sector_labels(evaluator.labels, int(args.sector_index))
    run_context = {
        "mode": "singleton",
        "worker_id": args.worker_id,
        "run_label": args.run_label,
        "repo_before_write": repo_metadata(),
        "tool_versions": tool_versions(),
        "environment": environment_metadata(),
    }

    utc_start = datetime.now(UTC).isoformat()
    wall_start = time.monotonic()
    amplitude, stats = evaluator.fixed_label_value(
        int(braid["n_strands"]),
        tuple(int(item) for item in braid["braid_word"]),
        tuple(fixed_labels),
        tuple(int(item) for item in braid["framings_in_braid_order"]),
    )
    coefficient = math.prod(evaluator.dimension(label) for label in fixed_labels)
    weighted = coefficient * amplitude
    elapsed = time.monotonic() - wall_start
    manifest = load_manifest_entry(args.manifest, int(args.sector_index))
    payload = {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-da4-untwisted-singleton.v1",
        "status": "computed-numeric",
        "generator_script": rel(Path(__file__)),
        "base_evaluator_script": rel(BASE_EVALUATOR_SCRIPT),
        "argv": sys.argv[1:],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage '
            "experiments/sage/yasui_figure3_a1_r1_normalized_da4_untwisted_singletons.sage.py "
            f"--sector-index {int(args.sector_index)} --worker-id {args.worker_id}"
        ),
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": elapsed,
        "kind": "fixed-label-sector",
        "mtc_id": mtc["mtc_id"],
        "category_id": "omega0_untwisted_D_A4",
        "link_id": "yasui-figure3-a1-r1-normalized",
        "yetter_twist": "none",
        "sector_index": int(args.sector_index),
        "sector_total": len(evaluator.labels) ** 3,
        "fixed_component_labels": list(fixed_labels),
        "component_order_in_braid": braid["component_order_in_braid"],
        "untwisted_coefficient": repr(float(coefficient)),
        "fixed_sector_amplitude": base.complex_json(amplitude),
        "weighted_untwisted_contribution": base.complex_json(weighted),
        "evaluator_stats": stats,
        "manifest_entry": manifest,
        "source": {
            "mtc_artifact": rel(args.mtc),
            "mtc_sha256": base.file_sha256(args.mtc),
            "braid_payload": rel(args.braid_payload),
            "braid_payload_sha256": base.file_sha256(args.braid_payload),
            "n_strands": int(braid["n_strands"]),
            "braid_word_length": len(braid["braid_word"]),
            "framings_in_braid_order": braid["framings_in_braid_order"],
            "component_order_in_braid": braid["component_order_in_braid"],
        },
        "repo": run_context["repo_before_write"],
        "tool_versions": run_context["tool_versions"],
        "environment": run_context["environment"],
        "run_context": run_context,
        "claim_boundary": (
            "Numeric fixed-label singleton for the untwisted D(A4) evaluator only; "
            "not an exact theorem-level certificate."
        ),
    }
    artifact = chunk_path(int(args.sector_index))
    if artifact.exists() and not args.force:
        raise FileExistsError(f"{artifact} exists; pass --force to overwrite")
    write_json(artifact, payload)
    payload["artifact"] = rel(artifact)
    return payload


def run_singleton(args: argparse.Namespace) -> int:
    payload = compute_singleton(args)
    print(
        json.dumps(
            {
                "phase": "singleton-complete",
                "sector_index": payload["sector_index"],
                "fixed_component_labels": payload["fixed_component_labels"],
                "artifact": payload["artifact"],
                "elapsed_seconds": payload["elapsed_seconds"],
                "max_basis_size": payload["evaluator_stats"].get("max_basis_size"),
                "max_state_size": payload["evaluator_stats"].get("max_state_size"),
            },
            sort_keys=True,
        ),
        flush=True,
    )
    return 0


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mtc", type=Path, default=MTC_PATH)
    parser.add_argument("--braid-payload", type=Path, default=BRAID_PAYLOAD_PATH)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--manifest-output", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--probe-summary-output", type=Path, default=PROBE_SUMMARY_PATH)
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--sector-index", type=int)
    parser.add_argument("--worker-id", default=f"local-{os.getpid()}")
    parser.add_argument("--run-label", default="manual")
    parser.add_argument("--force", action="store_true")
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    args.mtc = args.mtc.resolve()
    args.braid_payload = args.braid_payload.resolve()
    args.manifest = args.manifest.resolve()
    args.manifest_output = args.manifest_output.resolve()
    args.probe_summary_output = args.probe_summary_output.resolve()
    if args.write_manifest:
        return write_manifest(args)
    if args.sector_index is None:
        raise SystemExit("pass --write-manifest or --sector-index")
    return run_singleton(args)


if __name__ == "__main__":
    raise SystemExit(main())
