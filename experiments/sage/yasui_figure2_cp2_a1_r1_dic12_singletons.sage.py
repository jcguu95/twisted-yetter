"""Yasui Figure 2 CP2(a=1, R1-normalized) D(Dic_12) singleton runner.

This is a floating-point operational harness.  It reuses the generic numeric
F/R braid evaluator used for the D(A4) and previous D(Dic_12) Yasui runs, but
feeds it the R1-normalized Yasui Figure 2 braid.  The first intended use is
profiling: build the priority manifest, time representative singleton sectors,
then decide how to distribute the full 32768-sector run.
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
    / "drinfeld-double-dic12-omega0-mtc-fr-data-v1.json"
)
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "yasui"
CHUNK_DIR = RESULT_DIR / "figure2-cp2-a1-r1-dic12-omega0-singleton-chunks-v1"
MANIFEST_PATH = RESULT_DIR / "figure2-cp2-a1-r1-dic12-omega0-singleton-manifest-v1.json"
PROFILE_DIR = RESULT_DIR / "figure2-cp2-a1-r1-dic12-omega0-profiles-v1"
RANGE_AGGREGATE_DIR = RESULT_DIR / "figure2-cp2-a1-r1-dic12-omega0-range-aggregates-v1"

N_STRANDS = 5
BRAID_WORD = (
    1,
    1,
    2,
    3,
    3,
    2,
    1,
    2,
    3,
    2,
    2,
    -4,
    3,
    2,
    1,
    2,
    3,
    3,
    2,
    3,
    4,
    -3,
)
COMPONENT_ORDER_IN_BRAID = ("A", "C", "B")
TOTAL_FRAMINGS_IN_BRAID_ORDER = (4, 4, 1)
H2_PULLBACK_IN_BRAID_ORDER = (2, 2, 1)
WITNESS_ORDER = 4

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


base = load_module(BASE_EVALUATOR_SCRIPT, "generic_fr_braid_evaluator_for_yasui_figure2_dic12")


def command(argv: list[str]) -> str:
    return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()


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


def complex_json(value: complex) -> dict[str, str]:
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def parse_complex(payload: dict) -> complex:
    return complex(float(payload["real"]), float(payload["imag"]))


def repo_metadata() -> dict:
    status_short = optional_command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": optional_command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(status_short),
        "status_short": status_short,
    }


def numpy_config_text() -> str:
    stream = io.StringIO()
    with contextlib.redirect_stdout(stream):
        try:
            np.__config__.show()
        except Exception as exc:
            print(f"numpy.__config__.show failed: {exc!r}")
    return stream.getvalue()


def total_memory_bytes() -> int | None:
    try:
        return int(os.sysconf("SC_PAGE_SIZE")) * int(os.sysconf("SC_PHYS_PAGES"))
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
    return {"sage": SAGE_VERSION, "python": sys.version, "numpy": np.__version__}


def braid_payload() -> dict:
    return {
        "n_strands": N_STRANDS,
        "braid_word": list(BRAID_WORD),
        "braid_word_length": len(BRAID_WORD),
        "component_order_in_braid": list(COMPONENT_ORDER_IN_BRAID),
        "total_framings_in_braid_order": list(TOTAL_FRAMINGS_IN_BRAID_ORDER),
        "h2_pullback_in_braid_order": list(H2_PULLBACK_IN_BRAID_ORDER),
        "normalization": {
            "tham511_upside_down_factor": "divide raw Yasui RT value by D^2",
            "source_three_handles": 2,
            "dual_one_handles": 2,
        },
    }


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


def effective_problem(evaluator, fixed_labels: tuple[str, ...]) -> dict:
    components, strand_to_component = evaluator.component_data(N_STRANDS, BRAID_WORD)
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
            N_STRANDS,
            BRAID_WORD,
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
            "effective_framings": [TOTAL_FRAMINGS_IN_BRAID_ORDER[index] for index in sub_original_components],
        }
    return {
        "unit_pruned": False,
        "selected_component_count": len(fixed_labels),
        "selected_strand_count": N_STRANDS,
        "subbraid_word_length": len(BRAID_WORD),
        "effective_n_strands": N_STRANDS,
        "effective_braid_word": list(BRAID_WORD),
        "effective_component_labels": list(fixed_labels),
        "effective_framings": list(TOTAL_FRAMINGS_IN_BRAID_ORDER),
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
        "difficulty_score": (max_basis_size**2) * word_factor,
        "max_state_size_proxy": max_basis_size**2,
    }


def manifest_entry(evaluator, index: int, fixed_labels: tuple[str, ...]) -> dict:
    effective = effective_problem(evaluator, fixed_labels)
    profile = path_profile(evaluator, effective)
    entry = {
        "sector_index": index,
        "fixed_component_labels": list(fixed_labels),
        "component_order_in_braid": list(COMPONENT_ORDER_IN_BRAID),
        "unit_pruned": effective["unit_pruned"],
        "selected_component_count": effective["selected_component_count"],
        "selected_strand_count": effective["selected_strand_count"],
        "subbraid_word_length": effective["subbraid_word_length"],
        "effective_component_labels": effective["effective_component_labels"],
        "effective_framings": effective["effective_framings"],
    }
    entry.update(profile)
    return entry


def load_mtc_and_evaluator(args: argparse.Namespace):
    mtc = read_json(args.mtc)
    evaluator = base.DA4FRBraidEvaluator(mtc)
    return mtc, evaluator


def write_manifest(args: argparse.Namespace) -> int:
    utc_start = datetime.now(UTC).isoformat()
    wall_start = time.monotonic()
    mtc, evaluator = load_mtc_and_evaluator(args)
    entries = [
        manifest_entry(evaluator, index, tuple(labels))
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
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-r1-dic12-singleton-manifest.v1",
        "status": "manifest-complete",
        "mathematical_status": "OPERATIONAL_PROFILE_NOT_THEOREM",
        "generator_script": rel(Path(__file__)),
        "base_evaluator_script": rel(BASE_EVALUATOR_SCRIPT),
        "argv": sys.argv[1:],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage '
            "experiments/sage/yasui_figure2_cp2_a1_r1_dic12_singletons.sage.py --write-manifest"
        ),
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - wall_start,
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
        "environment": environment_metadata(),
        "source": {
            "mtc_artifact": rel(args.mtc),
            "mtc_sha256": run_context["mtc_sha256"],
            **braid_payload(),
        },
        "mtc_id": mtc["mtc_id"],
        "category_id": "omega0_untwisted_D_Dic12",
        "link_id": "yasui-figure2-cp2-a1-r1",
        "sector_total": len(evaluator.labels) ** 3,
        "simple_labels": list(evaluator.labels),
        "priority_order_strategy": (
            "Sort by difficulty_score=max_basis_size^2*max(1,subbraid_word_length) "
            "after unit pruning, then max_basis_size, sum_basis_size, subbraid_word_length, "
            "selected_strand_count, sector_index. This is a scheduling heuristic."
        ),
        "summary": {
            "unit_pruned_count": sum(1 for entry in entries if entry["unit_pruned"]),
            "max_basis_size": max(entry["max_basis_size"] for entry in entries),
            "max_sum_basis_size": max(entry["sum_basis_size"] for entry in entries),
            "max_difficulty_score": max(entry["difficulty_score"] for entry in entries),
            "p50_max_basis_size": sorted(entry["max_basis_size"] for entry in entries)[len(entries) // 2],
            "p90_max_basis_size": sorted(entry["max_basis_size"] for entry in entries)[int(len(entries) * 0.9)],
            "p99_max_basis_size": sorted(entry["max_basis_size"] for entry in entries)[int(len(entries) * 0.99)],
        },
        "entries": entries,
    }
    write_json(args.manifest, payload)
    print(
        json.dumps(
            {
                "phase": "manifest-complete",
                "artifact": rel(args.manifest),
                "sector_total": payload["sector_total"],
                "summary": payload["summary"],
                "elapsed_seconds": payload["elapsed_seconds"],
            },
            sort_keys=True,
        )
    )
    return 0


def chunk_path(index: int) -> Path:
    return CHUNK_DIR / f"chunk-{index:07d}-{index + 1:07d}.json"


def compute_singleton(
    args: argparse.Namespace,
    mtc: dict,
    evaluator,
    manifest_by_index: dict[int, dict],
    index: int,
    run_context: dict,
) -> dict:
    fixed_labels = sector_labels(evaluator.labels, index)
    utc_start = datetime.now(UTC).isoformat()
    wall_start = time.monotonic()
    amplitude, stats = evaluator.fixed_label_value(
        N_STRANDS,
        BRAID_WORD,
        fixed_labels,
        TOTAL_FRAMINGS_IN_BRAID_ORDER,
    )
    coefficient = math.prod(evaluator.dimension(label) for label in fixed_labels)
    weighted = coefficient * amplitude
    elapsed = time.monotonic() - wall_start
    payload = {
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-r1-dic12-singleton-sector.v1",
        "status": "computed-numeric",
        "mathematical_status": "FLOATING_POINT_SECTOR_VALUE_NOT_THEOREM",
        "generator_script": rel(Path(__file__)),
        "base_evaluator_script": rel(BASE_EVALUATOR_SCRIPT),
        "argv": sys.argv[1:],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage '
            "experiments/sage/yasui_figure2_cp2_a1_r1_dic12_singletons.sage.py "
            f"--sector-index {index} --force"
        ),
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": elapsed,
        "mtc_id": mtc["mtc_id"],
        "category_id": "omega0_untwisted_D_Dic12",
        "link_id": "yasui-figure2-cp2-a1-r1",
        "sector_index": index,
        "sector_total": len(evaluator.labels) ** 3,
        "fixed_component_labels": list(fixed_labels),
        "component_order_in_braid": list(COMPONENT_ORDER_IN_BRAID),
        "untwisted_coefficient": repr(float(coefficient)),
        "fixed_sector_amplitude": complex_json(amplitude),
        "weighted_untwisted_contribution": complex_json(weighted),
        "evaluator_stats": stats,
        "manifest_entry": manifest_by_index.get(index),
        "source": {
            "mtc_artifact": rel(args.mtc),
            "mtc_sha256": base.file_sha256(args.mtc),
            **braid_payload(),
        },
        "repo": run_context["repo"],
        "tool_versions": run_context["tool_versions"],
        "environment": run_context["environment"],
        "run_context": run_context,
    }
    artifact = chunk_path(index)
    if artifact.exists() and not args.force:
        raise FileExistsError(f"{artifact} exists; pass --force to overwrite")
    write_json(artifact, payload)
    payload["artifact"] = rel(artifact)
    return payload


def load_manifest_by_index(path: Path) -> tuple[dict, dict[int, dict]]:
    manifest = read_json(path)
    return manifest, {int(entry["sector_index"]): entry for entry in manifest["entries"]}


def ranks_to_indices(manifest: dict, ranks: list[int]) -> list[int]:
    by_rank = {int(entry["priority_rank"]): int(entry["sector_index"]) for entry in manifest["entries"]}
    max_rank = max(by_rank)
    indices = []
    for rank in ranks:
        normalized = min(max(int(rank), 0), max_rank)
        indices.append(by_rank[normalized])
    return indices


def run_indices(args: argparse.Namespace, indices: list[int], label: str) -> int:
    utc_start = datetime.now(UTC).isoformat()
    wall_start = time.monotonic()
    load_start = time.monotonic()
    mtc, evaluator = load_mtc_and_evaluator(args)
    hot_load_elapsed = time.monotonic() - load_start
    manifest, manifest_by_index = load_manifest_by_index(args.manifest)
    run_context = {
        "mode": "profile-ranks" if args.profile_ranks else "singleton",
        "profile_label": label,
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
        "environment": environment_metadata(),
        "hot_evaluator_load_elapsed_seconds": hot_load_elapsed,
        "mtc_sha256": base.file_sha256(args.mtc),
    }
    processed = []
    skipped = []
    for index in indices:
        artifact = chunk_path(index)
        if artifact.exists() and args.skip_existing:
            entry = manifest_by_index.get(index) or {}
            skipped.append(
                {
                    "sector_index": index,
                    "priority_rank": entry.get("priority_rank"),
                    "difficulty_score": entry.get("difficulty_score"),
                    "reason": "preexisting-artifact",
                    "artifact": rel(artifact),
                }
            )
            continue
        payload = compute_singleton(args, mtc, evaluator, manifest_by_index, index, run_context)
        entry = manifest_by_index.get(index) or {}
        processed.append(
            {
                "sector_index": index,
                "priority_rank": entry.get("priority_rank"),
                "difficulty_score": entry.get("difficulty_score"),
                "fixed_component_labels": payload["fixed_component_labels"],
                "elapsed_seconds": payload["elapsed_seconds"],
                "max_basis_size": payload["evaluator_stats"].get("max_basis_size"),
                "max_state_size": payload["evaluator_stats"].get("max_state_size"),
                "artifact": payload["artifact"],
            }
        )
        if not args.quiet:
            print(json.dumps(processed[-1], sort_keys=True), flush=True)
    profile = {
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-r1-dic12-profile.v1",
        "status": "complete",
        "mathematical_status": "OPERATIONAL_PROFILE_NOT_THEOREM",
        "generator_script": rel(Path(__file__)),
        "base_evaluator_script": rel(BASE_EVALUATOR_SCRIPT),
        "argv": sys.argv[1:],
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_wall_seconds": time.monotonic() - wall_start,
        "hot_evaluator_load_elapsed_seconds": hot_load_elapsed,
        "profile_label": label,
        "requested_indices": indices,
        "processed_count": len(processed),
        "skipped_count": len(skipped),
        "processed": processed,
        "skipped": skipped,
        "manifest": {
            "path": rel(args.manifest),
            "sector_total": manifest["sector_total"],
            "summary": manifest["summary"],
        },
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
        "environment": environment_metadata(),
    }
    profile_path = PROFILE_DIR / f"{label}-profile-v1.json"
    write_json(profile_path, profile)
    print(
        json.dumps(
            {
                "phase": "profile-complete",
                "profile": rel(profile_path),
                "processed_count": len(processed),
                "skipped_count": len(skipped),
                "elapsed_wall_seconds": profile["elapsed_wall_seconds"],
            },
            sort_keys=True,
        )
    )
    return 0


def witness_chi_on_class(class_name: str) -> complex:
    return complex({"1A": 1, "aA": -1, "a2A": 1, "a3A": -1, "xA": 1j, "axA": -1j}[class_name])


def witness_z_scalar(rep: str) -> complex:
    for prefix in ("lin", "rho", "chi", "eta"):
        if rep.startswith(prefix):
            return complex((-1) ** int(rep[len(prefix) :]))
    raise ValueError(f"unknown Dic12 centralizer irrep label {rep!r}")


def witness_monodromy(label: str) -> complex:
    class_name, rep = label.split(":", 1)
    return witness_chi_on_class(class_name) * witness_z_scalar(rep)


def standard_cp2_rows(mtc: dict, evaluator) -> list[dict]:
    global_dimension = sum(evaluator.dimension(label) ** 2 for label in evaluator.labels)
    rows = []
    for h_power in range(WITNESS_ORDER):
        value = 0j
        for label in evaluator.labels:
            dim = evaluator.dimension(label)
            value += (
                dim
                * dim
                * (witness_monodromy(label) ** h_power)
                * evaluator.twist(label)
            )
        rows.append(
            {
                "h_power": h_power,
                "standard_cp2_plus_one_omega": complex_json(value),
                "ratio_to_untwisted": None,
                "global_dimension_D": repr(float(global_dimension)),
            }
        )
    untwisted = parse_complex(rows[0]["standard_cp2_plus_one_omega"])
    for row in rows:
        row["ratio_to_untwisted"] = complex_json(parse_complex(row["standard_cp2_plus_one_omega"]) / untwisted)
    return rows


def rank_entries(manifest: dict, rank_start: int, rank_count: int) -> list[dict]:
    entries_by_rank = {int(entry["priority_rank"]): entry for entry in manifest["entries"]}
    max_rank = max(entries_by_rank)
    ranks = range(rank_start, min(rank_start + rank_count, max_rank + 1))
    return [entries_by_rank[rank] for rank in ranks]


def range_aggregate(args: argparse.Namespace) -> int:
    if args.rank_start is None or args.rank_count is None:
        raise SystemExit("range aggregate requires --rank-start and --rank-count")
    utc_start = datetime.now(UTC).isoformat()
    wall_start = time.monotonic()
    load_start = time.monotonic()
    mtc, evaluator = load_mtc_and_evaluator(args)
    hot_load_elapsed = time.monotonic() - load_start
    manifest, _ = load_manifest_by_index(args.manifest)
    entries = rank_entries(manifest, args.rank_start, args.rank_count)
    global_dimension = sum(evaluator.dimension(label) ** 2 for label in evaluator.labels)
    raw_by_power = [0j for _ in range(WITNESS_ORDER)]
    elapsed_values = []
    slowest = []
    processed = 0
    for entry in entries:
        fixed_labels = tuple(entry["fixed_component_labels"])
        sector_index = int(entry["sector_index"])
        sector_start = time.monotonic()
        amplitude, stats = evaluator.fixed_label_value(
            N_STRANDS,
            BRAID_WORD,
            fixed_labels,
            TOTAL_FRAMINGS_IN_BRAID_ORDER,
        )
        coefficient = math.prod(evaluator.dimension(label) for label in fixed_labels)
        weighted = coefficient * amplitude
        elapsed = time.monotonic() - sector_start
        elapsed_values.append(elapsed)
        processed += 1
        for h_power in range(WITNESS_ORDER):
            component_powers = [
                (h_power * pullback) % WITNESS_ORDER
                for pullback in H2_PULLBACK_IN_BRAID_ORDER
            ]
            factor = 1 + 0j
            for label, power in zip(fixed_labels, component_powers, strict=True):
                factor *= witness_monodromy(label) ** power
            raw_by_power[h_power] += weighted * factor
        if len(slowest) < 20 or elapsed > slowest[0]["elapsed_seconds"]:
            slowest.append(
                {
                    "sector_index": sector_index,
                    "priority_rank": int(entry["priority_rank"]),
                    "difficulty_score": int(entry["difficulty_score"]),
                    "fixed_component_labels": list(fixed_labels),
                    "elapsed_seconds": elapsed,
                    "max_basis_size": stats.get("max_basis_size"),
                    "max_state_size": stats.get("max_state_size"),
                }
            )
            slowest = sorted(slowest, key=lambda row: row["elapsed_seconds"], reverse=True)[:20]
    normalized_rows = []
    for h_power, raw in enumerate(raw_by_power):
        normalized_rows.append(
            {
                "h_power": h_power,
                "component_powers_in_braid_order": [
                    (h_power * pullback) % WITNESS_ORDER
                    for pullback in H2_PULLBACK_IN_BRAID_ORDER
                ],
                "raw_partial_sum": complex_json(raw),
                "normalized_partial_sum_by_D_squared": complex_json(raw / (global_dimension * global_dimension)),
            }
        )
    elapsed_sorted = sorted(elapsed_values)
    elapsed_summary = {
        "count": len(elapsed_values),
        "sum": repr(float(sum(elapsed_values))),
        "min": repr(float(elapsed_sorted[0])) if elapsed_sorted else None,
        "median": repr(float(elapsed_sorted[len(elapsed_sorted) // 2])) if elapsed_sorted else None,
        "p90": repr(float(elapsed_sorted[int(len(elapsed_sorted) * 0.9)])) if elapsed_sorted else None,
        "p99": repr(float(elapsed_sorted[int(len(elapsed_sorted) * 0.99)])) if elapsed_sorted else None,
        "max": repr(float(elapsed_sorted[-1])) if elapsed_sorted else None,
    }
    payload = {
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-r1-dic12-range-aggregate.v1",
        "status": "complete",
        "mathematical_status": "FLOATING_POINT_RANGE_AGGREGATE_NOT_THEOREM",
        "generator_script": rel(Path(__file__)),
        "base_evaluator_script": rel(BASE_EVALUATOR_SCRIPT),
        "argv": sys.argv[1:],
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_wall_seconds": time.monotonic() - wall_start,
        "hot_evaluator_load_elapsed_seconds": hot_load_elapsed,
        "rank_start": args.rank_start,
        "rank_count_requested": args.rank_count,
        "processed_count": processed,
        "rank_stop_exclusive": args.rank_start + processed,
        "global_dimension_D": repr(float(global_dimension)),
        "global_dimension_D_squared": repr(float(global_dimension * global_dimension)),
        "rows": normalized_rows,
        "elapsed_seconds_summary": elapsed_summary,
        "slowest_20": slowest,
        "source": {
            "mtc_artifact": rel(args.mtc),
            "mtc_sha256": base.file_sha256(args.mtc),
            **braid_payload(),
        },
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
        "environment": environment_metadata(),
    }
    output = RANGE_AGGREGATE_DIR / f"{args.profile_label}-range-aggregate-v1.json"
    write_json(output, payload)
    print(
        json.dumps(
            {
                "phase": "range-aggregate-complete",
                "artifact": rel(output),
                "processed_count": processed,
                "elapsed_wall_seconds": payload["elapsed_wall_seconds"],
                "elapsed_seconds_summary": elapsed_summary,
            },
            sort_keys=True,
        )
    )
    return 0


def combine_range_aggregates(args: argparse.Namespace) -> int:
    utc_start = datetime.now(UTC).isoformat()
    mtc, evaluator = load_mtc_and_evaluator(args)
    global_dimension = sum(evaluator.dimension(label) ** 2 for label in evaluator.labels)
    aggregate_paths = sorted(RANGE_AGGREGATE_DIR.glob("*-range-aggregate-v1.json"))
    raw_by_power = [0j for _ in range(WITNESS_ORDER)]
    covered_ranks = set()
    inputs = []
    for path in aggregate_paths:
        record = read_json(path)
        inputs.append(
            {
                "path": rel(path),
                "rank_start": record["rank_start"],
                "rank_stop_exclusive": record["rank_stop_exclusive"],
                "processed_count": record["processed_count"],
                "elapsed_wall_seconds": record["elapsed_wall_seconds"],
            }
        )
        covered_ranks.update(range(int(record["rank_start"]), int(record["rank_stop_exclusive"])))
        for row in record["rows"]:
            raw_by_power[int(row["h_power"])] += parse_complex(row["raw_partial_sum"])
    standard_rows = standard_cp2_rows(mtc, evaluator)
    standard_by_power = {
        row["h_power"]: parse_complex(row["standard_cp2_plus_one_omega"])
        for row in standard_rows
    }
    yasui_rows = []
    for h_power, raw in enumerate(raw_by_power):
        normalized = raw / (global_dimension * global_dimension)
        diff = normalized - standard_by_power[h_power]
        yasui_rows.append(
            {
                "h_power": h_power,
                "component_powers_in_braid_order": [
                    (h_power * pullback) % WITNESS_ORDER
                    for pullback in H2_PULLBACK_IN_BRAID_ORDER
                ],
                "raw_yasui_sum": complex_json(raw),
                "normalized_by_D_squared": complex_json(normalized),
                "standard_cp2_plus_one_omega": standard_rows[h_power]["standard_cp2_plus_one_omega"],
                "difference_normalized_minus_standard": complex_json(diff),
                "abs_difference": repr(float(abs(diff))),
                "matches_standard_at_1e_minus_7": bool(abs(diff) < 1e-7),
            }
        )
    missing_ranks = [rank for rank in range(len(evaluator.labels) ** 3) if rank not in covered_ranks]
    payload = {
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-r1-dic12-range-combined-aggregate.v1",
        "status": "pass" if not missing_ranks and all(row["matches_standard_at_1e_minus_7"] for row in yasui_rows) else "needs-review",
        "mathematical_status": "FLOATING_POINT_COMPUTATIONAL_CHECK_NOT_THEOREM",
        "generator_script": rel(Path(__file__)),
        "base_evaluator_script": rel(BASE_EVALUATOR_SCRIPT),
        "argv": sys.argv[1:],
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
        "source": {
            "mtc_artifact": rel(args.mtc),
            "mtc_sha256": base.file_sha256(args.mtc),
            **braid_payload(),
        },
        "global_dimension_D": repr(float(global_dimension)),
        "global_dimension_D_squared": repr(float(global_dimension * global_dimension)),
        "input_range_aggregates": inputs,
        "covered_rank_count": len(covered_ranks),
        "missing_rank_count": len(missing_ranks),
        "missing_ranks_first_20": missing_ranks[:20],
        "witness": {
            "order": WITNESS_ORDER,
            "component_power_rule": "for h_power=a, use powers (2a,2a,a) in braid order A,C,B",
        },
        "standard_cp2_rows": standard_rows,
        "yasui_rows": yasui_rows,
    }
    output = RESULT_DIR / "figure2-cp2-a1-r1-dic12-omega0-range-combined-aggregate-v1.json"
    write_json(output, payload)
    print(json.dumps({"phase": "combine", "artifact": rel(output), "status": payload["status"]}, sort_keys=True))
    return 0


def aggregate_from_chunks(args: argparse.Namespace) -> int:
    mtc, evaluator = load_mtc_and_evaluator(args)
    manifest, _ = load_manifest_by_index(args.manifest)
    global_dimension = sum(evaluator.dimension(label) ** 2 for label in evaluator.labels)
    rows_by_power = []
    missing = []
    chunk_paths = sorted(CHUNK_DIR.glob("chunk-*.json"))
    contributions = []
    for path in chunk_paths:
        record = read_json(path)
        contributions.append(record)
    seen = {int(record["sector_index"]) for record in contributions}
    for entry in manifest["entries"]:
        if int(entry["sector_index"]) not in seen:
            missing.append(int(entry["sector_index"]))
    for h_power in range(WITNESS_ORDER):
        component_powers = [
            (h_power * pullback) % WITNESS_ORDER
            for pullback in H2_PULLBACK_IN_BRAID_ORDER
        ]
        raw = 0j
        for record in contributions:
            labels = record["fixed_component_labels"]
            factor = 1 + 0j
            for label, power in zip(labels, component_powers, strict=True):
                factor *= witness_monodromy(label) ** power
            raw += parse_complex(record["weighted_untwisted_contribution"]) * factor
        normalized = raw / (global_dimension * global_dimension)
        rows_by_power.append(
            {
                "h_power": h_power,
                "component_powers_in_braid_order": component_powers,
                "raw_yasui_sum_over_available_chunks": complex_json(raw),
                "normalized_by_D_squared": complex_json(normalized),
            }
        )
    standard_rows = standard_cp2_rows(mtc, evaluator)
    standard_by_power = {row["h_power"]: parse_complex(row["standard_cp2_plus_one_omega"]) for row in standard_rows}
    for row in rows_by_power:
        h_power = row["h_power"]
        diff = parse_complex(row["normalized_by_D_squared"]) - standard_by_power[h_power]
        row["standard_cp2_plus_one_omega"] = standard_rows[h_power]["standard_cp2_plus_one_omega"]
        row["difference_normalized_minus_standard"] = complex_json(diff)
        row["abs_difference"] = repr(float(abs(diff)))
    payload = {
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-r1-dic12-aggregate.v1",
        "status": "complete" if not missing else "partial",
        "mathematical_status": "FLOATING_POINT_AGGREGATE_NOT_THEOREM",
        "generator_script": rel(Path(__file__)),
        "base_evaluator_script": rel(BASE_EVALUATOR_SCRIPT),
        "argv": sys.argv[1:],
        "utc_start": datetime.now(UTC).isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "repo": repo_metadata(),
        "tool_versions": tool_versions(),
        "source": {
            "mtc_artifact": rel(args.mtc),
            "mtc_sha256": base.file_sha256(args.mtc),
            **braid_payload(),
        },
        "global_dimension_D": repr(float(global_dimension)),
        "global_dimension_D_squared": repr(float(global_dimension * global_dimension)),
        "chunk_dir": rel(CHUNK_DIR),
        "available_chunk_count": len(contributions),
        "missing_count": len(missing),
        "missing_sector_indices_first_20": missing[:20],
        "witness": {
            "order": WITNESS_ORDER,
            "component_power_rule": "for h_power=a, use powers (2a,2a,a) in braid order A,C,B",
        },
        "standard_cp2_rows": standard_rows,
        "yasui_rows": rows_by_power,
    }
    output = RESULT_DIR / "figure2-cp2-a1-r1-dic12-omega0-aggregate-v1.json"
    write_json(output, payload)
    print(json.dumps({"phase": "aggregate", "artifact": rel(output), "status": payload["status"]}, sort_keys=True))
    return 0


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mtc", type=Path, default=MTC_PATH)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--sector-index", type=int)
    parser.add_argument("--profile-ranks", nargs="*", type=int)
    parser.add_argument("--rank-start", type=int)
    parser.add_argument("--rank-count", type=int)
    parser.add_argument("--profile-label", default="manual")
    parser.add_argument("--aggregate", action="store_true")
    parser.add_argument("--range-aggregate", action="store_true")
    parser.add_argument("--combine-range-aggregates", action="store_true")
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--skip-existing", action="store_true")
    parser.add_argument("--quiet", action="store_true")
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    args.mtc = args.mtc.resolve()
    args.manifest = args.manifest.resolve()
    if args.write_manifest:
        return write_manifest(args)
    if args.aggregate:
        return aggregate_from_chunks(args)
    if args.combine_range_aggregates:
        return combine_range_aggregates(args)
    if args.range_aggregate:
        return range_aggregate(args)
    if args.rank_start is not None or args.rank_count is not None:
        if args.rank_start is None or args.rank_count is None:
            raise SystemExit("pass both --rank-start and --rank-count")
        manifest, _ = load_manifest_by_index(args.manifest)
        ranks = list(range(args.rank_start, args.rank_start + args.rank_count))
        indices = ranks_to_indices(manifest, ranks)
        return run_indices(args, indices, args.profile_label)
    if args.profile_ranks is not None:
        manifest, _ = load_manifest_by_index(args.manifest)
        indices = ranks_to_indices(manifest, args.profile_ranks)
        return run_indices(args, indices, args.profile_label)
    if args.sector_index is not None:
        return run_indices(args, [args.sector_index], f"sector-{args.sector_index:07d}")
    raise SystemExit("pass --write-manifest, --profile-ranks, --sector-index, or --aggregate")


if __name__ == "__main__":
    raise SystemExit(main())
