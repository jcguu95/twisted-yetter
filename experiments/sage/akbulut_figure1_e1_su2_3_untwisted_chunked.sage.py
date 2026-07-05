"""Chunked SU(2)_3 untwisted comparison for Akbulut Figure 1.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/akbulut_figure1_e1_su2_3_untwisted_chunked.sage.py

This is safer than a single long streaming Sage process.  The parent process
spawns short-lived Sage/Python workers.  Each worker evaluates a contiguous
range of Kirby-color sectors, prints one JSON partial sum, and exits so the OS
can reclaim matrix-cache memory.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

from sage.all import ComplexField


REPO_ROOT = Path(__file__).resolve().parents[2]
BASE_SCRIPT = REPO_ROOT / "experiments" / "sage" / "akbulut_figure1_e1_su2_2_untwisted_comparison.sage.py"
SU2K_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "akbulut"
    / "figure1-e1-su2-3-untwisted-chunked-comparison-v2.json"
)
PARTIAL_DIR = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "akbulut"
    / "figure1-e1-su2-3-untwisted-chunks-v2"
)

LEVEL = 3
PRECISION = 120
CF = ComplexField(PRECISION)
TOLERANCE = CF("1e-8")
DEFAULT_CHUNK_SIZE = 10000


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def complex_json(value):
    value = CF(value)
    return {
        "field": f"ComplexField({PRECISION})",
        "display": str(value),
        "real": str(value.real()),
        "imag": str(value.imag()),
        "abs": str(abs(value)),
    }


def ru_maxrss_mb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / (1024 * 1024)


def build_context():
    base = load_module(BASE_SCRIPT, "akbulut_base_for_su2_3_chunked")
    su2k = load_module(SU2K_PATH, "su2k_for_akbulut_su2_3_chunked")
    evaluator = su2k.SU2KBraidEvaluator(LEVEL, exact=False, precision=PRECISION)
    payload = json.loads(base.INPUT.read_text())
    component_words, crossing_signs, _ = base.source_oriented_gauss_code(payload)
    braid = base.Link([component_words, crossing_signs]).braid()
    n_strands = int(braid.parent().strands())
    braid_word = tuple(int(generator) for generator in braid.Tietze())
    braid_linking = [
        [int(entry) for entry in row]
        for row in base.braid_closure_linking_matrix(n_strands, braid_word)
    ]
    source_order = base.component_order(payload)
    source_target_matrix = base.target_matrix(payload)
    candidates = base.component_permutations(source_target_matrix, braid_linking)
    selected = base.choose_permutation(source_order, candidates)
    if selected is None:
        raise ValueError("could not match braid components to source components by linking matrix")
    source_order_in_braid = [source_order[source_index] for source_index in selected]
    framings_in_braid_order = tuple(base.component_framings(payload)[source_index] for source_index in selected)
    return {
        "base": base,
        "evaluator": evaluator,
        "n_strands": n_strands,
        "braid_word": braid_word,
        "source_order_in_braid": source_order_in_braid,
        "framings_in_braid_order": framings_in_braid_order,
    }


def standard_unlink_value(evaluator):
    positive = evaluator.zero()
    negative = evaluator.zero()
    for label in evaluator.labels:
        dim_sq = evaluator.dimension(label) ** 2
        positive += dim_sq * evaluator.twist(label)
        negative += dim_sq * evaluator.twist(label) ** -1
    return positive * (negative ** 9)


def labels_for_index(labels, component_count, index):
    base = len(labels)
    digits = [0] * component_count
    value = int(index)
    for position in range(component_count - 1, -1, -1):
        digits[position] = value % base
        value //= base
    return tuple(labels[digit] for digit in digits)


def partial_path(start, end):
    return PARTIAL_DIR / f"chunk-{int(start):07d}-{int(end):07d}.json"


def write_json_atomic(path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def worker(start, count, *, write_partial=True):
    started = time.time()
    context = build_context()
    evaluator = context["evaluator"]
    component_count = len(context["source_order_in_braid"])
    sector_total = len(evaluator.labels) ** component_count
    end = min(int(start) + int(count), sector_total)
    dimensions = {label: evaluator.dimension(label) for label in evaluator.labels}
    partial = evaluator.zero()
    processed = 0
    for sector_index in range(int(start), end):
        fixed_labels = labels_for_index(evaluator.labels, component_count, sector_index)
        coefficient = evaluator.one()
        for label in fixed_labels:
            coefficient *= dimensions[label]
        amplitude = evaluator.fixed_label_value(
            context["n_strands"],
            context["braid_word"],
            fixed_labels,
            context["framings_in_braid_order"],
        )
        partial += coefficient * amplitude
        processed += 1
    payload = {
        "schema": "twisted-yetter.akbulut-figure1-e1-su2-3-untwisted-chunk.v1",
        "kind": "partial",
        "level": LEVEL,
        "precision_bits": PRECISION,
        "start": int(start),
        "end": end,
        "processed": processed,
        "sector_total": sector_total,
        "partial_real": str(CF(partial).real()),
        "partial_imag": str(CF(partial).imag()),
        "elapsed_seconds": time.time() - started,
        "ru_maxrss_mb": ru_maxrss_mb(),
        "fixed_label_cache_size": len(evaluator._fixed_label_cache),
        "numpy_crossing_cache_size": len(evaluator._numpy_crossing_cache),
    }
    if write_partial:
        write_json_atomic(partial_path(start, end), payload)
        payload["artifact"] = str(partial_path(start, end).relative_to(REPO_ROOT))
    print(json.dumps(payload, sort_keys=True), flush=True)


def run_parent(chunk_size, range_start=None, range_end=None):
    started = time.time()
    context = build_context()
    evaluator = context["evaluator"]
    component_count = len(context["source_order_in_braid"])
    sector_total = len(evaluator.labels) ** component_count
    start_bound = 0 if range_start is None else int(range_start)
    end_bound = sector_total if range_end is None else min(int(range_end), sector_total)
    if start_bound < 0 or start_bound > end_bound:
        raise ValueError("bad sector range")
    standard_value = standard_unlink_value(evaluator)
    akbulut_value = CF(0)
    partials = []
    print(
        json.dumps(
            {
                "phase": "starting-chunked",
                "level": LEVEL,
                "n_strands": context["n_strands"],
                "braid_word_length": len(context["braid_word"]),
                "component_count": component_count,
                "component_order_in_braid": context["source_order_in_braid"],
                "framings_in_braid_order": list(context["framings_in_braid_order"]),
                "sector_total": sector_total,
                "range_start": start_bound,
                "range_end": end_bound,
                "chunk_size": int(chunk_size),
            },
            sort_keys=True,
        ),
        flush=True,
    )
    for start in range(start_bound, end_bound, int(chunk_size)):
        end = min(start + int(chunk_size), end_bound)
        path = partial_path(start, end)
        child_started = time.time()
        if path.exists():
            partial = json.loads(path.read_text())
            child_wall_seconds = 0
            source = "existing-partial"
        else:
            command = [
                sys.executable,
                str(Path(__file__).resolve()),
                "--worker",
                "--start",
                str(start),
                "--count",
                str(chunk_size),
            ]
            completed = subprocess.run(command, check=True, capture_output=True, text=True)
            lines = [line for line in completed.stdout.splitlines() if line.strip()]
            partial = json.loads(lines[-1])
            child_wall_seconds = time.time() - child_started
            source = "computed"
        partial_value = CF(partial["partial_real"]) + CF(partial["partial_imag"]) * CF.gen()
        akbulut_value += partial_value
        partials.append(partial)
        print(
            json.dumps(
                {
                    "phase": "chunk-complete",
                    "start": partial["start"],
                    "end": partial["end"],
                    "processed_total": partial["end"],
                    "percent": float(100 * partial["end"] / sector_total),
                    "source": source,
                    "child_elapsed_seconds": partial["elapsed_seconds"],
                    "wall_seconds_for_child": child_wall_seconds,
                    "child_ru_maxrss_mb": partial["ru_maxrss_mb"],
                    "elapsed_seconds": time.time() - started,
                    "artifact": str(path.relative_to(REPO_ROOT)),
                },
                sort_keys=True,
            ),
            flush=True,
        )
    aggregation_scope = "full" if (start_bound == 0 and end_bound == sector_total) else "partial-range"
    difference = CF(akbulut_value - standard_value)
    if aggregation_scope == "full":
        status = "pass" if abs(difference) < TOLERANCE else "mismatch"
        output_path = OUTPUT
    else:
        status = "partial-range"
        output_path = (
            OUTPUT.parent
            / f"figure1-e1-su2-3-untwisted-partial-range-{start_bound:07d}-{end_bound:07d}-v2.json"
        )
    result = {
        "schema": "twisted-yetter.akbulut-figure1-e1-su2-3-untwisted-chunked-comparison.v1",
        "status": status,
        "category_id": "SU(2)_3",
        "source_input": str(context["base"].INPUT.relative_to(REPO_ROOT)),
        "claim_level": "chunked ordinary untwisted Kirby-color comparison against standard CP2#9CPbar",
        "algorithm": "spawn short-lived workers over contiguous fixed-label sector ranges",
        "aggregation_scope": aggregation_scope,
        "comparison_against_standard_is_meaningful": aggregation_scope == "full",
        "complexity": {
            "n_strands": context["n_strands"],
            "braid_word_length": len(context["braid_word"]),
            "component_count": component_count,
            "component_order_in_braid": context["source_order_in_braid"],
            "framings_in_braid_order": list(context["framings_in_braid_order"]),
            "sector_total": sector_total,
            "range_start": start_bound,
            "range_end": end_bound,
            "chunk_size": int(chunk_size),
            "partial_dir": str(PARTIAL_DIR.relative_to(REPO_ROOT)),
        },
        "partials": partials,
        "akbulut_value": complex_json(akbulut_value),
        "standard_value": complex_json(standard_value),
        "difference": complex_json(difference),
        "abs_difference": str(abs(difference)),
        "tolerance": str(TOLERANCE),
        "elapsed_seconds": time.time() - started,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": result["status"],
                "artifact": str(output_path.relative_to(REPO_ROOT)),
                "akbulut_value": result["akbulut_value"]["display"],
                "standard_value": result["standard_value"]["display"],
                "abs_difference": result["abs_difference"],
                "elapsed_seconds": result["elapsed_seconds"],
            },
            indent=2,
            sort_keys=True,
        ),
        flush=True,
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, default=DEFAULT_CHUNK_SIZE)
    parser.add_argument("--chunk-size", type=int, default=DEFAULT_CHUNK_SIZE)
    parser.add_argument("--range-start", type=int)
    parser.add_argument("--range-end", type=int)
    parser.add_argument("--no-write-partial", action="store_true")
    args = parser.parse_args()
    if args.worker:
        worker(args.start, args.count, write_partial=not args.no_write_partial)
    else:
        run_parent(args.chunk_size, range_start=args.range_start, range_end=args.range_end)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
