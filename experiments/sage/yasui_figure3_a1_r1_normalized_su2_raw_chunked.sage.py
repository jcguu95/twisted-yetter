"""Chunked raw R1-normalized Yasui Figure 3 (a=1) SU(2)_k comparison.

This is the memory-bounded version of
``yasui_figure3_a1_r1_normalized_su2_raw_comparison.sage.py``.  It computes the
same all-alpha rows, but evaluates fixed-label sectors in short child
processes so the SU(2)_k F/R-symbol caches do not grow without bound.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_r1_normalized_su2_raw_chunked.sage.py --level 10
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import subprocess
import sys
import time
from itertools import islice, product
from pathlib import Path

from sage.all import ComplexField
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
YASUI_PAYLOAD = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-braid-payload-v1.json"
)
SU2K_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "yasui"
PRECISION = 120
CF = ComplexField(PRECISION)
TOLERANCE = CF("1e-10")


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


def complex_pair(value):
    value = CF(value)
    return [str(value.real()), str(value.imag())]


def complex_from_pair(pair):
    return CF(pair[0]) + CF(pair[1]) * CF.gen()


def alphas_for(untwisted_only):
    return [(0, 0, 0)] if untwisted_only else list(product((0, 1), repeat=3))


def yasui_labels_for_alpha(yasui, alpha):
    alpha_h, alpha_e1, alpha_e2 = alpha
    by_source = {
        "A": alpha_e2,
        "B": alpha_h,
        "C": alpha_e1,
    }
    return tuple(by_source[name] for name in yasui["omega_label_order"])


def output_path(level, untwisted_only):
    mode = "untwisted" if untwisted_only else "all-alpha"
    return RESULT_DIR / f"figure3-a1-r1-normalized-su2-{level}-{mode}-raw-comparison-v3.json"


def partial_dir(level, untwisted_only):
    mode = "untwisted" if untwisted_only else "all-alpha"
    return RESULT_DIR / f"figure3-a1-r1-normalized-su2-{level}-{mode}-raw-chunks-v3"


def chunk_path(level, untwisted_only, start, end):
    return partial_dir(level, untwisted_only) / f"chunk-{start:07d}-{end:07d}.json"


def standard_value(evaluator, alpha):
    total = evaluator.zero()
    for fixed_labels in product(evaluator.labels, repeat=3):
        coefficient = evaluator.one()
        for omega_label, simple_label in zip(alpha, fixed_labels, strict=True):
            coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
        total += coefficient * evaluator.fixed_label_value(3, (), fixed_labels, (1, -1, -1))
    return total


def chunk_worker(level, start, count, untwisted_only, write_partial=True):
    su2k = load_module(SU2K_PATH, f"su2k_yasui_r1_chunk_worker_{level}_{start}_{count}")
    yasui = json.loads(YASUI_PAYLOAD.read_text())
    evaluator = su2k.SU2KBraidEvaluator(level, exact=False, precision=PRECISION)
    alpha_rows = alphas_for(untwisted_only)
    yasui_labels_by_alpha = {
        alpha: yasui_labels_for_alpha(yasui, alpha)
        for alpha in alpha_rows
    }
    partials = {alpha: evaluator.zero() for alpha in alpha_rows}
    labels_iter = product(evaluator.labels, repeat=3)
    selected = islice(labels_iter, start, start + count)
    started = time.time()
    processed = 0
    for fixed_labels in selected:
        amplitude = evaluator.fixed_label_value(
            int(yasui["n_strands"]),
            tuple(int(generator) for generator in yasui["braid_word"]),
            fixed_labels,
            tuple(int(framing) for framing in yasui["framings_in_braid_order"]),
        )
        for alpha in alpha_rows:
            coefficient = evaluator.one()
            for omega_label, simple_label in zip(yasui_labels_by_alpha[alpha], fixed_labels, strict=True):
                coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
            partials[alpha] += coefficient * amplitude
        processed += 1
    payload = {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-su2-raw-chunk.v3",
        "kind": "partial",
        "level": level,
        "alpha_mode": "untwisted" if untwisted_only else "all-alpha",
        "start": start,
        "end": start + processed,
        "requested_count": count,
        "processed": processed,
        "sector_total": (level + 1) ** 3,
        "precision_bits": PRECISION,
        "partials_by_alpha": {
            ",".join(str(item) for item in alpha): complex_pair(value)
            for alpha, value in partials.items()
        },
        "elapsed_seconds": time.time() - started,
    }
    if write_partial:
        path = chunk_path(level, untwisted_only, start, start + processed)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        payload["artifact"] = str(path.relative_to(REPO_ROOT))
    print(json.dumps(payload, sort_keys=True))
    return 0


def run_chunk_child(level, start, count, untwisted_only):
    expected_path = chunk_path(level, untwisted_only, start, start + count)
    if expected_path.exists():
        payload = json.loads(expected_path.read_text())
        print(
            json.dumps(
                {
                    "phase": "chunk-reused",
                    "level": level,
                    "start": payload["start"],
                    "end": payload["end"],
                    "processed": payload["processed"],
                    "percent": 100 * payload["end"] / payload["sector_total"],
                    "artifact": str(expected_path.relative_to(REPO_ROOT)),
                },
                sort_keys=True,
            ),
            flush=True,
        )
        return payload
    cmd = [
        "sage",
        str(Path(__file__).resolve()),
        "--worker",
        "--level",
        str(level),
        "--start",
        str(start),
        "--count",
        str(count),
    ]
    if untwisted_only:
        cmd.append("--untwisted-only")
    started = time.time()
    env = dict(os.environ)
    env.setdefault("DOT_SAGE", str(REPO_ROOT / ".sage"))
    completed = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        env=env,
        check=True,
        text=True,
        capture_output=True,
    )
    lines = [line for line in completed.stdout.splitlines() if line.strip()]
    if not lines:
        raise RuntimeError(f"chunk {start} produced no JSON output")
    payload = json.loads(lines[-1])
    print(
        json.dumps(
            {
                "phase": "chunk-complete",
                "level": level,
                "start": payload["start"],
                "end": payload["end"],
                "processed": payload["processed"],
                "percent": 100 * payload["end"] / payload["sector_total"],
                "artifact": payload.get("artifact"),
                "child_elapsed_seconds": payload["elapsed_seconds"],
                "wall_seconds_for_child": time.time() - started,
            },
            sort_keys=True,
        ),
        flush=True,
    )
    return payload


def compare_level(level, untwisted_only=False, chunk_size=64):
    su2k = load_module(SU2K_PATH, f"su2k_yasui_r1_chunked_su2_{level}")
    yasui = json.loads(YASUI_PAYLOAD.read_text())
    if yasui["status"] != "pass":
        raise ValueError("R1-normalized Yasui braid payload is not pass")
    evaluator = su2k.SU2KBraidEvaluator(level, exact=False, precision=PRECISION)
    started = time.time()
    alpha_rows = alphas_for(untwisted_only)
    sector_total = (level + 1) ** 3
    yasui_totals = {alpha: CF(0) for alpha in alpha_rows}
    for start in range(0, sector_total, chunk_size):
        payload = run_chunk_child(level, start, min(chunk_size, sector_total - start), untwisted_only)
        for alpha_key, value_pair in payload["partials_by_alpha"].items():
            alpha = tuple(int(item) for item in alpha_key.split(","))
            yasui_totals[alpha] += complex_from_pair(value_pair)

    rows = []
    all_close = True
    max_abs_difference = CF(0)
    for alpha in alpha_rows:
        standard = standard_value(evaluator, alpha)
        yasui_value = yasui_totals[alpha]
        difference = CF(yasui_value - standard)
        abs_difference = abs(difference)
        close = bool(abs_difference < TOLERANCE)
        all_close = all_close and close
        max_abs_difference = max(max_abs_difference, abs_difference)
        rows.append(
            {
                "alpha_basis_order": ["h", "e1", "e2"],
                "alpha": [int(item) for item in alpha],
                "standard_omega_labels": [int(item) for item in alpha],
                "yasui_omega_label_order": yasui["omega_label_order"],
                "yasui_omega_labels": [int(item) for item in yasui_labels_for_alpha(yasui, alpha)],
                "standard_value": complex_json(standard),
                "yasui_value": complex_json(yasui_value),
                "difference": complex_json(difference),
                "abs_difference": str(abs_difference),
                "close_under_tolerance": close,
            }
        )
    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-su2-raw-comparison.v3",
        "status": "pass" if all_close else "mismatch",
        "sage_version": SAGE_VERSION,
        "category_id": f"SU(2)_{level}",
        "alpha_mode": "untwisted" if untwisted_only else "all-alpha",
        "source": {
            "r1_normalized_payload": str(YASUI_PAYLOAD.relative_to(REPO_ROOT)),
            "standard_presentation": "split unlink with framings (+1,-1,-1)",
        },
        "complexity": {
            "yasui_n_strands": int(yasui["n_strands"]),
            "yasui_braid_word_length": len(yasui["braid_word"]),
            "yasui_framings_in_braid_order": yasui["framings_in_braid_order"],
            "yasui_omega_label_order": yasui["omega_label_order"],
            "yasui_fixed_sector_count": sector_total,
            "standard_fixed_sector_count": sector_total,
            "chunk_size": chunk_size,
            "chunk_count": (sector_total + chunk_size - 1) // chunk_size,
            "chunk_dir": str(partial_dir(level, untwisted_only).relative_to(REPO_ROOT)),
        },
        "tolerance": str(TOLERANCE),
        "max_abs_difference": str(max_abs_difference),
        "rows": rows,
        "elapsed_seconds": time.time() - started,
    }
    path = output_path(level, untwisted_only)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": result["status"],
                "artifact": str(path.relative_to(REPO_ROOT)),
                "category_id": result["category_id"],
                "alpha_mode": result["alpha_mode"],
                "max_abs_difference": result["max_abs_difference"],
                "elapsed_seconds": result["elapsed_seconds"],
                "yasui_fixed_sector_count": sector_total,
                "chunk_size": chunk_size,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if result["status"] == "pass" else 1


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--level", type=int, required=True)
    parser.add_argument("--untwisted-only", action="store_true")
    parser.add_argument("--chunk-size", type=int, default=64)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, default=64)
    args = parser.parse_args(argv)
    if args.worker:
        return chunk_worker(args.level, args.start, args.count, args.untwisted_only)
    return compare_level(args.level, untwisted_only=args.untwisted_only, chunk_size=args.chunk_size)


if __name__ == "__main__":
    raise SystemExit(main())
