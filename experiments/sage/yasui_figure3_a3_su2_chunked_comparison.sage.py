"""Chunked Yasui Figure 3 (a=3) SU(2)_k comparison."""

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
A3_PATH = REPO_ROOT / "experiments" / "sage" / "yasui_figure3_a3_su2_2_untwisted_comparison.sage.py"
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


def output_path(level, all_alpha):
    mode = "all-alpha" if all_alpha else "untwisted"
    return RESULT_DIR / f"figure3-a3-su2-{level}-{mode}-chunked-comparison-v1.json"


def partial_dir(level, all_alpha):
    mode = "all-alpha" if all_alpha else "untwisted"
    return RESULT_DIR / f"figure3-a3-su2-{level}-{mode}-chunks-v1"


def chunk_path(level, all_alpha, start, end):
    return partial_dir(level, all_alpha) / f"chunk-{start:07d}-{end:07d}.json"


def alpha_rows(all_alpha):
    return list(product((0, 1), repeat=3)) if all_alpha else [(0, 0, 0)]


def labels_for_alpha(alpha, component_order_in_braid):
    alpha_h, alpha_e1, alpha_e2 = alpha
    by_component = {"A": alpha_e2, "B": alpha_h, "C": alpha_e1}
    return tuple(by_component[name] for name in component_order_in_braid)


def build_braid_payload():
    a3 = load_module(A3_PATH, "yasui_a3_base_for_chunked")
    payload = json.loads(a3.INPUT.read_text())
    component_words, crossing_signs, crossing_records = a3.source_oriented_gauss_code(payload)
    link = a3.Link([component_words, crossing_signs])
    braid = link.braid()
    n_strands = int(braid.parent().strands())
    braid_word = [int(generator) for generator in braid.Tietze()]
    braid_linking = [
        [int(entry) for entry in row]
        for row in a3.braid_closure_linking_matrix(n_strands, tuple(braid_word))
    ]
    candidates = a3.component_permutation(a3.source_matrix(payload), braid_linking)
    selected = min(candidates) if candidates else None
    if selected is None:
        raise ValueError("a=3 component order did not match target linking matrix")
    components = a3.source_order(payload)
    component_order_in_braid = [components[source_index] for source_index in selected]
    framings = a3.source_framings(payload)
    framings_in_braid_order = [framings[source_index] for source_index in selected]
    return {
        "source_input": str(a3.INPUT.relative_to(REPO_ROOT)),
        "n_strands": n_strands,
        "braid_word": braid_word,
        "braid_word_length": len(braid_word),
        "component_order_in_source": a3.source_order(payload),
        "component_order_in_braid": component_order_in_braid,
        "source_index_per_braid_component": selected,
        "framings_in_braid_order": framings_in_braid_order,
        "target_intersection_matrix": a3.source_matrix(payload),
        "source_ordered_braid_linking_matrix": a3.source_ordered_matrix(braid_linking, selected),
        "crossing_signs": crossing_signs,
        "crossing_records": crossing_records,
    }


def chunk_worker(level, start, count, all_alpha):
    su2k = load_module(SU2K_PATH, f"su2k_yasui_a3_chunk_worker_{level}_{start}_{count}")
    braid = build_braid_payload()
    evaluator = su2k.SU2KBraidEvaluator(level, exact=False, precision=PRECISION)
    rows = alpha_rows(all_alpha)
    partials = {alpha: evaluator.zero() for alpha in rows}
    selected = islice(product(evaluator.labels, repeat=3), start, start + count)
    started = time.time()
    processed = 0
    for fixed_labels in selected:
        amplitude = evaluator.fixed_label_value(
            int(braid["n_strands"]),
            tuple(int(generator) for generator in braid["braid_word"]),
            tuple(int(label) for label in fixed_labels),
            tuple(int(framing) for framing in braid["framings_in_braid_order"]),
        )
        for alpha in rows:
            coefficient = evaluator.one()
            for omega_label, simple_label in zip(labels_for_alpha(alpha, braid["component_order_in_braid"]), fixed_labels, strict=True):
                coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
            partials[alpha] += coefficient * amplitude
        processed += 1
    payload = {
        "schema": "twisted-yetter.yasui-figure3-a3-su2-chunk.v1",
        "kind": "partial",
        "level": level,
        "alpha_mode": "all-alpha" if all_alpha else "untwisted",
        "start": start,
        "end": start + processed,
        "requested_count": count,
        "processed": processed,
        "sector_total": (level + 1) ** 3,
        "partials_by_alpha": {
            ",".join(str(item) for item in alpha): complex_pair(value)
            for alpha, value in partials.items()
        },
        "elapsed_seconds": time.time() - started,
    }
    path = chunk_path(level, all_alpha, start, start + processed)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    payload["artifact"] = str(path.relative_to(REPO_ROOT))
    print(json.dumps(payload, sort_keys=True), flush=True)
    return 0


def run_chunk(level, start, count, all_alpha):
    path = chunk_path(level, all_alpha, start, start + count)
    if path.exists():
        payload = json.loads(path.read_text())
        print(json.dumps({"phase": "chunk-reused", "start": start, "end": payload["end"], "percent": 100 * payload["end"] / payload["sector_total"], "artifact": str(path.relative_to(REPO_ROOT))}, sort_keys=True), flush=True)
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
    if all_alpha:
        cmd.append("--all-alpha")
    env = dict(os.environ)
    env.setdefault("DOT_SAGE", str(REPO_ROOT / ".sage"))
    started = time.time()
    completed = subprocess.run(cmd, cwd=REPO_ROOT, env=env, check=True, text=True, capture_output=True)
    lines = [line for line in completed.stdout.splitlines() if line.strip()]
    payload = json.loads(lines[-1])
    print(json.dumps({"phase": "chunk-complete", "start": payload["start"], "end": payload["end"], "processed": payload["processed"], "percent": 100 * payload["end"] / payload["sector_total"], "artifact": payload["artifact"], "child_elapsed_seconds": payload["elapsed_seconds"], "wall_seconds_for_child": time.time() - started}, sort_keys=True), flush=True)
    return payload


def standard_value(evaluator, alpha):
    total = evaluator.zero()
    for fixed_labels in product(evaluator.labels, repeat=3):
        coefficient = evaluator.one()
        for omega_label, simple_label in zip(alpha, fixed_labels, strict=True):
            coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
        total += coefficient * evaluator.fixed_label_value(3, (), fixed_labels, (1, -1, -1))
    return total


def compare(level, all_alpha=False, chunk_size=16):
    su2k = load_module(SU2K_PATH, f"su2k_yasui_a3_chunked_{level}")
    braid = build_braid_payload()
    evaluator = su2k.SU2KBraidEvaluator(level, exact=False, precision=PRECISION)
    started = time.time()
    rows = alpha_rows(all_alpha)
    totals = {alpha: CF(0) for alpha in rows}
    sector_total = (level + 1) ** 3
    for start in range(0, sector_total, chunk_size):
        payload = run_chunk(level, start, min(chunk_size, sector_total - start), all_alpha)
        for alpha_key, value_pair in payload["partials_by_alpha"].items():
            alpha = tuple(int(item) for item in alpha_key.split(","))
            totals[alpha] += complex_from_pair(value_pair)

    result_rows = []
    all_close = True
    max_abs_difference = CF(0)
    for alpha in rows:
        yasui_value = totals[alpha]
        standard = standard_value(evaluator, alpha)
        difference = CF(yasui_value - standard)
        abs_difference = abs(difference)
        close = bool(abs_difference < TOLERANCE)
        all_close = all_close and close
        max_abs_difference = max(max_abs_difference, abs_difference)
        result_rows.append(
            {
                "alpha_basis_order": ["h", "e1", "e2"],
                "alpha": [int(item) for item in alpha],
                "standard_omega_labels": [int(item) for item in alpha],
                "yasui_omega_label_order": braid["component_order_in_braid"],
                "yasui_omega_labels": [int(item) for item in labels_for_alpha(alpha, braid["component_order_in_braid"])],
                "yasui_value": complex_json(yasui_value),
                "standard_value": complex_json(standard),
                "difference": complex_json(difference),
                "abs_difference": str(abs_difference),
                "close_under_tolerance": close,
            }
        )
    result = {
        "schema": "twisted-yetter.yasui-figure3-a3-su2-chunked-comparison.v1",
        "status": "pass" if all_close else "mismatch",
        "sage_version": SAGE_VERSION,
        "category_id": f"SU(2)_{level}",
        "alpha_mode": "all-alpha" if all_alpha else "untwisted",
        "source": braid,
        "complexity": {
            "sector_total": sector_total,
            "chunk_size": chunk_size,
            "chunk_dir": str(partial_dir(level, all_alpha).relative_to(REPO_ROOT)),
        },
        "tolerance": str(TOLERANCE),
        "max_abs_difference": str(max_abs_difference),
        "rows": result_rows,
        "elapsed_seconds": time.time() - started,
    }
    out = output_path(level, all_alpha)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"], "artifact": str(out.relative_to(REPO_ROOT)), "category_id": result["category_id"], "alpha_mode": result["alpha_mode"], "max_abs_difference": result["max_abs_difference"], "elapsed_seconds": result["elapsed_seconds"], "sector_total": sector_total, "chunk_size": chunk_size}, indent=2, sort_keys=True))
    return 0 if result["status"] == "pass" else 1


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--level", type=int, required=True)
    parser.add_argument("--all-alpha", action="store_true")
    parser.add_argument("--chunk-size", type=int, default=16)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, default=16)
    args = parser.parse_args(argv)
    if args.worker:
        return chunk_worker(args.level, args.start, args.count, args.all_alpha)
    return compare(args.level, all_alpha=args.all_alpha, chunk_size=args.chunk_size)


if __name__ == "__main__":
    raise SystemExit(main())
