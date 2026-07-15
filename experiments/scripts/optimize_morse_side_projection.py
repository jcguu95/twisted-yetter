#!/usr/bin/env python3
"""Optimize an exact event-slice projection of a special-dotted Morse link."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

from experiments.scripts.morse_pl_lift import (
    analyze_projector_gather_cost,
    analyze_exact_side_morse_regularity,
    analyze_projection,
    build_blockwise_flat_side_lift,
    build_morse_pl_lift,
    build_projection_bundle,
    make_exact_side_projection_lift,
    optimize_special_disk_sides,
    render_projection_svg,
)


REPO = Path(__file__).resolve().parents[2]


def _utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace(
        "+00:00", "Z"
    )


def _angles(start: int, stop: int, step: int) -> list[int]:
    return list(range(start, stop, step))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--svg-output", type=Path)
    parser.add_argument("--coarse-step", type=int, default=10)
    parser.add_argument("--fine-radius", type=int, default=10)
    parser.add_argument("--fine-step", type=int, default=1)
    parser.add_argument("--bump-fraction", type=float, default=0.06)
    parser.add_argument(
        "--crossing-height-mode",
        choices=("fixed-extremes", "minimal-local"),
        default="minimal-local",
    )
    parser.add_argument("--crossing-margin", type=float, default=1e-3)
    parser.add_argument(
        "--block-order-strategy",
        choices=(
            "stable",
            "stable-reverse",
            "projected-mean-ascending",
            "projected-mean-descending",
            "projected-median-ascending",
            "projected-median-descending",
        ),
        default="stable",
    )
    parser.add_argument("--block-order-angle", type=float, default=70.0)
    args = parser.parse_args()
    if args.coarse_step <= 0 or args.fine_step <= 0:
        raise ValueError("angle steps must be positive")
    source = json.loads(args.input.read_text())
    specials = source.get("special_components", ())
    if len(specials) != 1:
        raise ValueError("side projection optimizer requires exactly one special component")
    special = specials[0]
    lift = build_morse_pl_lift(
        source["forms"],
        component_by_piece=source["component_by_piece"],
        special_components=specials,
    )
    optimization = optimize_special_disk_sides(lift, special)
    flattened = build_blockwise_flat_side_lift(
        lift,
        optimization,
        bump_fraction=args.bump_fraction,
        crossing_height_mode=args.crossing_height_mode,
        crossing_margin=args.crossing_margin,
        block_order_strategy=args.block_order_strategy,
        block_order_angle_degrees=args.block_order_angle,
    )
    controls = build_projection_bundle(flattened)

    cache: dict[int, dict] = {}

    def evaluate(angle: int) -> dict:
        if angle in cache:
            return cache[angle]
        side = make_exact_side_projection_lift(flattened, special, angle)
        report = analyze_projection(side, "xz", max_examples=0)
        morse_regularity = analyze_exact_side_morse_regularity(side)
        gather = analyze_projector_gather_cost(side)
        regular_crossings = report["counts"].get("regular_double_point", 0)
        record = {
            "angle_degrees": angle,
            "status": report["status"],
            "regular_crossing_count": regular_crossings,
            "projector_gather_swap_count": gather[
                "minimum_adjacent_swap_count"
            ],
            "total_crossing_cost": regular_crossings
            + 2 * gather["minimum_adjacent_swap_count"],
            "projector_gather": gather,
            "unexplained_singularity_count": report[
                "unexplained_singularity_count"
            ],
            "singularity_counts": report["counts"],
            "side_lift_hash": side["lift_hash"],
            "morse_regularity_status": morse_regularity["status"],
            "horizontal_edge_count": morse_regularity["horizontal_edge_count"],
        }
        cache[angle] = record
        return record

    coarse = [evaluate(angle) for angle in _angles(0, 180, args.coarse_step)]
    generic_coarse = [
        row
        for row in coarse
        if row["unexplained_singularity_count"] == 0
        and row["horizontal_edge_count"] == 0
    ]
    if not generic_coarse:
        raise RuntimeError("coarse sweep found no generic side projection")
    coarse_best = min(
        generic_coarse,
        key=lambda row: (row["total_crossing_cost"], row["regular_crossing_count"]),
    )
    fine_start = max(0, coarse_best["angle_degrees"] - args.fine_radius)
    fine_stop = min(180, coarse_best["angle_degrees"] + args.fine_radius + 1)
    fine = [evaluate(angle) for angle in _angles(fine_start, fine_stop, args.fine_step)]
    all_generic = [
        row
        for row in cache.values()
        if row["unexplained_singularity_count"] == 0
        and row["horizontal_edge_count"] == 0
    ]
    best = min(
        all_generic,
        key=lambda row: (row["total_crossing_cost"], row["regular_crossing_count"]),
    )
    best_side = make_exact_side_projection_lift(
        flattened, special, best["angle_degrees"]
    )
    puncture_count = controls["special_disk_intersections"][special][
        "puncture_count"
    ]
    passed = (
        puncture_count == optimization["minimum_puncture_count"]
        and controls["projections"]["xy"]["status"]
        == "PASS_XY_COMBINATORIAL_ROUND_TRIP"
        and best["unexplained_singularity_count"] == 0
        and best["horizontal_edge_count"] == 0
    )
    payload = {
        "schema": "twisted-yetter.morse-exact-side-projection-optimization.v1",
        "status": (
            "PASS_EXACT_SIDE_PROJECTION_OPTIMIZATION_CONTROLS"
            if passed
            else "NEEDS_REVIEW"
        ),
        "mathematical_status": source.get("status"),
        "source_ref": source.get("source_ref"),
        "source_locator": source.get("source_locator"),
        "input_path": str(args.input),
        "special_component": special,
        "source_lift_hash": lift["lift_hash"],
        "flattened_lift_hash": flattened["lift_hash"],
        "side_optimization": {
            key: value
            for key, value in optimization.items()
            if key != "assignment"
        },
        "blockwise_flattening": flattened["blockwise_flattening"],
        "projection_controls": {
            "xy": controls["projections"]["xy"],
            "puncture_count": puncture_count,
        },
        "coarse_angles": coarse,
        "fine_angles": fine,
        "best": best,
        "limitations": {
            "reidemeister_simplification_applied": False,
            "vertical_block_order_optimized": args.block_order_strategy != "stable",
            "claim": "projection heuristic checkpoint, not a minimum crossing proof",
        },
        "generator_script": str(Path(__file__).resolve().relative_to(REPO)),
        "argv": sys.argv,
        "reproduce_command": "PYTHONPATH=. uv run python " + " ".join(sys.argv),
        "generated_at": _utc_now(),
        "git_commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
        ).strip(),
        "git_dirty": bool(
            subprocess.check_output(
                ["git", "status", "--porcelain"], cwd=REPO, text=True
            ).strip()
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    if args.svg_output:
        args.svg_output.parent.mkdir(parents=True, exist_ok=True)
        args.svg_output.write_text(render_projection_svg(best_side, "xz"))
    print(
        json.dumps(
            {
                "status": payload["status"],
                "minimum_punctures": optimization["minimum_puncture_count"],
                "best": best,
                "output": str(args.output),
                "svg_output": str(args.svg_output) if args.svg_output else None,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if passed else 2


if __name__ == "__main__":
    raise SystemExit(main())
