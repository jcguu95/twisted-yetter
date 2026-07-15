#!/usr/bin/env python3
"""Compile a Morse DSL input into a certified canonical 3D PL lift."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

from experiments.scripts.morse_pl_lift import (
    apply_special_disk_side_assignment,
    build_morse_pl_lift,
    build_projection_bundle,
    optimize_special_disk_sides,
    render_projection_svg,
)
from experiments.scripts.special_dotted_morphism import compile_projected_morphism


REPO = Path(__file__).resolve().parents[2]


def _utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace(
        "+00:00", "Z"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--svg-prefix", type=Path)
    parser.add_argument("--near-xz-tilt", type=float, default=0.0137)
    parser.add_argument("--optimize-special-disk-sides", action="store_true")
    args = parser.parse_args()
    source = json.loads(args.input.read_text())
    lift = build_morse_pl_lift(
        source["forms"],
        component_by_piece=source["component_by_piece"],
        special_components=source.get("special_components", ()),
    )
    optimization = None
    if args.optimize_special_disk_sides:
        special_components = source.get("special_components", ())
        if len(special_components) != 1:
            raise ValueError("side optimization currently requires exactly one special component")
        optimization = optimize_special_disk_sides(lift, special_components[0])
        lift = apply_special_disk_side_assignment(lift, optimization)
    bundle = build_projection_bundle(lift, tilt=args.near_xz_tilt)
    forced_cut_comparison = None
    if optimization is not None:
        projected = compile_projected_morphism(
            source["forms"],
            component_by_piece=source["component_by_piece"],
            special_components=source["special_components"],
            component_order=source.get("component_order"),
        )
        certificate = projected["special_disk_certificates"][0]
        actual_punctures = bundle["special_disk_intersections"][special_components[0]][
            "punctures"
        ]
        forced_counts = Counter(
            cut["component"] for cut in certificate["forced_cuts"]
        )
        actual_counts = Counter(
            puncture["component"] for puncture in actual_punctures
        )
        matches = (
            optimization["minimum_puncture_count"]
            == certificate["forced_cut_count"]
            == len(actual_punctures)
            and forced_counts == actual_counts
        )
        forced_cut_comparison = {
            "status": (
                "PASS_OPTIMUM_EQUALS_FORCED_DISK_LOWER_BOUND"
                if matches
                else "FAIL_OPTIMUM_OR_COMPONENT_DISTRIBUTION_MISMATCH"
            ),
            "forced_lower_bound": certificate["forced_cut_count"],
            "optimized_minimum": optimization["minimum_puncture_count"],
            "realized_punctures": len(actual_punctures),
            "forced_count_by_component": dict(sorted(forced_counts.items())),
            "realized_count_by_component": dict(sorted(actual_counts.items())),
            "signed_comparison_status": (
                "NOT_COMPARED_PL_EDGE_DIRECTION_IS_EVENT_TIME_NOT_COMPONENT_ORIENTATION"
            ),
        }
    payload = {
        "schema": "twisted-yetter.morse-pl-lift-run.v1",
        "status": bundle["status"],
        "mathematical_status": source.get("status"),
        "source_ref": source.get("source_ref"),
        "source_locator": source.get("source_locator"),
        "input_path": str(args.input),
        "lift": lift,
        "projection_bundle": bundle,
        "side_optimization": optimization,
        "forced_cut_comparison": forced_cut_comparison,
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
    if args.svg_prefix:
        args.svg_prefix.parent.mkdir(parents=True, exist_ok=True)
        for projection in ("xy", "xz", "near-xz"):
            path = args.svg_prefix.with_name(
                f"{args.svg_prefix.name}-{projection}.svg"
            )
            path.write_text(
                render_projection_svg(
                    lift, projection, tilt=args.near_xz_tilt
                )
            )
    print(json.dumps({
        "status": payload["status"],
        "output": str(args.output),
        "projection_statuses": {
            name: report["status"]
            for name, report in bundle["projections"].items()
        },
        "puncture_counts": {
            name: report["puncture_count"]
            for name, report in bundle["special_disk_intersections"].items()
        },
        "forced_cut_comparison": forced_cut_comparison,
    }, indent=2, sort_keys=True))
    return 0 if payload["status"] == "PASS_PL_LIFT_PROJECTION_CONTROLS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
