"""Generate fixed-sector Figure 21 controls in Rep(Z2) and sVec."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import time

from experiments.sage.pointed_premodular_categories import (
    PIVOTAL_PROFILE_PATH,
    SymmetricZ2PremodularCategory,
)
from experiments.sage.ribbon_graph_evaluator import (
    PointedVacuumProjectorEvaluator,
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
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-right-pointed-premodular-projector-controls-v1.json"
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _complex(value: complex) -> dict[str, float]:
    value = complex(value)
    return {"real": value.real, "imag": value.imag}


def generate() -> dict:
    started = datetime.now(timezone.utc)
    clock = time.perf_counter()
    source = json.loads(INPUT_PATH.read_text())
    forms = source["forms"]
    component_by_piece = source["component_by_piece"]
    component_order = source["component_order"]
    framings = source["framing_labels"]
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=source["special_components"],
        component_order=component_order,
    )
    graph = build_vacuum_coupon_graph(forms, ir)
    ordinary = [component for component in component_order if component != "red"]
    sectors = {
        "all_unit": {component: 0 for component in ordinary},
        "purple_only": {
            component: int(component == "purple") for component in ordinary
        },
        "purple_and_black": {
            component: int(component in {"purple", "black"})
            for component in ordinary
        },
    }
    categories = {}
    for fermionic in (False, True):
        category = SymmetricZ2PremodularCategory(fermionic=fermionic)
        evaluator = PointedVacuumProjectorEvaluator(
            category,
            source_forms=forms,
            component_by_piece=component_by_piece,
            projected_ir=ir,
            total_framings=framings,
        )
        category_results = {}
        for name, labels in sectors.items():
            value, stats = evaluator.fixed_label_value(graph, labels)
            category_results[name] = {
                "labels": labels,
                "value": _complex(value),
                "projector_rank": stats["projector_rank"],
                "status": stats["status"],
                "framing_phase": (
                    None
                    if stats["framing_phase"] is None
                    else _complex(stats["framing_phase"])
                ),
            }
        categories[category.category_id] = category_results

    checks = {
        "all_unit_is_one": all(
            abs(results["all_unit"]["value"]["real"] - 1.0) < 1e-12
            and abs(results["all_unit"]["value"]["imag"]) < 1e-12
            for results in categories.values()
        ),
        "purple_only_has_no_vacuum": all(
            results["purple_only"]["projector_rank"] == 0
            for results in categories.values()
        ),
        "purple_and_black_has_vacuum": all(
            results["purple_and_black"]["projector_rank"] == 1
            for results in categories.values()
        ),
    }
    if not all(checks.values()):
        raise AssertionError(f"pointed premodular controls failed: {checks!r}")
    finished = datetime.now(timezone.utc)
    return {
        "schema": "twisted-yetter.figure21-pointed-premodular-projector-controls.v1",
        "status": "PASS_POINTED_PREMODULAR_FIXED_SECTOR_CONTROLS",
        "mathematical_status": "NUMERIC_CONTROL_NOT_FULL_INVARIANT",
        "purpose": (
            "Exercise the direct graph-level vacuum projector on a nonhorizontal "
            "29-puncture special disk in degenerate premodular categories."
        ),
        "generator_script": (
            "experiments/scripts/check_figure21_pointed_premodular.py"
        ),
        "argv": [],
        "reproduce_command": (
            "UV_CACHE_DIR=/tmp/uv-cache PYTHONPATH=. uv run python "
            "experiments/scripts/check_figure21_pointed_premodular.py"
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
            "sha256": _sha256(INPUT_PATH),
            "source_ref": source["source_ref"],
            "source_locator": source["source_locator"],
            "source_status": source["status"],
            "projected_ir_hash": stable_json_hash(ir),
            "coupon_graph_hash": graph["graph_hash"],
            "coupon_factor_count": graph["coupon_input_count"],
        },
        "category_data": {
            "pivotal_profile": str(PIVOTAL_PROFILE_PATH.relative_to(REPO_ROOT)),
            "pivotal_profile_sha256": _sha256(PIVOTAL_PROFILE_PATH),
            "categories": ["rep-z2", "svec"],
            "premodular_degeneracy": "symmetric braiding; not modular",
        },
        "checks": checks,
        "results": categories,
        "coverage": {
            "arbitrary_nonhorizontal_coupon": "SUPPORTED_FOR_POINTED_CATEGORIES",
            "general_pivotal_horizontal_coupon": "SUPPORTED",
            "general_nonpointed_nonhorizontal_coupon": "NOT_IMPLEMENTED",
        },
        "non_claims": [
            "This is not a complete Crane-Yetter evaluation.",
            "This does not verify the draft transcription against the printed figure.",
            "This does not support arbitrary nonpointed premodular categories."
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    result = generate()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
