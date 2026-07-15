#!/usr/bin/env python3
"""Validate and materialize the low-rank MTC classification scope matrix."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCES = REPO_ROOT / "experiments/inputs/references/low-rank-mtc-classification-primary-sources-v1.json"
DEFAULT_FAMILIES = REPO_ROOT / "experiments/inputs/mtc-classification/low-rank-mtc-families-v1.json"
DEFAULT_OUTPUT = REPO_ROOT / "experiments/results/mtc-classification/low-rank-mtc-classification-matrix-v1.json"


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def build_matrix(sources_path: Path, families_path: Path) -> dict[str, Any]:
    sources = _load(sources_path)
    family_input = _load(families_path)
    references = {entry["reference_id"]: entry for entry in sources["references"]}
    coverage = family_input["coverage_by_rank"]
    families = family_input["families"]

    assert {entry["rank"] for entry in coverage} == set(range(2, 6))
    family_ids = [entry["family_id"] for entry in families]
    assert len(family_ids) == len(set(family_ids))

    rows = []
    for entry in families:
        assert entry["reference_id"] in references
        assert 2 <= entry["rank"] <= 5
        assert entry["invertible_group_order"] >= 1
        assert entry["fusion_multiplicity_max"] >= 1
        row = dict(entry)
        row["universal_grading_group"] = entry["invertible_group"]
        row["universal_grading_group_order"] = entry["invertible_group_order"]
        row["character_twist_eligible"] = entry["invertible_group_order"] > 1
        row["character_count"] = entry["invertible_group_order"]
        row["universal_group_reason"] = (
            "For modular categories U(C) is isomorphic to the group of invertible simple objects; "
            "see ref:bgnprw-weakly-integral-rank7-2021, Section 2.2, page 4."
        )
        rows.append(row)

    eligible = [row for row in rows if row["character_twist_eligible"]]
    gaps = [
        "The rank-2-through-5 premodular braided-equivalence classification is complete, but braided classes can admit multiple spherical or ribbon refinements.",
        "This matrix does not claim a ribbon-equivalence exhaustion until every braided row has a spherical-structure audit.",
        "The 2016 rank-5 modular theorem is a Grothendieck-level classification; the 2024 source supplies the stronger braided-equivalence refinement used here.",
    ]
    now = datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    dirty = bool(_git("status", "--porcelain"))
    return {
        "schema": "twisted-yetter.low-rank-mtc-classification-matrix.v1",
        "status": "RANK2_TO_5_BRAIDED_CLASSIFICATION_MATRIX_WITH_RIBBON_REFINEMENT_GAP",
        "generated_at_utc": now,
        "mathematical_status": "LITERATURE_BACKED_SCOPE_MAP_NOT_A_NEW_CLASSIFICATION_THEOREM",
        "top_notice": "Complete through rank 5 only up to braided equivalence; do not interpret the rows as an exhaustive ribbon-equivalence list until spherical refinements are audited.",
        "coverage_by_rank": coverage,
        "open_gaps": gaps,
        "families": rows,
        "twist_candidate_family_ids": [row["family_id"] for row in eligible],
        "counts": {
            "family_rows": len(rows),
            "twist_candidate_rows": len(eligible),
            "references": len(references),
        },
        "inputs": [
            {"path": str(sources_path.relative_to(REPO_ROOT)), "sha256": _sha256(sources_path)},
            {"path": str(families_path.relative_to(REPO_ROOT)), "sha256": _sha256(families_path)},
        ],
        "generator_script": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
        "reproduce_command": "python3 experiments/scripts/build_low_rank_mtc_classification_matrix.py --write",
        "environment": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "git_commit": _git("rev-parse", "HEAD"),
            "git_dirty": dirty,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sources", type=Path, default=DEFAULT_SOURCES)
    parser.add_argument("--families", type=Path, default=DEFAULT_FAMILIES)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    matrix = build_matrix(args.sources.resolve(), args.families.resolve())
    rendered = json.dumps(matrix, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
