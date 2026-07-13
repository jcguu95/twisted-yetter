#!/usr/bin/env python3
"""Compile and certify category-independent special-dotted morphism input."""

from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time

import numpy as np
import sympy as sp

from experiments.scripts.special_dotted_morphism import (
    compile_projected_morphism,
    linearize_horizontal_disk_projector,
    preflight_horizontal_disk_corridor,
    stable_json_hash,
)


REPO = Path(__file__).resolve().parents[2]


def _utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace(
        "+00:00", "Z"
    )


def _git(*args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=REPO, text=True, stderr=subprocess.DEVNULL
    ).strip()


def _atomic_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(handle, "w") as stream:
            json.dump(payload, stream, indent=2, sort_keys=True)
            stream.write("\n")
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def _signature(matrix: list[list[int]]) -> dict:
    eigenvalues = np.linalg.eigvalsh(np.asarray(matrix, dtype=float))
    positive = int(np.sum(eigenvalues > 1e-8))
    negative = int(np.sum(eigenvalues < -1e-8))
    zero = len(eigenvalues) - positive - negative
    return {
        "positive": positive,
        "negative": negative,
        "zero": zero,
        "signature": positive - negative,
        "eigenvalues": [float(value) for value in eigenvalues],
    }


def _link_matrix_certificate(ir: dict, framing_labels: dict[str, int]) -> dict:
    component_order = ir["component_order"]
    missing = set(component_order) - set(framing_labels)
    extra = set(framing_labels) - set(component_order)
    if missing or extra:
        raise ValueError(
            f"framing label mismatch: missing={sorted(missing)!r}, extra={sorted(extra)!r}"
        )
    index = {component: position for position, component in enumerate(component_order)}
    signed = defaultdict(int)
    visible_self = defaultdict(int)
    for crossing in ir["crossings"]:
        left = crossing["over_component"]
        right = crossing["under_component"]
        if left == right:
            visible_self[left] += crossing["sign"]
        else:
            signed[tuple(sorted((left, right)))] += crossing["sign"]
    odd = {pair: value for pair, value in signed.items() if value % 2}
    if odd:
        raise ValueError(f"odd signed crossing sums: {odd!r}")
    matrix = [[0] * len(component_order) for _ in component_order]
    for component, framing in framing_labels.items():
        matrix[index[component]][index[component]] = int(framing)
    for (left, right), value in signed.items():
        matrix[index[left]][index[right]] = value // 2
        matrix[index[right]][index[left]] = value // 2
    exact = sp.Matrix(matrix)
    return {
        "component_order": component_order,
        "framing_labels_are_total_framings": True,
        "visible_self_writhe": dict(visible_self),
        "linking_matrix": matrix,
        "determinant": int(exact.det()),
        "rank": int(exact.rank()),
        "signature": _signature(matrix),
    }


def _metadata(args, started: str, started_monotonic: float) -> dict:
    dirty = bool(_git("status", "--porcelain"))
    return {
        "generator_script": str(Path(__file__).resolve().relative_to(REPO)),
        "argv": sys.argv,
        "reproduce_command": "PYTHONPATH=. uv run python " + " ".join(sys.argv),
        "utc_start": started,
        "utc_finish": _utc_now(),
        "elapsed_seconds": time.monotonic() - started_monotonic,
        "repo_root": str(REPO),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": dirty,
        "tool_versions": {
            "python": platform.python_version(),
            "numpy": np.__version__,
            "sympy": sp.__version__,
        },
        "limits": {
            "max_seconds": args.max_seconds,
            "validate_only": args.validate_only,
            "identity_projector": args.identity_projector,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--failure-output", type=Path)
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--identity-projector", action="store_true")
    parser.add_argument("--max-seconds", type=float, default=10.0)
    args = parser.parse_args()
    started = _utc_now()
    started_monotonic = time.monotonic()
    stage = "load-input"
    try:
        payload = json.loads(args.input.read_text())
        stage = "compile-topology"
        ir = compile_projected_morphism(
            payload["forms"],
            component_by_piece=payload["component_by_piece"],
            special_components=payload["special_components"],
        )
        if time.monotonic() - started_monotonic > args.max_seconds:
            raise TimeoutError("topology compilation exceeded --max-seconds")
        link_certificate = _link_matrix_certificate(ir, payload["framing_labels"])
        stage = "corridor-preflight"
        preflight = preflight_horizontal_disk_corridor(payload["forms"], ir)
        result = {
            "schema": "twisted-yetter.special-dotted-morphism-compilation.v1",
            "status": "MORPHISM_TOPOLOGY_CONTROLS_PASS_NOT_LINEARIZED",
            "mathematical_status": "DRAFT_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM",
            "source_ref": payload.get("source_ref"),
            "source_locator": payload.get("source_locator"),
            "input_path": str(args.input),
            "input_file_hash": stable_json_hash(payload),
            "link_certificate": link_certificate,
            "projected_morphism_ir": ir,
            "corridor_preflight": preflight,
        }
        if not args.validate_only:
            stage = "linearize-horizontal-projector"
            linearized = linearize_horizontal_disk_projector(
                payload["forms"], ir, identity_projector=args.identity_projector
            )
            if linearized["status"] != "PASS_HORIZONTAL_DISK_PROJECTOR_LINEARIZATION":
                raise RuntimeError(
                    f"projector corridor is not safely linearizable: {linearized['status']}"
                )
            result["status"] = "MORPHISM_HORIZONTAL_LINEARIZATION_CONTROLS_PASS"
            result["linearized"] = linearized
        result.update(_metadata(args, started, started_monotonic))
        if args.output:
            _atomic_json(args.output, result)
        else:
            json.dump(result, sys.stdout, indent=2, sort_keys=True)
            sys.stdout.write("\n")
        return 0
    except BaseException as exc:
        failure = {
            "schema": "twisted-yetter.special-dotted-morphism-failure.v1",
            "status": "FAIL_FAST_STOPPED",
            "stage": stage,
            "error_type": type(exc).__name__,
            "error": str(exc),
            "input_path": str(args.input),
            **_metadata(args, started, started_monotonic),
        }
        if "preflight" in locals():
            failure["corridor_preflight"] = preflight
        if args.failure_output:
            _atomic_json(args.failure_output, failure)
        else:
            json.dump(failure, sys.stderr, indent=2, sort_keys=True)
            sys.stderr.write("\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
