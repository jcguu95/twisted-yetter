#!/usr/bin/env python3
"""Fresh fixed-sector verification of the Figure 21 framing recovery."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import gzip
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import runpy
import socket
import subprocess
import sys
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))
RUNNER = REPO_ROOT / "experiments/sage/figure21_su2_2_full_evaluation.sage.py"
DEFAULT_LEDGER = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-right-su2-2-untwisted-framed-sector-ledger-v1.jsonl.gz"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-right-su2-2-framing-recovery-fresh-sector-verification-v1.json"
)
TOLERANCE = 1e-10


def utc_now() -> str:
    return datetime.now(UTC).isoformat()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def complex_json(value: complex) -> list[float]:
    return [float(value.real), float(value.imag)]


def git_metadata() -> dict[str, Any]:
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True
    ).strip()
    status = subprocess.check_output(
        ["git", "status", "--short"], cwd=REPO_ROOT, text=True
    ).splitlines()
    if status:
        raise ValueError("fresh-sector verification requires a clean worktree")
    return {"commit": commit, "dirty": False, "status_short": []}


def reservoir_sample(ledger: Path, count: int, seed: int) -> tuple[dict, list[dict]]:
    rng = random.Random(seed)
    sample = []
    eligible = 0
    with gzip.open(ledger, "rt") as handle:
        header = json.loads(next(handle))
        for line in handle:
            record = json.loads(line)
            if "weighted_contribution" not in record:
                continue
            eligible += 1
            if len(sample) < count:
                sample.append(record)
                continue
            replacement = rng.randrange(eligible)
            if replacement < count:
                sample[replacement] = record
    if len(sample) != count:
        raise ValueError(f"requested {count} samples from only {eligible} sectors")
    sample.sort(key=lambda record: record["sector_id"])
    return header, sample


def verify(args: argparse.Namespace) -> dict[str, Any]:
    started_at = utc_now()
    started = time.perf_counter()
    git = git_metadata()
    namespace = runpy.run_path(RUNNER)
    context = namespace["load_context"]()
    header, sample = reservoir_sample(args.ledger, args.sample_count, args.seed)
    ordinary = tuple(context["ordinary"])
    max_raw_residual = 0.0
    max_weighted_residual = 0.0
    cases = []
    for record in sample:
        labels_tuple = tuple(record["labels"])
        labels = dict(zip(ordinary, labels_tuple, strict=True))
        value, stats = context["evaluator"].fixed_label_value(
            context["graph"], labels
        )
        kirby_weight = math.prod(
            float(context["category"].dimension(label))
            for label in labels_tuple
        )
        weighted = kirby_weight * value
        expected_raw = complex(*record["raw_graph_scalar"])
        expected_weighted = complex(*record["weighted_contribution"])
        raw_residual = abs(value - expected_raw)
        weighted_residual = abs(weighted - expected_weighted)
        max_raw_residual = max(max_raw_residual, raw_residual)
        max_weighted_residual = max(max_weighted_residual, weighted_residual)
        if raw_residual > TOLERANCE or weighted_residual > TOLERANCE:
            raise ValueError(
                f"sector {record['sector_id']} recovery mismatch: "
                f"raw={raw_residual}, weighted={weighted_residual}"
            )
        cases.append(
            {
                "sector_id": record["sector_id"],
                "labels": list(labels_tuple),
                "projector_rank": record["projector_rank"],
                "fresh_raw_graph_scalar": complex_json(value),
                "ledger_raw_graph_scalar": record["raw_graph_scalar"],
                "raw_residual": raw_residual,
                "weighted_residual": weighted_residual,
                "framing_corrections": stats["framing_corrections"],
            }
        )
    payload = {
        "schema": (
            "twisted-yetter.figure21-su2-2-framing-recovery-"
            "fresh-sector-verification.v1"
        ),
        "status": "PASS",
        "mathematical_status": "NUMERICAL_IMPLEMENTATION_CONTROL",
        "purpose": (
            "Independently re-contract a deterministic random sample with the "
            "framing-aware evaluator and compare it sector by sector with the "
            "recovered ledger."
        ),
        "ledger": str(args.ledger.resolve().relative_to(REPO_ROOT)),
        "ledger_sha256": sha256_file(args.ledger),
        "ledger_evaluation_id": header["evaluation_id"],
        "sample_seed": args.seed,
        "sample_count": len(cases),
        "tolerance": TOLERANCE,
        "max_raw_residual": max_raw_residual,
        "max_weighted_residual": max_weighted_residual,
        "cases": cases,
        "generator_script": str(Path(__file__).relative_to(REPO_ROOT)),
        "generator_script_sha256": sha256_file(Path(__file__)),
        "git": git,
        "environment": {
            "python": platform.python_version(),
            "host": socket.gethostname(),
        },
        "utc_start": started_at,
        "utc_finish": utc_now(),
        "elapsed_seconds": time.perf_counter() - started,
        "reproduce_command": (
            "DOT_SAGE=\"$PWD/.sage\" sage --python "
            f"{Path(__file__).relative_to(REPO_ROOT)} "
            f"--ledger {args.ledger.resolve().relative_to(REPO_ROOT)} "
            f"--output {args.output.resolve().relative_to(REPO_ROOT)} "
            f"--sample-count {args.sample_count} --seed {args.seed}"
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    temporary.replace(args.output)
    return payload


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    result.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    result.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    result.add_argument("--sample-count", type=int, default=100)
    result.add_argument("--seed", type=int, default=20260714)
    return result


if __name__ == "__main__":
    print(json.dumps(verify(parser().parse_args()), indent=2, sort_keys=True))
