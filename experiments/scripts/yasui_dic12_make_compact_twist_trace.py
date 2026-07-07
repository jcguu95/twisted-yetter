#!/usr/bin/env python3
"""Create a compact text trace for the Yasui a=1 D(Dic12) witness twist."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
import zlib
from datetime import datetime, timezone
from pathlib import Path


DEFAULT_INPUT = (
    "experiments/results/yasui/"
    "figure3-a1-r1-normalized-dic12-witness-g-component-a-twist-aggregate-v1.json"
)

DEFAULT_TRACE_OUTPUT = (
    "experiments/results/yasui/"
    "figure3-a1-r1-normalized-dic12-witness-g-component-a-twist-compact-trace-v1.jsonl"
)

DEFAULT_MANIFEST_OUTPUT = (
    "experiments/results/yasui/"
    "figure3-a1-r1-normalized-dic12-witness-g-component-a-twist-compact-trace-manifest-v1.json"
)

MONODROMY_SYMBOLS = {
    (1.0, 0.0): "1",
    (-1.0, 0.0): "-1",
    (0.0, 1.0): "i",
    (0.0, -1.0): "-i",
}

SYMBOL_TO_COMPLEX = {
    "1": 1 + 0j,
    "-1": -1 + 0j,
    "i": 1j,
    "-i": -1j,
}


def load_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def run_text(argv: list[str]) -> str | None:
    try:
        return subprocess.check_output(argv, text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return None


def repo_state(repo_root: Path) -> dict:
    status = run_text(["git", "-C", str(repo_root), "status", "--short"])
    status_bytes = (status or "").encode()
    return {
        "root": str(repo_root),
        "git_commit": run_text(["git", "-C", str(repo_root), "rev-parse", "HEAD"]),
        "dirty": bool(status),
        "status_short_line_count": len((status or "").splitlines()),
        "status_short_sha256": hashlib.sha256(status_bytes).hexdigest(),
    }


def pair_from_record(record: dict) -> tuple[str, str]:
    return (record["real"], record["imag"])


def rounded_key(record: dict) -> tuple[float, float]:
    real = round(float(record["real"]))
    imag = round(float(record["imag"]))
    return (float(real), float(imag))


def monodromy_symbol(record: dict) -> str:
    key = rounded_key(record)
    if key not in MONODROMY_SYMBOLS:
        raise ValueError(f"unexpected monodromy record: {record}")
    return MONODROMY_SYMBOLS[key]


def symbol_power(symbol: str, power: int) -> complex:
    return SYMBOL_TO_COMPLEX[symbol] ** power


def symbol_from_complex(z: complex) -> str:
    key = (float(round(z.real)), float(round(z.imag)))
    if key not in MONODROMY_SYMBOLS:
        raise ValueError(f"unexpected phase: {z}")
    return MONODROMY_SYMBOLS[key]


def file_size(path: Path) -> int:
    return path.stat().st_size


def compression_estimates(path: Path) -> dict:
    payload = path.read_bytes()
    git_blob = f"blob {len(payload)}\0".encode() + payload
    return {
        "gzip_bytes": len(gzip.compress(payload)),
        "plain_zlib_bytes": len(zlib.compress(payload)),
        "git_loose_object_zlib_bytes_estimate": len(zlib.compress(git_blob)),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default=DEFAULT_INPUT)
    parser.add_argument("--trace-output", default=DEFAULT_TRACE_OUTPUT)
    parser.add_argument("--manifest-output", default=DEFAULT_MANIFEST_OUTPUT)
    args = parser.parse_args()

    start = time.perf_counter()
    utc_start = datetime.now(timezone.utc).isoformat()
    repo_root = Path.cwd()
    input_path = Path(args.input)
    trace_output = Path(args.trace_output)
    manifest_output = Path(args.manifest_output)
    payload = load_json(input_path)
    rows = payload["rows"]
    labels = sorted({label for row in rows for label in row["fixed_component_labels"]})
    label_index = {label: i for i, label in enumerate(labels)}
    component_powers = payload["case"]["twist_powers_in_braid_order"]

    metadata = {
        "kind": "metadata",
        "schema": "twisted-yetter.yasui-dic12-witness-character-compact-trace.v1",
        "source_artifact": str(input_path),
        "source_artifact_sha256": sha256_file(input_path),
        "case": payload["case"],
        "sector_total": payload["sector_total"],
        "row_count": len(rows),
        "label_dictionary": labels,
        "row_encoding": {
            "i": "sector_index",
            "l": "fixed_component_label indices into label_dictionary, in braid component order",
            "u": "untwisted weighted contribution [real, imag] as decimal strings",
            "m": "witness monodromy symbols per component, each in {1,-1,i,-i}",
            "p": "net phase from product_j m_j ^ twist_power_j",
            "t": "twisted weighted contribution [real, imag] as decimal strings",
        },
        "complex_field": "complex128 decimal string trace; numeric certificate, not exact arithmetic",
        "aggregate_twisted": payload["aggregate_twisted"],
        "aggregate_untwisted_reconstructed": payload["aggregate_untwisted_reconstructed"],
        "normalized_twisted_by_global_dimension_sum_d_squared": payload[
            "normalized_twisted_by_global_dimension_sum_d_squared"
        ],
        "ratio_twisted_to_untwisted": payload["ratio_twisted_to_untwisted"],
        "standard_split_reference": payload["standard_split_reference"],
        "claim_boundary": (
            "Compact mathematical trace for inspecting how the completed 32768 "
            "D(Dic_12) Yasui a=1 sector amplitudes are transformed by the witness "
            "character twist. Worker/server provenance is intentionally omitted."
        ),
    }

    trace_output.parent.mkdir(parents=True, exist_ok=True)
    with trace_output.open("w", encoding="utf-8") as f:
        f.write(json.dumps(metadata, sort_keys=True, separators=(",", ":")) + "\n")
        for row in sorted(rows, key=lambda r: r["sector_index"]):
            monodromies = [
                monodromy_symbol(record)
                for record in row["witness_monodromy_by_component"]
            ]
            phase = 1 + 0j
            for symbol, power in zip(monodromies, component_powers):
                phase *= symbol_power(symbol, power)
            compact_row = {
                "i": row["sector_index"],
                "l": [label_index[label] for label in row["fixed_component_labels"]],
                "u": pair_from_record(row["weighted_untwisted_contribution"]),
                "m": monodromies,
                "p": symbol_from_complex(phase),
                "t": pair_from_record(row["weighted_twisted_contribution"]),
            }
            f.write(json.dumps(compact_row, sort_keys=True, separators=(",", ":")) + "\n")

    elapsed = time.perf_counter() - start
    manifest = {
        "schema": "twisted-yetter.yasui-dic12-witness-character-compact-trace-manifest.v1",
        "status": "pass",
        "generator_script": "experiments/scripts/yasui_dic12_make_compact_twist_trace.py",
        "argv": sys.argv[1:],
        "reproduce_command": "python3 experiments/scripts/yasui_dic12_make_compact_twist_trace.py",
        "utc_start": utc_start,
        "utc_finish": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": elapsed,
        "repo": repo_state(repo_root),
        "environment": {
            "python_executable": sys.executable,
            "python_version": sys.version,
            "platform": platform.platform(),
            "machine": platform.machine(),
            "hostname": platform.node(),
            "cpu_count": os.cpu_count(),
        },
        "input": {
            "path": str(input_path),
            "sha256": metadata["source_artifact_sha256"],
            "size_bytes": file_size(input_path),
        },
        "output": {
            "path": str(trace_output),
            "sha256": sha256_file(trace_output),
            "size_bytes": file_size(trace_output),
            "compression_estimates": compression_estimates(trace_output),
            "line_count": len(rows) + 1,
            "format": "jsonl text; first line metadata, following lines compact sector rows",
        },
        "mathematical_summary": {
            "row_count": len(rows),
            "simple_label_count": len(labels),
            "component_order_in_braid": payload["case"]["component_order_in_braid"],
            "standard_order_interpretation": payload["case"][
                "standard_order_interpretation"
            ],
            "twist_powers_in_braid_order": component_powers,
            "aggregate_twisted": payload["aggregate_twisted"],
            "normalized_twisted_by_global_dimension_sum_d_squared": payload[
                "normalized_twisted_by_global_dimension_sum_d_squared"
            ],
            "ratio_twisted_to_untwisted": payload["ratio_twisted_to_untwisted"],
            "verdict": payload["verdict"],
        },
        "exclusion_policy": (
            "This compact trace omits SSH, Hetzner setup, worker timing, duplicated "
            "environment records, and other operational provenance. Those remain in "
            "raw experiment artifacts when needed for audit."
        ),
    }
    manifest_output.parent.mkdir(parents=True, exist_ok=True)
    with manifest_output.open("w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
        f.write("\n")

    print(
        json.dumps(
            {
                "status": "pass",
                "trace": str(trace_output),
                "trace_size_bytes": manifest["output"]["size_bytes"],
                "trace_sha256": manifest["output"]["sha256"],
                "manifest": str(manifest_output),
                "rows": len(rows),
                "normalized_twisted": payload[
                    "normalized_twisted_by_global_dimension_sum_d_squared"
                ]["display"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
