#!/usr/bin/env python3
"""Apply the Dic12 witness character twist to completed singleton chunks."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


DEFAULT_CHUNK_DIRS = [
    "experiments/results/yasui/figure3-a1-r1-normalized-dic12-omega0-untwisted-singleton-chunks-v1",
    "experiments/results/yasui/remote-pulls/hetzner-178-105-119-138-dic12-a1-v1",
    "experiments/results/yasui/remote-pulls/xil-m2-dic12-a1-v1",
]

DEFAULT_MANIFEST = (
    "experiments/results/yasui/"
    "figure3-a1-r1-normalized-dic12-omega0-untwisted-singleton-manifest-v1.json"
)

DEFAULT_OUTPUT = (
    "experiments/results/yasui/"
    "figure3-a1-r1-normalized-dic12-witness-g-component-a-twist-aggregate-v1.json"
)

DEFAULT_UNTWISTED_AGGREGATE = (
    "experiments/results/yasui/"
    "figure3-a1-r1-normalized-dic12-omega0-untwisted-distributed-aggregate-v1.json"
)

COMPONENT_ORDER = ["C", "A", "B"]
STANDARD_ORDER = ["h", "e1", "e2"]
WITNESS_THETA = -1


def complex_record(z: complex, field: str = "complex128-summed-in-python-float") -> dict:
    return {
        "abs": str(abs(z)),
        "display": f"{z.real}{z.imag:+}j",
        "field": field,
        "imag": str(z.imag),
        "real": str(z.real),
    }


def parse_complex_record(payload: dict) -> complex:
    return complex(float(payload["real"]), float(payload["imag"]))


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
    commit = run_text(["git", "-C", str(repo_root), "rev-parse", "HEAD"])
    status = run_text(["git", "-C", str(repo_root), "status", "--short"])
    return {
        "root": str(repo_root),
        "git_commit": commit,
        "dirty": bool(status),
        "status_short": status,
    }


def label_parts(label: str) -> tuple[str, str]:
    if ":" not in label:
        raise ValueError(f"bad simple label {label!r}")
    class_name, rep = label.split(":", 1)
    return class_name, rep


def witness_chi_on_class(class_name: str) -> complex:
    table = {
        "1A": 1,
        "aA": -1,
        "a2A": 1,
        "a3A": -1,
        "xA": 1j,
        "axA": -1j,
    }
    try:
        return complex(table[class_name])
    except KeyError as exc:
        raise ValueError(f"unknown Dic12 conjugacy class {class_name!r}") from exc


def trailing_int(rep: str, prefix: str) -> int:
    if not rep.startswith(prefix):
        raise ValueError(f"{rep!r} does not start with {prefix!r}")
    return int(rep[len(prefix) :])


def witness_z_scalar(rep: str) -> complex:
    if rep.startswith("lin"):
        return complex((-1) ** trailing_int(rep, "lin"))
    if rep.startswith("rho"):
        return complex((-1) ** trailing_int(rep, "rho"))
    if rep.startswith("chi"):
        return complex((-1) ** trailing_int(rep, "chi"))
    if rep.startswith("eta"):
        return complex((-1) ** trailing_int(rep, "eta"))
    raise ValueError(f"unknown Dic12 centralizer irrep label {rep!r}")


def witness_monodromy(label: str) -> complex:
    class_name, rep = label_parts(label)
    return witness_chi_on_class(class_name) * witness_z_scalar(rep)


def iter_chunk_files(chunk_roots: list[Path]):
    seen_paths = set()
    for root in chunk_roots:
        if root.is_file() and root.name.startswith("chunk-") and root.suffix == ".json":
            paths = [root]
        else:
            paths = sorted(root.rglob("chunk-*.json")) if root.exists() else []
        for path in paths:
            resolved = path.resolve()
            if resolved in seen_paths:
                continue
            seen_paths.add(resolved)
            yield path


def load_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def dump_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2, sort_keys=True)
        f.write("\n")


def parse_component_powers(items: list[str]) -> dict[str, int]:
    powers = {name: 0 for name in COMPONENT_ORDER}
    for item in items:
        if "=" not in item:
            raise ValueError(f"component power must look like A=1, got {item!r}")
        name, value = item.split("=", 1)
        if name not in powers:
            raise ValueError(f"unknown component {name!r}; expected one of {COMPONENT_ORDER}")
        powers[name] = int(value)
    return powers


def split_reference_ratio(component_powers: dict[str, int]) -> complex:
    # Component order C,A,B is interpreted as standard h,e1,e2.
    h_power = component_powers["C"]
    e1_power = component_powers["A"]
    e2_power = component_powers["B"]
    exponent = -h_power + e1_power + e2_power
    return complex(WITNESS_THETA**exponent)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", default=DEFAULT_MANIFEST)
    parser.add_argument("--untwisted-aggregate", default=DEFAULT_UNTWISTED_AGGREGATE)
    parser.add_argument("--chunk-dir", action="append", default=[])
    parser.add_argument("--component-power", action="append", default=["A=1"])
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--no-rows", action="store_true")
    args = parser.parse_args()

    start = time.perf_counter()
    utc_start = datetime.now(timezone.utc).isoformat()
    repo_root = Path.cwd()
    manifest_path = Path(args.manifest)
    untwisted_aggregate_path = Path(args.untwisted_aggregate)
    output_path = Path(args.output)
    chunk_dirs = [Path(p) for p in (args.chunk_dir or DEFAULT_CHUNK_DIRS)]
    component_powers = parse_component_powers(args.component_power)
    powers_in_order = [component_powers[name] for name in COMPONENT_ORDER]

    manifest = load_json(manifest_path)
    untwisted_aggregate = load_json(untwisted_aggregate_path)
    entries = manifest["entries"]
    sector_total = len(entries)
    seen: dict[int, Path] = {}
    duplicates = []
    bad_records = []
    rows = []
    aggregate_twisted = 0j
    aggregate_untwisted = 0j
    max_abs_twisted = {"sector_index": None, "abs": "0.0"}
    nonzero_count = 0
    source_counts: dict[str, int] = {}

    for chunk_path in iter_chunk_files(chunk_dirs):
        record = load_json(chunk_path)
        sector_index = record.get("sector_index")
        if not isinstance(sector_index, int):
            bad_records.append({"path": str(chunk_path), "reason": "missing integer sector_index"})
            continue
        if sector_index in seen:
            duplicates.append(
                {
                    "sector_index": sector_index,
                    "first_path": str(seen[sector_index]),
                    "duplicate_path": str(chunk_path),
                }
            )
            continue
        seen[sector_index] = chunk_path
        try:
            labels = record["fixed_component_labels"]
            untwisted = parse_complex_record(record["weighted_untwisted_contribution"])
            monodromies = [witness_monodromy(label) for label in labels]
            phase = 1 + 0j
            for monodromy, power in zip(monodromies, powers_in_order):
                phase *= monodromy**power
            twisted = untwisted * phase
        except Exception as exc:
            bad_records.append(
                {"path": str(chunk_path), "sector_index": sector_index, "reason": str(exc)}
            )
            continue

        aggregate_untwisted += untwisted
        aggregate_twisted += twisted
        abs_twisted = abs(twisted)
        if abs_twisted > float(max_abs_twisted["abs"]):
            max_abs_twisted = {"sector_index": sector_index, "abs": str(abs_twisted)}
        if abs_twisted > 1e-10:
            nonzero_count += 1
        source = record.get("run_context", {}).get("worker_id") or record.get("source", "unknown")
        source_counts[str(source)] = source_counts.get(str(source), 0) + 1
        if not args.no_rows:
            rows.append(
                {
                    "sector_index": sector_index,
                    "source_path": str(chunk_path),
                    "fixed_component_labels": labels,
                    "twist_powers_by_component": powers_in_order,
                    "witness_monodromy_by_component": [
                        complex_record(z) for z in monodromies
                    ],
                    "weighted_untwisted_contribution": complex_record(
                        untwisted, field="complex128"
                    ),
                    "weighted_twisted_contribution": complex_record(twisted),
                }
            )

    missing = sorted(set(range(sector_total)) - set(seen))
    global_dimension = float(
        untwisted_aggregate.get("global_dimension_sum_d_squared", 144.0)
    )
    expected_untwisted = parse_complex_record(
        untwisted_aggregate["standard_split_unlink_comparison"][
            "expected_standard_split_unlink_raw"
        ]
    )
    expected_ratio = split_reference_ratio(component_powers)
    expected_twisted = expected_untwisted * expected_ratio
    elapsed = time.perf_counter() - start
    status = "pass" if not missing and not duplicates and not bad_records else "fail"
    abs_diff_expected = abs(aggregate_twisted - expected_twisted)

    payload = {
        "schema": "twisted-yetter.yasui-dic12-witness-character-transform.v1",
        "status": status,
        "generator_script": "experiments/scripts/yasui_dic12_character_twist_transform.py",
        "argv": sys.argv[1:],
        "reproduce_command": (
            "python3 experiments/scripts/yasui_dic12_character_twist_transform.py "
            "--component-power A=1"
        ),
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
        "inputs": {
            "manifest": str(manifest_path),
            "manifest_sha256": sha256_file(manifest_path),
            "untwisted_aggregate": str(untwisted_aggregate_path),
            "untwisted_aggregate_sha256": sha256_file(untwisted_aggregate_path),
            "chunk_dirs": [str(path) for path in chunk_dirs],
        },
        "case": {
            "link_id": "yasui-figure3-a1-r1-normalized",
            "category_id": "omega0_untwisted_D_Dic12",
            "mtc_id": "omega0_untwisted_D_Dic12",
            "component_order_in_braid": COMPONENT_ORDER,
            "standard_order_interpretation": STANDARD_ORDER,
            "twist_power_by_component_name": component_powers,
            "twist_powers_in_braid_order": powers_in_order,
            "witness_invertible": {
                "label": "g=(a^3, chi)",
                "chi": "chi(x)=i, chi(a)=-1",
                "order": 4,
                "twist": WITNESS_THETA,
                "monodromy_formula": "M_g(C,rho)=chi(class representative)*rho(a^3)",
            },
        },
        "claim_boundary": (
            "Numeric coefficient transform of completed D(Dic_12) untwisted Yasui a=1 "
            "singleton amplitudes by the witness invertible monodromy character. "
            "This is not an exact theorem-level certificate."
        ),
        "sector_total": sector_total,
        "unique_sector_count": len(seen),
        "duplicate_count": len(duplicates),
        "duplicates": duplicates[:20],
        "missing_count": len(missing),
        "missing_sector_indices_first_100": missing[:100],
        "bad_record_count": len(bad_records),
        "bad_records": bad_records[:20],
        "source_counts": source_counts,
        "aggregate_untwisted_reconstructed": complex_record(aggregate_untwisted),
        "aggregate_twisted": complex_record(aggregate_twisted),
        "global_dimension_sum_d_squared": str(global_dimension),
        "normalized_twisted_by_global_dimension_sum_d_squared": complex_record(
            aggregate_twisted / global_dimension
        ),
        "ratio_twisted_to_untwisted": complex_record(
            aggregate_twisted / aggregate_untwisted
        ),
        "abs_difference_from_untwisted": str(abs(aggregate_twisted - aggregate_untwisted)),
        "nonzero_twisted_contribution_count_abs_gt_1e-10": nonzero_count,
        "max_abs_twisted_contribution": max_abs_twisted,
        "standard_split_reference": {
            "baseline_untwisted_raw": complex_record(expected_untwisted),
            "ratio_formula": "theta(g_h)^-1 theta(g_e1) theta(g_e2)",
            "ratio_for_this_component_power": complex_record(expected_ratio),
            "expected_twisted_raw": complex_record(expected_twisted),
            "abs_difference_from_expected_twisted_raw": str(abs_diff_expected),
        },
        "verdict": (
            "twisted_matches_expected_nonbaseline_split_signal"
            if status == "pass" and abs_diff_expected < 1e-8
            else "inconclusive_or_failed"
        ),
    }
    if not args.no_rows:
        payload["rows"] = sorted(rows, key=lambda row: row["sector_index"])
    dump_json(output_path, payload)
    print(
        json.dumps(
            {
                "status": payload["status"],
                "artifact": str(output_path),
                "twisted": payload["aggregate_twisted"]["display"],
                "normalized_twisted": payload[
                    "normalized_twisted_by_global_dimension_sum_d_squared"
                ]["display"],
                "ratio": payload["ratio_twisted_to_untwisted"]["display"],
                "expected": payload["standard_split_reference"][
                    "expected_twisted_raw"
                ]["display"],
                "abs_diff_expected": payload["standard_split_reference"][
                    "abs_difference_from_expected_twisted_raw"
                ],
                "missing": payload["missing_count"],
                "duplicates": payload["duplicate_count"],
                "bad": payload["bad_record_count"],
                "verdict": payload["verdict"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if payload["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
