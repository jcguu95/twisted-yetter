"""Build a runtime certificate from a deterministic Morse singleton sample."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import json
import math
from pathlib import Path

from experiments.scripts.morse_singleton_workload import (
    atomic_write_json,
    canonical_json_bytes,
    file_sha256,
    iter_singleton_payloads,
)


def anchors(base, component_count):
    result = {0, base**component_count - 1}
    repeated_place_value = sum(base**position for position in range(component_count))
    for digit in range(base):
        result.add(digit * repeated_place_value)
        for position in range(component_count):
            result.add(digit * base**position)
    return result


def percentile(sorted_values, probability):
    if not sorted_values:
        return None
    index = round(probability * (len(sorted_values) - 1))
    return sorted_values[index]


def summary(values):
    ordered = sorted(float(value) for value in values)
    return {
        "count": len(ordered),
        "sum_seconds": sum(ordered),
        "mean_seconds": sum(ordered) / len(ordered) if ordered else None,
        "min_seconds": ordered[0] if ordered else None,
        "median_seconds": percentile(ordered, 0.5),
        "p90_seconds": percentile(ordered, 0.9),
        "p99_seconds": percentile(ordered, 0.99),
        "max_seconds": ordered[-1] if ordered else None,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ranking-summary", type=Path, required=True)
    parser.add_argument("--population-ranking-summary", type=Path)
    parser.add_argument("--base", type=int, required=True)
    parser.add_argument("--component-count", type=int, required=True)
    parser.add_argument("--workers", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("roots", nargs="+", type=Path)
    args = parser.parse_args()

    ranking = json.loads(args.ranking_summary.read_text())
    population = int(ranking["sector_total"])
    expected_sample_count = int(ranking["ranked_sector_count"])
    expected_indices = set()
    for path in args.roots:
        for ledger in path.rglob("singleton-ledger-*.jsonl"):
            for line in ledger.read_text().splitlines():
                if line.strip():
                    expected_indices.add(int(json.loads(line)["sector_index"]))

    records = {}
    duplicates = []
    digest = hashlib.sha256()
    for locator, payload in iter_singleton_payloads(args.roots):
        if payload.get("status") != "pass":
            continue
        index = int(payload["sector_index"])
        digest.update(canonical_json_bytes(payload) + b"\n")
        if index in records:
            duplicates.append({"sector_index": index, "locator": locator})
        else:
            records[index] = payload

    worker_contexts = []
    pool_summaries = []
    for root in args.roots:
        for path in sorted(root.rglob("worker-context-*.json")):
            context = json.loads(path.read_text())
            worker_contexts.append(
                {
                    "path": str(path),
                    "sha256": file_sha256(path),
                    "run_id": context.get("run_id"),
                    "worker_id": context.get("worker_id"),
                    "utc_start": context.get("utc_start"),
                    "evaluation_identity": context.get("evaluation_identity"),
                    "evaluation_identity_sha256": context.get(
                        "evaluation_identity_sha256"
                    ),
                    "sector_index_file_sha256": context.get(
                        "sector_index_file_sha256"
                    ),
                    "repo": context.get("repo"),
                    "tool_versions": context.get("tool_versions"),
                    "environment": context.get("environment"),
                    "checkpoint_format": context.get("checkpoint_format"),
                    "progress_every": context.get("progress_every"),
                }
            )
        for path in sorted(root.rglob("pool-summary.json")):
            pool = json.loads(path.read_text())
            pool_summaries.append(
                {
                    "path": str(path),
                    "sha256": file_sha256(path),
                    "status": pool.get("status"),
                    "run_id": pool.get("run_id"),
                    "workers": pool.get("workers"),
                    "selected_shard_count": pool.get("selected_shard_count"),
                    "utc_start": pool.get("utc_start"),
                    "utc_finish": pool.get("utc_finish"),
                    "elapsed_seconds": pool.get("elapsed_seconds"),
                    "repo": pool.get("repo"),
                    "environment": pool.get("environment"),
                }
            )

    anchor_set = anchors(args.base, args.component_count)
    sampled_anchor_indices = sorted(set(records) & anchor_set)
    random_indices = sorted(set(records) - anchor_set)
    random_times = [records[index]["elapsed_seconds"] for index in random_indices]
    anchor_times = [records[index]["elapsed_seconds"] for index in sampled_anchor_indices]
    random_stats = summary(random_times)
    all_stats = summary(payload["elapsed_seconds"] for payload in records.values())
    remaining_population = population - len(anchor_set)
    estimated_cpu_seconds = (
        float(random_stats["mean_seconds"]) * remaining_population
        + sum(float(value) for value in anchor_times)
    )
    stratified = None
    if args.population_ranking_summary:
        population_ranking = json.loads(args.population_ranking_summary.read_text())
        population_counts = {
            int(row["dimension"]): int(row["count"])
            for row in population_ranking["max_boundary_dimension_counts"]
        }
        sample_by_dimension = {}
        for record in records.values():
            dimension = int(
                record["ranking_metadata"]["max_boundary_fusion_dimension"]
            )
            sample_by_dimension.setdefault(dimension, []).append(
                float(record["elapsed_seconds"])
            )
        if set(population_counts) != set(sample_by_dimension):
            raise ValueError("calibration sample does not cover every population stratum")
        strata = []
        stratified_cpu_seconds = 0.0
        for dimension in sorted(population_counts):
            timing = summary(sample_by_dimension[dimension])
            contribution = timing["mean_seconds"] * population_counts[dimension]
            stratified_cpu_seconds += contribution
            strata.append(
                {
                    "max_boundary_fusion_dimension": dimension,
                    "population_count": population_counts[dimension],
                    "sample_timing": timing,
                    "estimated_cpu_seconds": contribution,
                }
            )
        stratified = {
            "population_ranking_summary": str(args.population_ranking_summary),
            "population_ranking_summary_sha256": file_sha256(
                args.population_ranking_summary
            ),
            "strata": strata,
            "estimated_cpu_seconds": stratified_cpu_seconds,
            "estimated_cpu_hours": stratified_cpu_seconds / 3600,
            "ideal_wall_hours": stratified_cpu_seconds / args.workers / 3600,
            "operational_wall_hours_range": [
                stratified_cpu_seconds / args.workers / 3600 * 1.05,
                stratified_cpu_seconds / args.workers / 3600 * 1.25,
            ],
        }
    status = (
        "pass"
        if len(records) == expected_sample_count and not duplicates
        else "incomplete-or-needs-review"
    )
    payload = {
        "schema": "twisted-yetter.native-morse-runtime-calibration.v1",
        "status": status,
        "mathematical_status": "RUNTIME_ESTIMATE_NOT_AN_RT_EVALUATION",
        "generator_script": "experiments/scripts/morse_runtime_calibration.py",
        "ranking_summary": str(args.ranking_summary),
        "ranking_summary_sha256": file_sha256(args.ranking_summary),
        "roots": [str(path) for path in args.roots],
        "population_sector_count": population,
        "expected_sample_sector_count": expected_sample_count,
        "observed_unique_sector_count": len(records),
        "observed_index_count": len(expected_indices),
        "duplicate_count": len(duplicates),
        "duplicates": duplicates,
        "source_record_digest_sha256": digest.hexdigest(),
        "worker_contexts": worker_contexts,
        "pool_summaries": pool_summaries,
        "sampling": {
            "base": args.base,
            "component_count": args.component_count,
            "anchor_population_count": len(anchor_set),
            "sampled_anchor_count": len(sampled_anchor_indices),
            "random_sample_count": len(random_indices),
            "anchor_indices": sampled_anchor_indices,
            "note": "anchors are removed from the random mean and added back at measured cost",
        },
        "all_sample_timing": all_stats,
        "random_sample_timing": random_stats,
        "sampled_anchor_timing": summary(anchor_times),
        "extrapolation": {
            "estimated_cpu_seconds": estimated_cpu_seconds,
            "estimated_cpu_hours": estimated_cpu_seconds / 3600,
            "worker_count": args.workers,
            "ideal_wall_seconds": estimated_cpu_seconds / args.workers,
            "ideal_wall_hours": estimated_cpu_seconds / args.workers / 3600,
            "operational_wall_multiplier_range": [1.05, 1.25],
            "operational_wall_hours_range": [
                estimated_cpu_seconds / args.workers / 3600 * 1.05,
                estimated_cpu_seconds / args.workers / 3600 * 1.25,
            ],
            "caveat": "random-sample extrapolation; full ranking and dynamic shards reduce imbalance but do not change total CPU",
        },
        "stratified_extrapolation": stratified,
        "generated_at_utc": datetime.now(UTC).isoformat(),
    }
    atomic_write_json(args.output, payload)
    print(args.output.resolve())
    if status != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
