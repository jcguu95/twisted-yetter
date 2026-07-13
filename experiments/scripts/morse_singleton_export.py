"""Validate chunk singleton rows and export canonical index-ordered JSONL."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-count", type=int, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("chunks", nargs="+", type=Path)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows = {}
    identity = None
    chunk_records = []
    for path in args.chunks:
        payload = json.loads(path.read_text())
        current_identity = (
            payload["input"],
            payload["category"],
            tuple(payload["component_order"]),
            tuple(sorted(payload["character_assignments"].items())),
        )
        if identity is None:
            identity = current_identity
        if current_identity != identity:
            raise ValueError(f"chunk identity mismatch: {path}")
        sector_values = payload.get("sector_values")
        if sector_values is None:
            raise ValueError(f"chunk has no singleton rows: {path}")
        for row in sector_values:
            index = int(row["sector_index"])
            if index in rows:
                raise ValueError(f"duplicate sector index {index}")
            rows[index] = row
        chunk_records.append(
            {
                "path": str(path),
                "sector_range": payload["sector_range"],
                "row_count": len(sector_values),
            }
        )
    expected_indices = set(range(args.expected_count))
    observed_indices = set(rows)
    if observed_indices != expected_indices:
        missing = sorted(expected_indices - observed_indices)[:20]
        extra = sorted(observed_indices - expected_indices)[:20]
        raise ValueError(f"singleton coverage mismatch; missing={missing}, extra={extra}")
    jsonl = args.output_dir / "singletons.jsonl"
    digest = hashlib.sha256()
    with jsonl.open("w") as handle:
        for index in range(args.expected_count):
            line = json.dumps(rows[index], sort_keys=True, separators=(",", ":")) + "\n"
            handle.write(line)
            digest.update(line.encode())
    manifest = {
        "schema": "twisted-yetter.native-morse-singleton-export.v1",
        "status": "pass",
        "input": identity[0],
        "category": identity[1],
        "component_order": list(identity[2]),
        "character_assignments": dict(identity[3]),
        "sector_count": args.expected_count,
        "unique_sector_count": len(rows),
        "coverage": "exact-0-through-59048" if args.expected_count == 59049 else "exact",
        "jsonl": str(jsonl),
        "jsonl_sha256": digest.hexdigest(),
        "chunk_count": len(chunk_records),
        "chunks": sorted(
            chunk_records, key=lambda row: row["sector_range"]["start"]
        ),
        "generated_at_utc": datetime.now(UTC).isoformat(),
    }
    manifest_path = args.output_dir / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(manifest_path.resolve())


if __name__ == "__main__":
    main()
