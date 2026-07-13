"""Pure-Python helpers for restartable native-Morse singleton workloads."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import tempfile


def canonical_json_bytes(payload) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()


def payload_sha256(payload) -> str:
    return hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def atomic_write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


class FsyncJSONLWriter:
    """Append one durable canonical-JSON record per line."""

    def __init__(self, path: Path):
        self.path = path
        self.handle = None

    def __enter__(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.handle = self.path.open("a", encoding="utf-8")
        return self

    def append(self, payload) -> None:
        self.handle.write(canonical_json_bytes(payload).decode() + "\n")
        self.handle.flush()
        os.fsync(self.handle.fileno())

    def __exit__(self, exc_type, exc_value, traceback):
        if self.handle is not None:
            self.handle.close()


def recover_jsonl_checkpoint(path: Path, identity_sha256: str):
    """Load a ledger and truncate only a torn final line.

    Any malformed interior row, conflicting duplicate, or identity mismatch is
    treated as corruption instead of being silently skipped.
    """

    if not path.exists():
        return {}
    records = {}
    with path.open("r+b") as handle:
        while True:
            line_start = handle.tell()
            raw = handle.readline()
            if not raw:
                break
            is_final = handle.peek(1) == b""
            if not raw.endswith(b"\n"):
                if is_final:
                    handle.truncate(line_start)
                    break
                raise ValueError(f"unterminated interior JSONL row in {path}")
            try:
                payload = json.loads(raw)
            except json.JSONDecodeError as error:
                if is_final:
                    handle.truncate(line_start)
                    break
                raise ValueError(f"bad interior JSONL row in {path}") from error
            if payload.get("status") != "pass":
                raise ValueError(f"non-pass checkpoint row in {path}")
            if payload.get("evaluation_identity_sha256") != identity_sha256:
                raise ValueError(f"checkpoint identity mismatch in {path}")
            index = int(payload["sector_index"])
            if index in records and canonical_json_bytes(records[index]) != canonical_json_bytes(payload):
                raise ValueError(f"conflicting duplicate sector {index} in {path}")
            records[index] = payload
    return records


def iter_singleton_payloads(roots):
    """Yield ``(source_locator, payload)`` from file and JSONL checkpoints."""

    for root in roots:
        for path in sorted(root.rglob("sector-*.json")):
            yield str(path), json.loads(path.read_text())
        for path in sorted(root.rglob("singleton-ledger*.jsonl")):
            lines = path.read_text().splitlines()
            for line_number, line in enumerate(lines, start=1):
                if not line.strip():
                    continue
                try:
                    payload = json.loads(line)
                except json.JSONDecodeError as error:
                    if line_number == len(lines):
                        continue
                    raise ValueError(f"bad JSONL row at {path}:{line_number}") from error
                yield f"{path}#{line_number}", payload


def balanced_lpt_shards(rows, shard_count: int, weight_key: str):
    """Balance indivisible rows by longest-processing-time-first scheduling."""

    if shard_count < 1:
        raise ValueError("shard_count must be positive")
    shards = [{"estimated_work": 0.0, "rows": []} for _ in range(shard_count)]
    ordered = sorted(
        rows,
        key=lambda row: (float(row[weight_key]), int(row["sector_index"])),
        reverse=True,
    )
    for row in ordered:
        shard = min(
            shards,
            key=lambda item: (item["estimated_work"], len(item["rows"])),
        )
        shard["rows"].append(row)
        shard["estimated_work"] += float(row[weight_key])
    for shard in shards:
        shard["rows"].sort(
            key=lambda row: (float(row[weight_key]), int(row["sector_index"]))
        )
    return shards


def read_jsonl(path: Path):
    rows = []
    for line_number, line in enumerate(path.read_text().splitlines(), start=1):
        if not line.strip():
            continue
        payload = json.loads(line)
        if not isinstance(payload, dict) or "sector_index" not in payload:
            raise ValueError(f"bad JSONL row at {path}:{line_number}")
        rows.append(payload)
    return rows
