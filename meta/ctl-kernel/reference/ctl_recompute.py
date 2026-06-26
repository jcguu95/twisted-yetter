#!/usr/bin/env python3
"""Small independent-style CID recomputation helper for CTL vectors."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Any


DOMAIN = b"ctl-object-v1\0"


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def cid(value: Any) -> str:
    return "ctlobj-sha256:" + hashlib.sha256(DOMAIN + canonical_bytes(value)).hexdigest()


def check_vectors(root: Path) -> None:
    with (root / "encoding.jsonl").open(encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            row = json.loads(line)
            assert canonical_bytes(row["value"]).hex() == row["canonical_hex"], row["name"]
            assert cid(row["value"]) == row["cid"], row["name"]

    for case_file in sorted(root.glob("*/case.json")):
        manifest = json.loads(case_file.read_text(encoding="utf-8"))
        for expected_cid, obj in manifest["object_values"].items():
            assert cid(obj) == expected_cid, f"{case_file}: {expected_cid}"
    print("recompute: valid")


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: ctl_recompute.py VECTORS_DIR")
    check_vectors(Path(sys.argv[1]))


if __name__ == "__main__":
    main()

