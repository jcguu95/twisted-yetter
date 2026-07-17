#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any


TURN_ID = "019f6e86-6c24-70b0-9d00-6d2f301f7c27"
START_UTC = "2026-07-17T05:22:11.166Z"
END_UTC = "2026-07-17T05:25:35.510Z"


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def git_output(repo_root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo_root), *args], text=True
    ).strip()


def message_text(payload: dict[str, Any]) -> str:
    return "".join(
        item["text"]
        for item in payload.get("content", [])
        if item.get("type") in {"input_text", "output_text"}
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Preserve the exact visible turn that proposed the premodular "
            "Twisted Yetter formula ansatz."
        )
    )
    parser.add_argument("--source-jsonl", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--repo-root", type=Path, default=Path(__file__).resolve().parents[2]
    )
    args = parser.parse_args()

    raw_lines = args.source_jsonl.read_bytes().splitlines(keepends=True)
    selected: list[tuple[bytes, dict[str, Any]]] = []
    verified_model: str | None = None
    verified_effort: str | None = None

    for raw_line in raw_lines:
        record = json.loads(raw_line)
        if record.get("type") == "turn_context":
            payload = record.get("payload", {})
            if payload.get("turn_id") == TURN_ID:
                verified_model = payload.get("model")
                verified_effort = payload.get("effort")
            continue
        if record.get("type") != "response_item":
            continue
        payload = record.get("payload", {})
        if payload.get("type") != "message" or payload.get("role") not in {
            "user",
            "assistant",
        }:
            continue
        turn_id = payload.get("internal_chat_message_metadata_passthrough", {}).get(
            "turn_id"
        )
        if turn_id != TURN_ID:
            continue
        if not START_UTC <= record["timestamp"] <= END_UTC:
            continue
        selected.append((raw_line, record))

    messages = []
    for _, record in selected:
        payload = record["payload"]
        messages.append(
            {
                "timestamp_utc": record["timestamp"],
                "turn_id": TURN_ID,
                "role": payload["role"],
                "phase": payload.get("phase"),
                "text": message_text(payload),
            }
        )

    user_count = sum(message["role"] == "user" for message in messages)
    assistant_count = sum(message["role"] == "assistant" for message in messages)
    final_count = sum(message["phase"] == "final_answer" for message in messages)
    if (user_count, assistant_count, final_count) != (1, 4, 1):
        raise SystemExit(
            "unexpected transcript shape: "
            f"users={user_count}, assistants={assistant_count}, finals={final_count}"
        )
    if verified_model != "gpt-5.6-sol" or verified_effort != "medium":
        raise SystemExit(
            "unexpected model provenance: "
            f"model={verified_model!r}, effort={verified_effort!r}"
        )

    canonical_messages = json.dumps(
        messages, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    repo_root = args.repo_root.resolve()
    artifact = {
        "schema": "twisted-yetter/research-conversation-transcript/1",
        "artifact_id": (
            "twisted-yetter-premodular-formula-conjecture-transcript-v1"
        ),
        "status": "ARCHIVAL_SOURCE_ONLY",
        "epistemic_status": "UNREVIEWED_INITIAL_CONJECTURE",
        "formal_evidence": False,
        "top_notice": (
            "This artifact preserves the exact visible proposal turn. The "
            "proposal was materially qualified by the immediately following "
            "self-review and must not be read as a theorem, proof, accepted "
            "formula, or established project conclusion."
        ),
        "conversation_scope": {
            "thread_id": "019f6650-fe21-7cf2-8a63-6d3d14064cb5",
            "turn_ids": [TURN_ID],
            "start_utc": START_UTC,
            "end_utc": END_UTC,
            "local_timezone": "America/Edmonton",
            "local_date": "2026-07-16",
            "local_time_range": "23:22:11-23:25:35",
            "visible_messages_only": True,
            "hidden_reasoning_included": False,
            "tool_calls_or_outputs_included": False,
        },
        "provenance": {
            "model_verified_from_turn_context": verified_model,
            "reasoning_effort_verified_from_turn_context": verified_effort,
            "user_later_described_effort_as": "ultra",
            "provenance_discrepancy": (
                "The user later described this as an ultra-effort turn, but "
                "the source session records medium. The verified session value "
                "is retained."
            ),
            "source_kind": "local_codex_session_jsonl",
            "source_path_at_capture": str(args.source_jsonl.resolve()),
            "source_window_sha256": sha256_bytes(
                b"".join(raw for raw, _ in selected)
            ),
            "messages_canonical_sha256": sha256_bytes(canonical_messages),
            "source_repo_commit_before_generation": git_output(
                repo_root, "rev-parse", "HEAD"
            ),
            "source_repo_clean_before_generation": not bool(
                git_output(repo_root, "status", "--porcelain")
            ),
        },
        "generator_script": (
            "experiments/scripts/"
            "build_twisted_yetter_premodular_formula_conjecture_transcript_v1.py"
        ),
        "argv_template": (
            "python3 experiments/scripts/"
            "build_twisted_yetter_premodular_formula_conjecture_transcript_v1.py "
            "--source-jsonl <original-codex-session.jsonl> "
            "--output experiments/results/theory/"
            "twisted-yetter-premodular-formula-conjecture-transcript-v1.json"
        ),
        "message_counts": {
            "total": len(messages),
            "user": user_count,
            "assistant_visible": assistant_count,
            "assistant_final_answers": final_count,
        },
        "messages": messages,
        "explicit_non_claims": [
            "The initial proposal is not an established theorem.",
            "The initial proposal is not a proof or proof certificate.",
            "The initial proposal is not the project's accepted current conclusion.",
            "The initial proposal is not computationally validated on premodular Figure 21 data.",
            "The initial proposal's unqualified formulas are superseded by the self-review note.",
        ],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(artifact, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
