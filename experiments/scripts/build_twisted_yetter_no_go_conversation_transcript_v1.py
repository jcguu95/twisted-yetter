#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any


TURN_IDS = [
    "019f6d44-b607-7640-bdbe-b1f2dc5327a0",
    "019f6d59-c618-71e2-b1ba-dfe9301b8059",
    "019f6d7a-8940-7fd3-8c17-7f260c2a3ec6",
]
START_UTC = "2026-07-16T23:31:46.290Z"
END_UTC = "2026-07-17T00:33:17.291Z"


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
        description="Preserve the exact visible no-go proof conversation window."
    )
    parser.add_argument("--source-jsonl", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()

    raw_lines = args.source_jsonl.read_bytes().splitlines(keepends=True)
    selected: list[tuple[bytes, dict[str, Any]]] = []
    for raw_line in raw_lines:
        record = json.loads(raw_line)
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
        if turn_id not in TURN_IDS:
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
                "turn_id": payload["internal_chat_message_metadata_passthrough"][
                    "turn_id"
                ],
                "role": payload["role"],
                "phase": payload.get("phase"),
                "text": message_text(payload),
            }
        )

    user_count = sum(message["role"] == "user" for message in messages)
    assistant_count = sum(message["role"] == "assistant" for message in messages)
    final_count = sum(message["phase"] == "final_answer" for message in messages)
    if (user_count, assistant_count, final_count) != (3, 11, 3):
        raise SystemExit(
            "unexpected transcript shape: "
            f"users={user_count}, assistants={assistant_count}, finals={final_count}"
        )
    if sorted({message["turn_id"] for message in messages}) != sorted(TURN_IDS):
        raise SystemExit("transcript turn IDs do not match the frozen turn set")

    canonical_messages = json.dumps(
        messages, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    repo_root = args.repo_root.resolve()
    artifact = {
        "schema": "twisted-yetter/research-conversation-transcript/1",
        "artifact_id": "twisted-yetter-no-go-proof-conversation-transcript-v1",
        "status": "ARCHIVAL_SOURCE_ONLY",
        "epistemic_status": "UNREVIEWED_CANDIDATE_ARGUMENT",
        "formal_evidence": False,
        "top_notice": (
            "This artifact preserves an exact visible research conversation. It is not a "
            "theorem, proof certificate, accepted project conclusion, or evidence that the "
            "proposed no-go argument is correct."
        ),
        "conversation_scope": {
            "thread_id": "019f6650-fe21-7cf2-8a63-6d3d14064cb5",
            "turn_ids": TURN_IDS,
            "start_utc": START_UTC,
            "end_utc": END_UTC,
            "start_user_text_prefix": "我很悲觀，看來這就代表 MTC 是完全沒有用的。",
            "end_assistant_text_prefix": "**先釐清名稱**",
            "visible_messages_only": True,
            "hidden_reasoning_included": False,
            "tool_calls_or_outputs_included": False,
        },
        "provenance": {
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
            "source_kind": "local_codex_session_jsonl",
            "source_path_at_capture": str(args.source_jsonl.resolve()),
            "source_window_sha256": sha256_bytes(b"".join(raw for raw, _ in selected)),
            "messages_canonical_sha256": sha256_bytes(canonical_messages),
            "source_repo_commit_before_generation": git_output(repo_root, "rev-parse", "HEAD"),
            "source_repo_clean_before_generation": not bool(
                git_output(repo_root, "status", "--porcelain")
            ),
        },
        "generator_script": "experiments/scripts/build_twisted_yetter_no_go_conversation_transcript_v1.py",
        "argv_template": (
            "python3 experiments/scripts/build_twisted_yetter_no_go_conversation_transcript_v1.py "
            "--source-jsonl <original-codex-session.jsonl> "
            "--output experiments/results/theory/"
            "twisted-yetter-no-go-proof-conversation-transcript-v1.json"
        ),
        "message_counts": {
            "total": len(messages),
            "user": user_count,
            "assistant_visible": assistant_count,
            "assistant_final_answers": final_count,
        },
        "messages": messages,
        "explicit_non_claims": [
            "The conversation is not an established theorem.",
            "The conversation is not a completed proof or proof certificate.",
            "The conversation is not the project's accepted current mathematical conclusion.",
            "The user's lack of a specific objection on initial reading is not expert verification.",
            "The marked stable realization argument and all other proof obligations still require review and formal write-up.",
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
