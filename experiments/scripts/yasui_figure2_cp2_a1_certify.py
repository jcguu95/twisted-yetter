"""Certify the corrected Yasui Figure 2 CP2(a=1) crossing-table input."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time
from typing import Any

from twisted_yetter.artifacts import (
    default_tool_versions,
    dumps_certificate,
    file_sha256,
    git_metadata,
    hash_json,
    make_certificate,
    utc_now_iso,
)
from twisted_yetter.yasui_figure2_cp2 import (
    analyze_crossing_table,
    load_crossing_table,
    tham511_context,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure2-cp2-a1-crossing-table.json"
SANITY_OUTPUT = (
    REPO_ROOT / "experiments" / "results" / "yasui" / "figure2-cp2-a1-pd-sanity-v1.json"
)
CONTEXT_OUTPUT = (
    REPO_ROOT / "experiments" / "results" / "yasui" / "figure2-cp2-a1-tham511-context-v1.json"
)


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def stable_json(payload: Any) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def context_artifact(
    *,
    context: dict[str, Any],
    input_path: Path,
    command: str,
    argv: list[str],
    started_at_utc: str,
    start_time: float,
) -> dict[str, Any]:
    return {
        **context,
        "generator_script": rel(Path(__file__)),
        "command": command,
        "argv": argv,
        "reproduce_command": (
            "PYTHONPATH=src uv run python experiments/scripts/"
            "yasui_figure2_cp2_a1_certify.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_metadata(REPO_ROOT),
        "tool_versions": default_tool_versions(),
        "input": rel(input_path),
        "input_hash": file_sha256(input_path),
        "started_at_utc": started_at_utc,
        "finished_at_utc": utc_now_iso(),
        "elapsed_seconds": int(round(time.monotonic() - start_time)),
    }


def build_outputs(input_path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    payload = load_crossing_table(input_path)
    analysis = analyze_crossing_table(payload)
    context = tham511_context(payload, analysis)
    return analysis, context


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=INPUT)
    parser.add_argument("--sanity-output", type=Path, default=SANITY_OUTPUT)
    parser.add_argument("--context-output", type=Path, default=CONTEXT_OUTPUT)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    started_at_utc = utc_now_iso()
    start_time = time.monotonic()
    command = " ".join(sys.argv)
    argv = [str(item) for item in sys.argv]

    analysis, context = build_outputs(args.input)
    certificate = make_certificate(
        status="pass" if analysis["status"] == "pass" else "inconclusive",
        command=command,
        argv=argv,
        git=git_metadata(REPO_ROOT),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "input": rel(args.input),
                "input_sha256": file_sha256(args.input),
                "expected_matrix": analysis["expected_matrix"],
            }
        ),
        exact_output={
            **analysis,
            "source_input": rel(args.input),
            "context_artifact": rel(args.context_output),
        },
        generator_script=rel(Path(__file__)),
        reproduce_command=(
            "PYTHONPATH=src uv run python experiments/scripts/"
            "yasui_figure2_cp2_a1_certify.py --write"
        ),
        started_at_utc=started_at_utc,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(round(time.monotonic() - start_time)),
        repo_root=str(REPO_ROOT),
        notes=[
            "This certifies the corrected hand PD bookkeeping and matrix sanity only.",
            "The Tham 5.11 context artifact remains a working hypothesis, not a theorem.",
        ],
    )
    context_payload = context_artifact(
        context=context,
        input_path=args.input,
        command=command,
        argv=argv,
        started_at_utc=started_at_utc,
        start_time=start_time,
    )

    if args.write:
        args.sanity_output.parent.mkdir(parents=True, exist_ok=True)
        args.context_output.parent.mkdir(parents=True, exist_ok=True)
        args.sanity_output.write_text(dumps_certificate(certificate))
        args.context_output.write_text(stable_json(context_payload))

    summary = {
        "sanity_status": analysis["status"],
        "sanity_artifact": rel(args.sanity_output),
        "context_status": context["status"],
        "context_artifact": rel(args.context_output),
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if analysis["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
