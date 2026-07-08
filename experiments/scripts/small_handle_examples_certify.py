#!/usr/bin/env python3
"""Generate algebraic sanity artifacts for small special-handle examples."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
import time

from twisted_yetter.artifacts import (
    default_tool_versions,
    dumps_certificate,
    file_sha256,
    git_metadata,
    make_certificate,
    utc_now_iso,
)
from twisted_yetter.small_handle_examples import analyze_catalog, load_catalog


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_INPUT = (
    REPO_ROOT
    / "experiments/inputs/small-handle-examples/special-handle-catalog-v1.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments/results/small-handle-examples/special-handle-catalog-sanity-v1.json"
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)

    started = utc_now_iso()
    start_monotonic = time.monotonic()
    payload = load_catalog(args.input)
    exact_output = analyze_catalog(payload)
    finished = utc_now_iso()
    status = "pass" if exact_output["status"] == "pass" else "fail"
    input_path = args.input.resolve()
    output_path = args.output.resolve()
    command = (
        "PYTHONPATH=src python experiments/scripts/"
        "small_handle_examples_certify.py --write"
    )
    certificate = make_certificate(
        status=status,
        command=command,
        argv=sys.argv[1:],
        git=git_metadata(REPO_ROOT),
        tool_versions=default_tool_versions(),
        input_hash=file_sha256(input_path),
        exact_output=exact_output,
        generator_script="experiments/scripts/small_handle_examples_certify.py",
        reproduce_command=command,
        started_at_utc=started,
        finished_at_utc=finished,
        elapsed_seconds=time.monotonic() - start_monotonic,
        repo_root=str(REPO_ROOT),
        notes=[
            "Algebraic handle-chain sanity only.",
            "This is not an RT link evaluation and not a closed 4D invariant.",
        ],
    )
    text = dumps_certificate(certificate)
    if args.write:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(text)
    else:
        print(text, end="")
    return 0 if status == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
