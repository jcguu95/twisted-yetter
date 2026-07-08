#!/usr/bin/env python3
from __future__ import annotations

import os
import json
import subprocess
import sys
from pathlib import Path


DOGFOOD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOGFOOD_ROOT.parent
DEFAULT_CTL_META_ROOT = REPO_ROOT.parent / "ctl-meta"
UPSTREAM_CTL_STORE = Path("meta") / "ctl-dogfood" / "scripts" / "ctl_store.py"


def ctl_meta_root() -> Path:
    return Path(os.environ.get("CTL_META_ROOT", DEFAULT_CTL_META_ROOT)).resolve()


def upstream_script() -> Path:
    return ctl_meta_root() / UPSTREAM_CTL_STORE


def has_store_root_arg(argv: list[str]) -> bool:
    return any(arg == "--store-root" or arg.startswith("--store-root=") for arg in argv)


def repo_relative_if_inside(path_text: str) -> str:
    path = Path(path_text)
    if not path.is_absolute():
        return path_text
    try:
        return path.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path_text


def normalize_repo_paths(argv: list[str]) -> list[str]:
    out: list[str] = []
    index = 0
    while index < len(argv):
        arg = argv[index]
        if arg == "--path" and index + 1 < len(argv):
            out.extend([arg, repo_relative_if_inside(argv[index + 1])])
            index += 2
            continue
        if arg.startswith("--path="):
            key, value = arg.split("=", 1)
            out.append(f"{key}={repo_relative_if_inside(value)}")
            index += 1
            continue
        out.append(arg)
        index += 1
    return out


def run_upstream(argv: list[str], *, capture: bool = False) -> subprocess.CompletedProcess[str]:
    upstream = upstream_script()
    if not upstream.exists():
        raise FileNotFoundError(f"missing upstream CTL store provider: {upstream}")
    return subprocess.run(
        [sys.executable, str(upstream), *argv],
        check=False,
        capture_output=capture,
        text=capture,
    )


def path_hygiene_report(dogfood_root: Path = DOGFOOD_ROOT) -> dict[str, object]:
    result = run_upstream(["--store-root", str(dogfood_root), "path-hygiene"], capture=True)
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip())
    return json.loads(result.stdout)


def main() -> int:
    argv = normalize_repo_paths(sys.argv[1:])
    if not has_store_root_arg(argv):
        argv = ["--store-root", str(DOGFOOD_ROOT), *argv]

    try:
        return run_upstream(argv).returncode
    except FileNotFoundError as exc:
        print(str(exc), file=sys.stderr)
        return 127


if __name__ == "__main__":
    raise SystemExit(main())
