from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
CTL_STORE = REPO_ROOT / "ctl-dogfood" / "scripts" / "ctl_store.py"
CTL_META_ROOT = Path(os.environ.get("CTL_META_ROOT", REPO_ROOT.parent / "ctl-meta")).resolve()


def run_ctl_store(*args: str, timeout: int = 120) -> dict[str, object]:
    env = {**os.environ, "CTL_META_ROOT": str(CTL_META_ROOT)}
    result = subprocess.run(
        [sys.executable, str(CTL_STORE), *args],
        check=False,
        capture_output=True,
        text=True,
        timeout=timeout,
        env=env,
    )
    assert result.returncode == 0, result.stderr or result.stdout
    return json.loads(result.stdout)


def test_ctl_store_wrapper_is_thin_adapter() -> None:
    text = CTL_STORE.read_text()

    assert "import ctl_ref" not in text
    assert "def search_current" not in text
    assert "UPSTREAM_CTL_STORE" in text
    assert "--store-root" in text


def test_verify_uses_twisted_yetter_store_by_default() -> None:
    report = run_ctl_store("verify")

    assert report["status"] == "ok"
    assert report["project_id"] == "project:twisted-yetter"


def test_lookup_current_bound_subject() -> None:
    report = run_ctl_store("lookup-current", "subject:twisted-yetter:category-family:su2-k")

    assert report["status"] == "ok"
    assert report["source_state"] == "current-ctl-object"
    binding = report["binding"]
    assert isinstance(binding, dict)
    assert binding["state"] == "bound"


def test_lookup_current_absent_binding() -> None:
    report = run_ctl_store("lookup-current", "claim:does-not-exist")

    assert report["status"] == "ok"
    assert report["source_state"] == "absent-current-binding"
    binding = report["binding"]
    assert isinstance(binding, dict)
    assert binding["state"] == "absent"


def test_search_current_is_discovery_only() -> None:
    report = run_ctl_store("search-current", "SU(2)_k", timeout=180)

    assert report["status"] == "ok"
    assert report["source_state"] == "current-discovery-only"
    matches = report["matches"]
    assert isinstance(matches, list)
    assert matches
    assert {match["source_state"] for match in matches if isinstance(match, dict)} == {"current-discovery-only"}
