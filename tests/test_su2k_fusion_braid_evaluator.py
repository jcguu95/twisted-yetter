import os
import subprocess
from pathlib import Path


def test_su2k_fusion_braid_evaluator_self_test_passes() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    result = subprocess.run(
        ["sage", "experiments/sage/su2k_fusion_braid_evaluator.sage.py", "--self-test"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert '"status": "pass"' in result.stdout
    assert "right_trefoil_sigma_matches_existing_oracle_value" in result.stdout
