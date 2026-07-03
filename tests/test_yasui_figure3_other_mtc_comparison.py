import json
import os
import subprocess
from pathlib import Path


OUTPUT = Path("experiments/results/yasui/figure3-a1-other-mtc-comparison-v1.json")


def test_yasui_figure3_vec_z3_matches_standard_and_nonpointed_are_blocked() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    subprocess.run(
        ["sage", "experiments/sage/yasui_figure3_a1_other_mtc_comparison.sage.py"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )
    payload = json.loads(OUTPUT.read_text())

    assert payload["status"] == "pass-with-blocked-nonpointed"
    vec_z3 = payload["computed_categories"][0]
    assert vec_z3["category_id"] == "Vec_Z3_q"
    assert vec_z3["status"] == "pass"
    assert len(vec_z3["rows"]) == 27
    assert all(row["equal_raw_value"] for row in vec_z3["rows"])

    blocked = {item["category_id"]: item for item in payload["blocked_categories"]}
    assert blocked["SU(2)_6"]["status"] == "blocked-no-arbitrary-link-evaluator"
    assert blocked["SU(3)_3"]["status"] == "blocked-no-arbitrary-link-evaluator"
