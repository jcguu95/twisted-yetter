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

    assert payload["status"] == "blocked-yasui-braid-payload-not-admitted"
    vec_z3 = payload["computed_categories"][0]
    assert vec_z3["category_id"] == "Vec_Z3_q"
    assert vec_z3["status"] == "blocked-yasui-braid-payload-not-admitted"
    assert vec_z3["rows"] == []
    assert vec_z3["observed_yasui_matrix_source_order"] == [
        [3, 2, -4],
        [2, 1, -2],
        [-4, -2, 3],
    ]
    assert vec_z3["expected_yasui_matrix_source_order"] == [
        [3, 2, 4],
        [2, 1, 2],
        [4, 2, 3],
    ]
    assert "payload admission failure" in vec_z3["reason"]

    blocked = {item["category_id"]: item for item in payload["blocked_categories"]}
    assert blocked["SU(2)_6"]["status"] == "blocked-yasui-braid-payload-not-admitted"
    assert "SU(2)_2 fixed-sector calibration" in blocked["SU(2)_6"]["reason"]
    assert "large mismatch" in blocked["SU(2)_6"]["reason"]
    assert any("SU(2)_2 fixed-sector Yasui calibration: pass" in item for item in blocked["SU(2)_6"]["latest_checks"])
    assert any("SU(2)_6 fusion-braid calibration gate: pass" in item for item in blocked["SU(2)_6"]["latest_checks"])
    assert any("SU(2)_6 standard-vs-Yasui comparison: numerical mismatch" in item for item in blocked["SU(2)_6"]["latest_checks"])
    assert any("Kirby-slide stress suite: pass" in item for item in blocked["SU(2)_6"]["latest_checks"])
    assert blocked["SU(3)_3"]["status"] == "blocked-no-arbitrary-link-evaluator"
