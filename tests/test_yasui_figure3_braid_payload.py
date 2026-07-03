import json
import os
import subprocess
from pathlib import Path


OUTPUT = Path("experiments/results/yasui/figure3-a1-braid-payload-v1.json")


def test_yasui_figure3_braid_payload_is_reproducible() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    subprocess.run(
        ["sage", "experiments/sage/yasui_figure3_a1_to_braid.sage.py"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )
    payload = json.loads(OUTPUT.read_text())

    assert payload["status"] == "pass"
    assert payload["component_order_in_source"] == ["A", "B", "C"]
    assert payload["component_order_in_braid"] == ["A", "C", "B"]
    assert payload["framings_in_braid_order"] == [3, 3, 1]
    assert payload["kirby_calibration"]["switched_crossing_ids"] == [
        "x04",
        "x05",
        "x08",
        "x09",
        "x13",
        "x15",
    ]
    assert payload["braid_closure_linking_matrix"] == [
        [0, 4, 2],
        [4, 0, 2],
        [2, 2, 0],
    ]
    assert payload["source_ordered_braid_linking_matrix"] == [
        [0, 2, 4],
        [2, 0, 2],
        [4, 2, 0],
    ]
    assert len(payload["su2_2_omega_evaluations"]) == 8
    assert len(payload["local_piece_programs"]) == 8


def test_yasui_figure3_matches_standard_cp2_two_cpbar_su2_2() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    subprocess.run(
        ["sage", "experiments/sage/yasui_figure3_a1_compare_standard.sage.py"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )
    payload = json.loads(
        Path("experiments/results/yasui/figure3-a1-standard-comparison-su2-2-v1.json").read_text()
    )

    assert payload["status"] == "pass"
    assert all(row["equal_raw_value"] for row in payload["rows"])
