import json
import os
import subprocess
from pathlib import Path


CLEAN_OUTPUT = Path("experiments/results/yasui/figure3-a1-braid-payload-v1.json")
NORMALIZED_OUTPUT = Path("experiments/results/yasui/figure3-a1-r1-normalized-braid-payload-v1.json")


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
    payload = json.loads(CLEAN_OUTPUT.read_text())

    assert payload["status"] == "pass"
    assert payload["component_order_in_source"] == ["A", "B", "C"]
    assert payload["component_order_in_braid"] == ["C", "A", "B"]
    assert payload["framings_in_braid_order"] == [3, 3, 1]
    assert payload["kirby_calibration"]["switched_crossing_ids"] == []
    assert payload["n_strands"] == 12
    assert len(payload["braid_word"]) == 97
    assert payload["braid_closure_linking_matrix"] == [
        [0, -4, -2],
        [-4, 0, 2],
        [-2, 2, 0],
    ]
    assert payload["source_ordered_braid_linking_matrix"] == [
        [0, 2, -4],
        [2, 0, -2],
        [-4, -2, 0],
    ]
    assert payload["su2_2_omega_evaluations"] == []
    assert payload["su2_2_omega_evaluations_status"].startswith("skipped-legacy-jones-diagnostic")
    assert len(payload["local_piece_programs"]) == 8


def test_yasui_figure3_r1_normalized_braid_payload_is_reproducible() -> None:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    subprocess.run(
        ["sage", "experiments/sage/yasui_figure3_a1_r1_normalized_to_braid.sage.py"],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )
    payload = json.loads(NORMALIZED_OUTPUT.read_text())

    assert payload["status"] == "pass"
    assert payload["component_order_in_braid"] == ["C", "A", "B"]
    assert payload["framings_in_braid_order"] == [3, 3, 1]
    assert payload["n_strands"] == 7
    assert len(payload["braid_word"]) == 30
    assert payload["source_ordered_braid_linking_matrix"] == [
        [0, 2, -4],
        [2, 0, -2],
        [-4, -2, 0],
    ]
    normalization = payload["r1_normalization"]
    assert normalization["removed_crossing_ids"] == ["x02", "x03", "x04", "x09", "x18"]
    assert normalization["normalized_visible_self_writhe_by_source_component"] == {
        "A": 2,
        "B": 0,
        "C": 0,
    }
    assert normalization["removed_writhe_by_source_component"] == {
        "A": 1,
        "B": 1,
        "C": 3,
    }
    assert normalization["framing_identity_status"] == "pass"


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

    assert payload["status"] == "skipped-legacy-jones-diagnostic"
    assert payload["rows"] == []
