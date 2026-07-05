import json
import os
import subprocess
from pathlib import Path


def load_json(path: str) -> dict:
    return json.loads(Path(path).read_text())


def test_hand_entered_pd_codes_are_present() -> None:
    cases = [
        (
            "experiments/inputs/yasui/figure3-a1-crossing-table.json",
            "needs-evaluator-artifact",
            ["A", "B", "C"],
            25,
        ),
        (
            "experiments/inputs/yasui/figure3-a3-crossing-table.json",
            "needs-evaluator-artifact",
            ["A", "B", "C"],
            46,
        ),
        (
            "experiments/inputs/akbulut/figure1-e1-crossing-table.json",
            "initial-transcription-cyclic-sign-sanity-pass",
            ["A", "B", "C", "D", "E", "F", "G", "H", "X", "Y"],
            30,
        ),
    ]

    for path, status, components, crossing_count in cases:
        payload = load_json(path)
        assert payload["status"] == status
        assert [component["id"] for component in payload["components"]] == components
        assert len(payload["crossings"]) == crossing_count


def assert_all_alpha_pass(path: str, category_id: str, rows: int = 8) -> None:
    payload = load_json(path)
    assert payload["status"] == "pass"
    assert payload["category_id"] == category_id
    assert payload["alpha_mode"] == "all-alpha"
    assert len(payload["rows"]) == rows
    assert all(row["close_under_tolerance"] for row in payload["rows"])


def test_yasui_a1_r1_normalized_su2_all_alpha_artifacts_pass() -> None:
    assert_all_alpha_pass(
        "experiments/results/yasui/figure3-a1-r1-normalized-su2-2-all-alpha-raw-comparison-v3.json",
        "SU(2)_2",
    )
    assert_all_alpha_pass(
        "experiments/results/yasui/figure3-a1-r1-normalized-su2-3-all-alpha-raw-comparison-v2.json",
        "SU(2)_3",
    )
    assert_all_alpha_pass(
        "experiments/results/yasui/figure3-a1-r1-normalized-su2-6-all-alpha-raw-comparison-v2.json",
        "SU(2)_6",
    )


def test_yasui_a3_su2_all_alpha_artifacts_pass() -> None:
    assert_all_alpha_pass(
        "experiments/results/yasui/figure3-a3-su2-2-all-alpha-chunked-comparison-v1.json",
        "SU(2)_2",
    )
    assert_all_alpha_pass(
        "experiments/results/yasui/figure3-a3-su2-3-all-alpha-chunked-comparison-v1.json",
        "SU(2)_3",
    )
    assert_all_alpha_pass(
        "experiments/results/yasui/figure3-a3-su2-6-all-alpha-chunked-comparison-v1.json",
        "SU(2)_6",
    )


def test_akbulut_e1_current_su2_artifacts_pass() -> None:
    su2_2 = load_json("experiments/results/akbulut/figure1-e1-su2-2-sampled-twists-comparison-v1.json")
    assert su2_2["category_id"] == "SU(2)_2"
    assert su2_2["mismatch_count"] == 0
    assert su2_2["row_count"] == len(su2_2["rows"])
    assert all(row["close_under_tolerance"] for row in su2_2["rows"])

    su2_3 = load_json("experiments/results/akbulut/figure1-e1-su2-3-twisted-x-chunked-comparison-v1.json")
    assert su2_3["status"] == "pass"
    assert su2_3["category_id"] == "SU(2)_3"
    assert su2_3["comparison_against_standard_is_meaningful"] is True
    assert float(su2_3["abs_difference"]) < 1e-9


def sage_env() -> dict[str, str]:
    env = dict(os.environ)
    env["DOT_SAGE"] = str(Path.cwd() / ".sage")
    return env


def test_akbulut_e1_su2_2_base_generator_reproduces() -> None:
    result = subprocess.run(
        ["sage", "experiments/sage/akbulut_figure1_e1_su2_2_untwisted_comparison.sage.py"],
        check=True,
        capture_output=True,
        text=True,
        env=sage_env(),
    )
    assert '"status": "pass"' in result.stdout

    payload = load_json("experiments/results/akbulut/figure1-e1-su2-2-untwisted-comparison-v1.json")
    assert payload["status"] == "pass"
    assert payload["category_id"] == "SU(2)_2"


def test_akbulut_e1_su2_3_twisted_x_worker_dependency_probe() -> None:
    result = subprocess.run(
        [
            "sage",
            "experiments/sage/akbulut_figure1_e1_su2_3_twisted_x_chunked.sage.py",
            "--worker",
            "--start",
            "0",
            "--count",
            "1",
            "--no-write-partial",
        ],
        check=True,
        capture_output=True,
        text=True,
        env=sage_env(),
    )
    payload = json.loads(result.stdout.strip().splitlines()[-1])
    assert payload["schema"] == "twisted-yetter.akbulut-figure1-e1-su2-3-twisted-x-chunk.v1"
    assert payload["level"] == 3
    assert payload["start"] == 0
    assert payload["end"] == 1
    assert payload["processed"] == 1
