import json
import subprocess
from collections import Counter
from pathlib import Path


INPUT = Path("experiments/inputs/yasui/figure3-a1-crossing-table.json")
CALIBRATION = Path("experiments/results/yasui/figure3-a1-calibration-v1.json")


def test_yasui_figure3_a1_arc_bookkeeping_passes() -> None:
    payload = json.loads(INPUT.read_text())
    counter = Counter(label for crossing in payload["crossings"] for label in crossing["tuple"])

    for component in payload["components"]:
        component_id = component["id"]
        for index in range(1, component["arc_count"] + 1):
            assert counter[f"{component_id}{index}"] == 2


def test_yasui_figure3_a1_records_twist_blocker() -> None:
    payload = json.loads(INPUT.read_text())

    assert payload["status"] == "needs-self-twist-expansion-and-sign-calibration"
    assert payload["self_twists"][0]["component_id"] == "A"
    assert "A15" in payload["self_twists"][0]["description"]
    assert payload["self_twists"][0]["status"] == "must be expanded before evaluator use"


def test_yasui_figure3_calibration_report_is_reproducible() -> None:
    subprocess.run(
        ["python3", "experiments/scripts/yasui_figure3_a1_calibration.py"],
        check=True,
        capture_output=True,
        text=True,
    )
    report = json.loads(CALIBRATION.read_text())

    assert report["status"] == "blocked-before-evaluator"
    pair_reports = {item["pair"]: item for item in report["pair_reports"]}
    assert pair_reports["A-C"]["status"] == "pass"
    assert pair_reports["B-C"]["status"] == "pass"
    assert pair_reports["A-B"]["status"] == "needs-calibration"
    assert pair_reports["A-B"]["provisional_signed_sum"] == -4
    assert pair_reports["A-B"]["target_signed_sum"] == 4
