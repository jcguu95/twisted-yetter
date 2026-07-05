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
        for label in component["arc_order"]:
            assert counter[label] == 2


def test_yasui_figure3_a1_records_twist_blocker() -> None:
    payload = json.loads(INPUT.read_text())

    assert payload["status"] == "needs-evaluator-artifact"
    twists = {item["component_id"]: item for item in payload["self_twists"]}
    assert set(twists) == {"A", "B", "C"}
    assert "A15" in twists["A"]["description"]
    assert twists["A"]["status"] == "expanded-as-source-transcribed-self-crossing"
    assert twists["A"]["expanded_crossing_ids"] == ["x18"]
    assert twists["A"]["expanded_crossing_tuple"] == [
        "A15b",
        "A15b",
        "A15c",
        "A15a",
    ]
    assert twists["B"]["expanded_crossing_ids"] == ["x09"]
    assert twists["C"]["expanded_crossing_ids"] == ["x02", "x03", "x04"]


def test_yasui_figure3_calibration_report_is_reproducible() -> None:
    subprocess.run(
        ["python3", "experiments/scripts/yasui_figure3_a1_calibration.py"],
        check=True,
        capture_output=True,
        text=True,
    )
    report = json.loads(CALIBRATION.read_text())

    assert report["status"] == "pass"
    pair_reports = {item["pair"]: item for item in report["pair_reports"]}
    assert pair_reports["A-C"]["status"] == "pass"
    assert pair_reports["A-B"]["status"] == "pass"
    assert pair_reports["A-B"]["provisional_signed_sum"] == 4
    assert pair_reports["A-B"]["target_signed_sum"] == 4
    assert pair_reports["A-C"]["provisional_signed_sum"] == -8
    assert pair_reports["A-C"]["target_signed_sum"] == -8
    assert pair_reports["B-C"]["status"] == "pass"
    assert pair_reports["B-C"]["provisional_signed_sum"] == -4
    assert pair_reports["B-C"]["target_signed_sum"] == -4
    framing_reports = {item["component"]: item for item in report["framing_reports"]}
    assert framing_reports["A"]["visible_self_writhe"] == 3
    assert framing_reports["B"]["visible_self_writhe"] == 1
    assert framing_reports["C"]["visible_self_writhe"] == 3
    assert framing_reports["A"]["effective_framing_correction"] == 0
    assert framing_reports["B"]["effective_framing_correction"] == 0
    assert framing_reports["C"]["effective_framing_correction"] == 0
