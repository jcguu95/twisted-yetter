import json
from pathlib import Path


ARTIFACT = Path("experiments/results/mtc-candidates/vec-z3-pointed-stress-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_vec_z3_stress_summary_is_successful() -> None:
    exact = _exact_output()

    assert exact["category_id"] == "Vec_Z3_q"
    assert exact["universal_group"] == "Z/3"
    assert exact["total_move_count"] == 121
    assert exact["total_comparison_count"] == 17589
    assert exact["total_failure_count"] == 0


def test_vec_z3_stress_covers_sizes_one_through_five() -> None:
    exact = _exact_output()
    cases = exact["dimension_cases"]

    assert [case["size"] for case in cases] == [1, 2, 3, 4, 5]
    assert [case["move_count"] for case in cases] == [1, 7, 19, 36, 58]
    assert [case["comparison_count"] for case in cases] == [3, 63, 513, 2916, 14094]
    assert all(case["status"] == "pass" for case in cases)
    assert all(case["failure_count"] == 0 for case in cases)


def test_vec_z3_stress_records_sample_controls() -> None:
    exact = _exact_output()

    for case in exact["dimension_cases"]:
        samples = case["sample_controls"]
        assert samples
        assert {sample["status"] for sample in samples} == {"pass"}
        assert all("basis" in sample for sample in samples)
        assert all("labels_before" in sample for sample in samples)
        assert all("labels_after" in sample for sample in samples)
