import json
from pathlib import Path


ARTIFACT = Path("experiments/results/mtc-candidates/mtc-candidate-data-v1.json")


def _categories() -> dict[str, dict[str, object]]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return {category["category_id"]: category for category in exact["categories"]}


def test_mtc_candidate_artifact_records_the_three_requested_categories() -> None:
    categories = _categories()

    assert tuple(categories) == ("SU(2)_6", "Vec_Z3_q", "SU(3)_2")
    assert all(category["status"] == "pass" for category in categories.values())


def test_su2_level6_has_z2_universal_grading() -> None:
    su2 = _categories()["SU(2)_6"]

    assert su2["universal_group"]["name"] == "Z/2"  # type: ignore[index]
    assert su2["simple_labels"] == ["0", "1", "2", "3", "4", "5", "6"]
    assert su2["universal_group"]["degrees"] == {  # type: ignore[index]
        "0": 0,
        "1": 1,
        "2": 0,
        "3": 1,
        "4": 0,
        "5": 1,
        "6": 0,
    }
    assert su2["fusion_rules"]["1*1"] == {"0": 1, "2": 1}  # type: ignore[index]
    assert su2["fusion_rules"]["3*3"] == {"0": 1, "2": 1, "4": 1, "6": 1}  # type: ignore[index]


def test_vec_z3_pointed_category_has_z3_and_slide_controls() -> None:
    vec = _categories()["Vec_Z3_q"]

    assert vec["universal_group"]["name"] == "Z/3"  # type: ignore[index]
    assert vec["fusion_rules"]["1*2"] == {"0": 1}  # type: ignore[index]
    assert vec["twists"]["2"]["display"] == vec["twists"]["1"]["display"]  # type: ignore[index]

    slide_controls = vec["pointed_handle_slide_controls"]  # type: ignore[index]
    assert len(slide_controls) == 27
    assert {item["status"] for item in slide_controls} == {"pass"}


def test_su3_level2_is_the_first_nonpointed_z3_candidate() -> None:
    su3 = _categories()["SU(3)_2"]

    assert su3["universal_group"]["name"] == "Z/3"  # type: ignore[index]
    assert su3["simple_labels"] == [
        "(0,0)",
        "(1,0)",
        "(0,1)",
        "(2,0)",
        "(1,1)",
        "(0,2)",
    ]
    assert su3["universal_group"]["degrees"] == {  # type: ignore[index]
        "(0,0)": 0,
        "(1,0)": 1,
        "(0,1)": 2,
        "(2,0)": 2,
        "(1,1)": 0,
        "(0,2)": 1,
    }

    assert su3["fusion_rules"]["(1,0)*(0,1)"] == {"(0,0)": 1, "(1,1)": 1}  # type: ignore[index]
    assert su3["fusion_rules"]["(1,0)*(1,0)"] == {"(0,1)": 1, "(2,0)": 1}  # type: ignore[index]
