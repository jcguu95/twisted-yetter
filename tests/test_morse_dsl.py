import pytest

from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.k3_figure815_morse_draft import build_checkable_prefix


def test_nested_cups_order():
    m = MorseBuilder()
    m.cup("A", at="far-left")
    m.cup("B", between=("A.left", "A.right"))
    m.nested_cups(["L1", "L2", "L3"], between=("A.left", "B.left"))
    assert m.order == [
        "A.left",
        "L1.left",
        "L2.left",
        "L3.left",
        "L3.right",
        "L2.right",
        "L1.right",
        "B.left",
        "B.right",
        "A.right",
    ]


def test_times_infers_current_targets():
    m = MorseBuilder()
    m.cup("A", at="far-left")
    m.cup("B", at="far-right")
    m.cup("C", at="far-right")
    m.over_right("A.right", times=2)
    assert {"kind": "cross", "over": "A.right", "under": "B.left"} in m.forms
    assert {"kind": "cross", "over": "A.right", "under": "B.right"} in m.forms
    assert m.order == ["A.left", "B.left", "B.right", "A.right", "C.left", "C.right"]


def test_rejects_nonadjacent_crossing():
    m = MorseBuilder()
    m.cup("A", at="far-left")
    m.cup("B", at="far-right")
    with pytest.raises(ValueError, match="not adjacent"):
        m.cross(over="A.left", under="B.right")


def test_kink_preserves_order():
    m = MorseBuilder()
    m.cup("B", at="far-left")
    m.kink("B.left", sign="-", times=2)
    assert m.order == ["B.left", "B.right"]


def test_full_twist_uses_current_interval():
    m = MorseBuilder()
    m.cup("A", at="far-left")
    m.nested_cups(["L1", "L2", "L3"], between=("A.left", "A.right"))
    m.full_twist(start="L1.left", end="L3.left", direction="left", sign="-")
    assert {"kind": "cross", "over": "L3.left", "under": "L2.left", "sign": "-"} in m.forms
    assert {"kind": "cross", "over": "L3.left", "under": "L1.left", "sign": "-"} in m.forms
    assert {"kind": "cross", "over": "L2.left", "under": "L1.left", "sign": "-"} in m.forms


def test_figure815_e1_separates_b_framing_from_wheel_framings():
    forms = build_checkable_prefix(wheel_count=4).forms
    kinks = {
        form["strand"]: form["times"]
        for form in forms
        if form["kind"] == "kink"
    }
    assert kinks["B.left"] == 1
    assert all(kinks[f"L{i}.left"] == 2 for i in range(1, 5))
    assert all(kinks[f"R{i}.right"] == 2 for i in range(1, 5))


def test_figure815_e2_has_b_framing_minus_two():
    forms = build_checkable_prefix(wheel_count=10).forms
    b_kink = next(form for form in forms if form.get("strand") == "B.left")
    assert b_kink["times"] == 2
