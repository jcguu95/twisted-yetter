import cmath
import math

from experiments.scripts.reweight_figure21_su2_2_framings import (
    reweight_record,
    sector_framing_phase,
    su2_k2_twists,
)


def test_su2_k2_framing_phase_is_componentwise_ribbon_twist():
    twists = su2_k2_twists()
    phase = sector_framing_phase(
        (1, 2),
        ("A", "B"),
        {"A": 2, "B": -1},
        twists,
    )
    expected = cmath.exp(3j * math.pi / 4) * -1.0
    assert abs(phase - expected) < 1e-12


def test_reweight_record_preserves_blackboard_contribution():
    source = {
        "sector_id": 7,
        "labels": [1],
        "status": "EVALUATED_NONZERO",
        "evaluation_id": "source-id",
        "raw_graph_scalar": [2.0, 0.0],
        "weighted_contribution": [3.0, 0.0],
        "special_label_contributions": [
            {
                "special_label": 0,
                "source_value": [2.0, 0.0],
                "weighted_source_value": [2.0, 0.0],
            }
        ],
    }
    result = reweight_record(
        source,
        component_order=("A",),
        framing_corrections={"A": 1},
        twists={0: 1.0 + 0.0j, 1: 1.0j, 2: -1.0 + 0.0j},
        evaluation_id="framed-id",
    )
    assert result["blackboard_raw_graph_scalar"] == [2.0, 0.0]
    assert result["blackboard_weighted_contribution"] == [3.0, 0.0]
    assert result["raw_graph_scalar"] == [0.0, 2.0]
    assert result["weighted_contribution"] == [0.0, 3.0]
    assert result["source_evaluation_id"] == "source-id"
    assert result["evaluation_id"] == "framed-id"


def test_reweight_record_requires_inherited_source_identity():
    source = {
        "sector_id": 1,
        "labels": [1],
        "status": "PRUNED_NO_VACUUM",
    }
    try:
        reweight_record(
            source,
            component_order=("A",),
            framing_corrections={"A": 0},
            twists=su2_k2_twists(),
            evaluation_id="framed-id",
        )
    except ValueError as exc:
        assert "inherited evaluation identity" in str(exc)
    else:
        raise AssertionError("missing source identity was accepted")
