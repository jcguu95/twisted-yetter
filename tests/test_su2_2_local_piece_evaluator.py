import json
from pathlib import Path


ARTIFACT = Path("experiments/results/local-piece/su2-2-local-piece-evaluator-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_local_piece_evaluator_records_b0_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su2_2-local-piece-evaluator.v1"
    assert exact["category_id"] == "SU(2)_2"
    assert exact["claim_level"] == "B0 executable local-piece evaluator / braid-closure slice"
    assert "local braid-crossing pieces" in exact["scope"]
    assert "arbitrary planar tensor graph" in exact["not_scope"]
    assert exact["supported_piece_kinds"] == ["braid_crossing"]
    assert "cup" in exact["next_piece_kinds"]
    assert exact["program_count"] == 5
    assert exact["move_regression_count"] == 4


def test_local_piece_examples_dispatch_to_su2_2_oracle() -> None:
    exact = _exact_output()
    evaluations = {item["program"]["program_id"]: item for item in exact["evaluations"]}

    assert set(evaluations) == {
        "lp-cp2-omega0-fixed-psi",
        "lp-unlink-two-components",
        "lp-positive-hopf",
        "lp-right-trefoil",
        "lp-figure-eight",
    }
    assert evaluations["lp-positive-hopf"]["diagnostics"]["braid_word"] == [1, 1]
    assert evaluations["lp-positive-hopf"]["diagnostics"]["linking_matrix"] == [[0, 1], [1, 0]]
    assert evaluations["lp-right-trefoil"]["diagnostics"]["closure_data"]["component_count"] == 1

    assert evaluations["lp-cp2-omega0-fixed-psi"]["oracle_output"]["omega_value"]["display"] == (
        "2*zeta16^3"
    )
    assert evaluations["lp-right-trefoil"]["oracle_output"]["omega_value"]["display"] == "4"
    assert evaluations["lp-figure-eight"]["oracle_output"]["omega_value"]["display"] == "0"


def test_local_piece_move_regressions_pass_exactly() -> None:
    exact = _exact_output()
    regressions = exact["move_regressions"]

    assert {item["status"] for item in regressions} == {"pass"}
    assert {item["name"] for item in regressions} == {
        "r-r-inverse-cancellation-two-strand-unlink",
        "trefoil-positive-markov-stabilization",
        "trefoil-negative-markov-stabilization",
        "trefoil-braid-conjugation",
    }

    markov = [
        item
        for item in regressions
        if item["kind"] == "one-component-all-sector-local-piece-equivalence"
    ]
    assert markov
    for regression in markov:
        assert regression["sector_check_count"] == 4
        assert {item["status"] for item in regression["sector_checks"]} == {"pass"}


def test_local_piece_artifact_keeps_upstream_stress_gates_visible() -> None:
    exact = _exact_output()

    assert "experiments/results/sage-stress/su2-2-braid-auto-stress-v1.json" in exact[
        "upstream_regression_artifacts"
    ]
    assert "experiments/results/mtc-candidates/su3-3-multiplicity-stress-v1.json" in exact[
        "upstream_regression_artifacts"
    ]


def test_local_piece_artifact_is_float_free() -> None:
    payload = json.loads(ARTIFACT.read_text())
    _assert_no_float(payload)


def _assert_no_float(value: object) -> None:
    if isinstance(value, float):
        raise AssertionError(f"float found in exact payload: {value!r}")
    if isinstance(value, dict):
        for item in value.values():
            _assert_no_float(item)
    if isinstance(value, list):
        for item in value:
            _assert_no_float(item)
