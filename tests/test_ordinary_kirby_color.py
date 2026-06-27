import json
from pathlib import Path

import pytest

from twisted_yetter.link_diagram import (
    Component,
    LinkDiagram,
    hopf_link,
    s4_diagram,
    unlink,
    unknot,
)
from twisted_yetter.ordinary_kirby_color import (
    CLAIM_LEVEL,
    HANDLE_SCOPE,
    KIRBY_COLOR_CONVENTION,
    NORMALIZATION_STATUS,
    ORDINARY_KIRBY_COLOR_SCHEMA,
    SOURCE_STATUS_BY_SLOT,
    evaluate_ordinary_kirby_color,
    load_fixture_certificate,
    omega_coefficients,
    stable_ordinary_kirby_color_json,
)
from twisted_yetter.su2_level2 import SQRT2, QuadraticSurd


TOY_FIXTURE_DIR = Path("experiments/inputs/toy-diagrams")


def test_omega_coefficients_are_experimental_quantum_dimensions() -> None:
    assert omega_coefficients() == {
        "0": QuadraticSurd(1),
        "1": SQRT2,
        "2": QuadraticSurd(1),
    }


def test_empty_fixture_certificate_records_one_and_source_slots() -> None:
    certificate = evaluate_ordinary_kirby_color(s4_diagram())

    assert certificate["schema"] == ORDINARY_KIRBY_COLOR_SCHEMA
    assert certificate["status"] == "pass"
    assert certificate["kirby_color_convention"] == KIRBY_COLOR_CONVENTION
    assert certificate["kirby_color_formula"] == "omega = sum_i d_i X_i"
    assert certificate["sector_count"] == 1
    assert certificate["total_value"] == _sparse_sum([(0, QuadraticSurd(1))])
    assert certificate["source_status_by_slot"] == SOURCE_STATUS_BY_SLOT
    assert set(certificate["source_status_by_slot"].values()) == {"SOURCE NEEDED"}
    assert certificate["handle_scope"] == HANDLE_SCOPE
    assert certificate["normalization_status"] == NORMALIZATION_STATUS
    assert certificate["claim_level"] == CLAIM_LEVEL
    assert certificate["closed_4_manifold_claim_allowed"] is False
    assert "closed 4-manifold invariant" in certificate["claim_boundary"]["not_scope"]


def test_zero_framed_unknot_sums_to_global_dimension_without_normalization_claim() -> None:
    certificate = evaluate_ordinary_kirby_color(unknot("u", framing=0))

    assert certificate["sector_count"] == 3
    assert certificate["total_value"] == _sparse_sum([(0, QuadraticSurd(4))])
    assert [sector["labels_by_component"] for sector in certificate["sectors"]] == [
        {"u": "0"},
        {"u": "1"},
        {"u": "2"},
    ]


def test_plus_one_framed_unknot_records_exact_symbolic_zeta_terms() -> None:
    certificate = load_fixture_certificate(
        TOY_FIXTURE_DIR / "cp2-plus-one-framed-unknot.json"
    )

    assert certificate["diagram_id"] == "cp2-plus-one-framed-unknot"
    assert certificate["fixture_path"] == (
        "experiments/inputs/toy-diagrams/cp2-plus-one-framed-unknot.json"
    )
    assert certificate["total_value"] == _sparse_sum(
        [
            (0, QuadraticSurd(1)),
            (3, QuadraticSurd(2)),
            (8, QuadraticSurd(1)),
        ]
    )


def test_split_unlink_fixture_sums_componentwise_over_all_label_assignments() -> None:
    certificate = load_fixture_certificate(TOY_FIXTURE_DIR / "unlink-two-component.json")

    assert certificate["diagram_id"] == "unlink-2"
    assert certificate["component_ids"] == ["u1", "u2"]
    assert certificate["sector_count"] == 9
    assert certificate["total_value"] == _sparse_sum([(0, QuadraticSurd(16))])


def test_certificate_json_is_stable_and_deterministic() -> None:
    first = evaluate_ordinary_kirby_color(unlink(["a", "b"], framings=[0, 1]))
    second = evaluate_ordinary_kirby_color(unlink(["a", "b"], framings=[0, 1]))

    assert first == second
    assert stable_ordinary_kirby_color_json(first) == stable_ordinary_kirby_color_json(second)
    assert json.loads(stable_ordinary_kirby_color_json(first)) == first


def test_closed_4_manifold_claim_flag_is_refused_while_sources_are_missing() -> None:
    with pytest.raises(ValueError, match="closed_4_manifold_claim=True is refused"):
        evaluate_ordinary_kirby_color(s4_diagram(), closed_4_manifold_claim=True)


def test_crossings_and_dotted_handles_are_explicitly_out_of_scope() -> None:
    with pytest.raises(NotImplementedError, match="no-crossing"):
        evaluate_ordinary_kirby_color(hopf_link())

    dotted = LinkDiagram(
        "dotted-unsupported",
        components=(Component("d", 0, dotted=True),),
    )
    with pytest.raises(NotImplementedError, match="dotted handles"):
        evaluate_ordinary_kirby_color(dotted)


def _sparse_sum(entries: list[tuple[int, QuadraticSurd]]) -> dict[str, object]:
    return {
        "kind": "Q(sqrt2)[zeta_16]_sparse_sum",
        "terms": [
            {"exponent": exponent, "coefficient": coefficient.to_jsonable()}
            for exponent, coefficient in entries
        ],
    }
