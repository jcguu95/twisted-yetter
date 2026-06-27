import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.link_diagram import (
    Component,
    Crossing,
    LinkDiagram,
    StrandRef,
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
    evaluate_su2_level2_ordinary_kirby_color,
    load_fixture_certificate,
    omega_coefficients,
    stable_ordinary_kirby_color_json,
)
from twisted_yetter.su2_level2 import SQRT2, QuadraticSurd


TOY_FIXTURE_DIR = Path("experiments/inputs/toy-diagrams")
ORDINARY_KIRBY_ARTIFACT = Path(
    "experiments/results/ordinary-kirby-color/su2-level2-local-convention.json"
)


def test_omega_coefficients_are_experimental_quantum_dimensions() -> None:
    assert omega_coefficients() == {
        "0": QuadraticSurd(1),
        "1": SQRT2,
        "2": QuadraticSurd(1),
    }


def test_empty_fixture_certificate_records_one_and_source_slots() -> None:
    certificate = evaluate_su2_level2_ordinary_kirby_color(s4_diagram())

    assert certificate["schema"] == ORDINARY_KIRBY_COLOR_SCHEMA
    assert certificate["status"] == "pass"
    assert certificate["kirby_color_convention"] == KIRBY_COLOR_CONVENTION
    assert certificate["kirby_color_formula"] == "omega = sum_i d_i X_i"
    assert certificate["sector_count"] == 1
    assert certificate["sectors"][0]["core_supported_kind"] == "empty"
    assert certificate["total_value"] == _sparse_sum([(0, QuadraticSurd(1))])
    assert certificate["source_status_by_slot"] == SOURCE_STATUS_BY_SLOT
    assert set(certificate["source_status_by_slot"].values()) == {"SOURCE NEEDED"}
    assert certificate["handle_scope"] == HANDLE_SCOPE
    assert certificate["normalization_status"] == NORMALIZATION_STATUS
    assert certificate["claim_level"] == CLAIM_LEVEL
    assert certificate["closed_4_manifold_claim_allowed"] is False
    assert "closed 4-manifold invariant" in certificate["claim_boundary"]["not_scope"]


def test_zero_framed_unknot_sums_to_global_dimension_without_normalization_claim() -> None:
    certificate = evaluate_su2_level2_ordinary_kirby_color(unknot("u", framing=0))

    assert certificate["sector_count"] == 3
    assert certificate["total_value"] == _sparse_sum([(0, QuadraticSurd(4))])
    assert all(sector["core_supported_kind"] == "split_no_crossing" for sector in certificate["sectors"])
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


def test_hopf_fixture_expands_all_sectors_through_restricted_core() -> None:
    certificate = load_fixture_certificate(TOY_FIXTURE_DIR / "hopf-link.json")

    assert certificate["status"] == "pass"
    assert certificate["diagram_id"] == "hopf-linking-1"
    assert certificate["crossing_count"] == 2
    assert certificate["sector_count"] == 9
    assert certificate["total_value"] == _sparse_sum([(0, QuadraticSurd(4))])
    assert {
        sector["core_supported_kind"] for sector in certificate["sectors"]
    } == {"positive_hopf"}
    zero_hopf_sector = certificate["sectors"][4]
    assert zero_hopf_sector["labels_by_component"] == {"h1": "1", "h2": "1"}
    assert zero_hopf_sector["term"]["coefficient"] == QuadraticSurd(0).to_jsonable()


def test_certificate_json_is_stable_and_deterministic() -> None:
    first = evaluate_su2_level2_ordinary_kirby_color(unlink(["a", "b"], framings=[0, 1]))
    second = evaluate_su2_level2_ordinary_kirby_color(unlink(["a", "b"], framings=[0, 1]))

    assert first == second
    assert stable_ordinary_kirby_color_json(first) == stable_ordinary_kirby_color_json(second)
    assert json.loads(stable_ordinary_kirby_color_json(first)) == first


def test_closed_4_manifold_claim_flag_is_refused_while_sources_are_missing() -> None:
    with pytest.raises(ValueError, match="closed_4_manifold_claim=True is refused"):
        evaluate_su2_level2_ordinary_kirby_color(
            s4_diagram(),
            closed_4_manifold_claim=True,
        )


def test_backward_compatible_alias_uses_public_entry_point() -> None:
    assert evaluate_ordinary_kirby_color(s4_diagram()) == (
        evaluate_su2_level2_ordinary_kirby_color(s4_diagram())
    )


def test_dotted_handles_produce_structured_sector_blockers() -> None:
    dotted = LinkDiagram("dotted-unsupported", components=(Component("d", 0, dotted=True),))

    certificate = evaluate_su2_level2_ordinary_kirby_color(dotted)

    assert certificate["status"] == "blocked"
    assert certificate["sector_count"] == 3
    assert certificate["blocker"]["reason_id"] == "restricted-core-sector-blocked"
    assert certificate["blocker"]["blocked_sector_count"] == 3
    assert {
        sector["core_blocker"]["reason_id"] for sector in certificate["sectors"]
    } == {"dotted-components-unsupported"}


def test_general_unsupported_crossings_produce_structured_sector_blockers() -> None:
    unsupported = LinkDiagram(
        "three-component-crossing-not-planar-evaluable",
        components=(Component("a", 0), Component("b", 0), Component("c", 0)),
        crossings=(
            Crossing("x1", 1, StrandRef("a", "a1"), StrandRef("b", "b1")),
            Crossing("x2", 1, StrandRef("a", "a2"), StrandRef("b", "b2")),
        ),
    )

    certificate = evaluate_su2_level2_ordinary_kirby_color(unsupported)

    assert certificate["status"] == "blocked"
    assert certificate["sector_count"] == 27
    assert certificate["total_value"] == _sparse_sum([])
    assert certificate["blocker"]["blocked_sector_count"] == 27
    assert {
        sector["core_blocker"]["reason_id"] for sector in certificate["sectors"]
    } == {"general-crossing-diagram-unsupported"}


def test_official_local_convention_artifact_records_supported_and_blocked_cases() -> None:
    artifact = json.loads(ORDINARY_KIRBY_ARTIFACT.read_text())
    validate_certificate(artifact)

    exact_output = artifact["exact_output"]
    assert exact_output["node_id"] == "n22-ordinary-kirby-color-implementation"
    assert exact_output["claim_level"] == "experimental/local-convention"
    assert exact_output["result_count"] == 7
    assert exact_output["result_statuses"] == [
        "pass",
        "pass",
        "pass",
        "pass",
        "pass",
        "blocked",
        "blocked",
    ]
    assert exact_output["claim_boundary"] == {
        "not_closed_4d_invariant": True,
        "not_surgery_normalized": True,
        "not_twisted_yetter": True,
        "not_general_planar_rt_evaluator": True,
    }


def _sparse_sum(entries: list[tuple[int, QuadraticSurd]]) -> dict[str, object]:
    return {
        "kind": "Q(sqrt2)[zeta_16]_sparse_sum",
        "terms": [
            {"exponent": exponent, "coefficient": coefficient.to_jsonable()}
            for exponent, coefficient in entries
        ],
    }
