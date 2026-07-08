import json
from pathlib import Path

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.small_handle_examples import analyze_catalog, load_catalog


INPUT = Path("experiments/inputs/small-handle-examples/special-handle-catalog-v1.json")
ARTIFACT = Path(
    "experiments/results/small-handle-examples/special-handle-catalog-sanity-v1.json"
)


def _examples_by_id() -> dict[str, dict[str, object]]:
    return {
        example["id"]: example
        for example in analyze_catalog(load_catalog(INPUT))["examples"]
    }


def test_small_handle_catalog_all_examples_pass_algebraic_sanity() -> None:
    analysis = analyze_catalog(load_catalog(INPUT))

    assert analysis["status"] == "pass"
    assert analysis["mathematical_status"] == (
        "ALGEBRAIC_HANDLE_SANITY_NOT_LINK_EVALUATOR_OUTPUT"
    )
    assert analysis["example_count"] == 16
    assert analysis["example_status_counts"] == {"pass": 16}
    assert analysis["claim_boundary"] == {
        "not_rt_evaluation": True,
        "not_closed_4d_invariant": True,
        "not_special_dotted_projector_implementation": True,
        "purpose": (
            "fixture-level algebra for future Tham 5.11/special-dotted "
            "tests: d2, d3, H2, quotient form, and Z2 character "
            "cohomology"
        ),
    }


def test_no_three_handle_candidates_have_unimodular_augmented_sanity() -> None:
    examples = _examples_by_id()
    no_three_ids = [
        "cp2-visible-cancel-1-2",
        "cpbar-visible-cancel-1-2",
        "cp2-paired-one-handle",
        "cpbar-paired-one-handle",
        "cp2-uneven-incidence",
        "cpbar-uneven-incidence",
        "cp2-two-dotted-three-two-handles",
        "s2xs2-one-dotted-three-two-handles",
    ]

    for example_id in no_three_ids:
        example = examples[example_id]
        assert example["handle_counts"]["3"] == 0
        assert abs(example["augmented_dotted_surgery_matrix"]["determinant"]) == 1
        assert example["augmented_dotted_surgery_matrix"]["nullity"] == 0
        assert example["homology_ranks_over_Q"]["b1"] == 0
        assert example["homology_ranks_over_Q"]["b3"] == 0


def test_first_nontrivial_paired_one_handle_z2_assignments_are_quotiented_by_d2() -> None:
    example = _examples_by_id()["cp2-paired-one-handle"]
    z2 = example["z2_character_cohomology"]

    assert example["h2"]["rank"] == 1
    assert example["forms"]["q_on_h2_quotient_basis"] == [[1]]
    assert z2["coboundary_generators"] == [[1, 1]]
    assert z2["coboundaries"] == [[0, 0], [1, 1]]
    assert z2["h2_character_count"] == 2
    assert z2["cohomology_representatives"] == [
        {
            "coset_size": 2,
            "representative": [0, 0],
            "values_on_h2_quotient_basis": [0],
        },
        {
            "coset_size": 2,
            "representative": [0, 1],
            "values_on_h2_quotient_basis": [1],
        },
    ]


def test_minimal_kernel_image_example_uses_both_d2_and_d3() -> None:
    example = _examples_by_id()["cp2-kernel-image-all-handles"]
    z2 = example["z2_character_cohomology"]

    assert example["handle_counts"] == {"0": 1, "1": 1, "2": 3, "3": 1, "4": 1}
    assert example["chain_complex"]["d2_matrix_c2_to_c1"] == [[1, 1, 0]]
    assert example["h2"]["d3_relation_columns"] == [[1, -1, 0]]
    assert example["h2"]["quotient_basis_representatives"] == [[0, 0, 1]]
    assert example["h2"]["relation_radical_checks"] == [
        {
            "relation_index": 0,
            "relation_vector": [1, -1, 0],
            "pairings_against_kernel_basis": [0, 0],
            "is_radical_on_kernel": True,
        }
    ]
    assert example["forms"]["q_on_h2_quotient_basis"] == [[1]]
    assert z2["cocycle_representatives_before_quotient"] == [
        [0, 0, 0],
        [0, 0, 1],
        [1, 1, 0],
        [1, 1, 1],
    ]
    assert z2["cohomology_representatives"][1]["representative"] == [0, 0, 1]


def test_rank_two_one_dotted_candidate_has_four_z2_characters_and_hyperbolic_form() -> None:
    example = _examples_by_id()["s2xs2-one-dotted-three-two-handles"]
    z2 = example["z2_character_cohomology"]

    assert example["h2"]["rank"] == 2
    assert example["forms"]["q_on_h2_quotient_basis"] == [[0, 1], [1, 0]]
    assert z2["h2_character_count"] == 4
    assert [
        item["values_on_h2_quotient_basis"]
        for item in z2["cohomology_representatives"]
    ] == [[0, 0], [0, 1], [1, 0], [1, 1]]
    assert example["forms"]["standard_su2_2_omega_control"]["value"] == {
        "kind": "Z[zeta_16]_sparse_sum",
        "root_symbol": "zeta_16 = exp(2*pi*i/16)",
        "terms": [{"exponent": 0, "integer_coefficient": 4}],
    }


def test_checked_in_small_handle_artifact_matches_current_analysis() -> None:
    certificate = json.loads(ARTIFACT.read_text())
    validate_certificate(certificate)

    assert certificate["status"] == "pass"
    assert certificate["exact_output"] == analyze_catalog(load_catalog(INPUT))
