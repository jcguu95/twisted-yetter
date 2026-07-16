from experiments.scripts.build_figure21_rank2_rank3_standard_comparison_v1 import (
    generate,
)


def test_rank2_rank3_standard_comparison_records_rank2_differences():
    payload = generate()
    assert payload["status"] == (
        "PASS_RANK2_RANK3_STANDARD_COMPARISON_ALL_MATCH_PHASE_ALIGNED"
    )
    assert payload["row_count"] == 4
    assert payload["matching_row_count"] == 2
    assert payload["differing_row_count"] == 2
    assert payload["phase_aligned_matching_row_count"] == 4
    by_id = {row["realization_id"]: row for row in payload["rows"]}
    for realization_id in (
        "rank2-cyclic-z2-semion-minus",
        "rank2-cyclic-z2-semion-plus",
    ):
        diff = by_id[realization_id]["figure21_nonzero_minus_standard_distribution"]
        assert diff == {"+1+0i": -32, "-1+0i": 32}
        alignment = by_id[realization_id]["phase_alignment"]
        assert alignment["status"] == "PASS_PHASE_ALIGNED_MATCH"
        assert alignment["phase_multiplier_on_figure21_values"] == "-1+0i"
        assert alignment["aligned_minus_standard_distribution"] == {}
    for realization_id in (
        "rank3-cyclic-z3-minus",
        "rank3-cyclic-z3-plus",
    ):
        assert by_id[realization_id]["figure21_nonzero_minus_standard_distribution"] == {}
        alignment = by_id[realization_id]["phase_alignment"]
        assert alignment["status"] == "PASS_PHASE_ALIGNED_MATCH"
        assert alignment["phase_multiplier_on_figure21_values"] == "+1+0i"


def test_rank2_rank3_standard_comparison_is_not_exoticness_claim():
    payload = generate()
    assert payload["mathematical_status"] == (
        "COMPUTED_COMPARISON_NOT_H2_CERTIFIED_EXOTIC_CLAIM"
    )
    assert "This does not certify that Figure 21 is exotic." in payload["non_claims"]
    assert payload["content_hash"].startswith("sha256:")
