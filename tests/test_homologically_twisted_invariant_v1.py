from __future__ import annotations

from copy import deepcopy
from fractions import Fraction
from pathlib import Path

import pytest

from twisted_yetter.homologically_twisted_invariant_v1 import (
    ALPHA_DENOMINATOR,
    PROOF_OBJECT_KIND,
    canonical_hash,
    build_invariant_runtime_fixture,
    validate_invariant_runtime,
)
from twisted_yetter.kirby_completeness_v1 import SPECIAL_MOVE_KINDS


ROOT = Path(__file__).resolve().parents[1]
LEAN_SOURCE = (
    ROOT
    / "lean/TwistedYetter/Kirby/"
    "HomologicallyTwistedInvariant.lean"
)


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_complete_runtime_fixture_validates_all_moves_and_alphas() -> None:
    fixture = build_invariant_runtime_fixture()
    validate_invariant_runtime(fixture)

    assert len(fixture["steps"]) == len(SPECIAL_MOVE_KINDS)
    assert fixture["movie_result"]["checked_step_alpha_count"] == (
        len(SPECIAL_MOVE_KINDS) * ALPHA_DENOMINATOR
    )
    assert fixture["movie_result"]["directed_constructor_coverage"] == list(
        SPECIAL_MOVE_KINDS
    )


def test_every_step_uses_the_exact_r7_r8_or_r9_proof_kind() -> None:
    fixture = build_invariant_runtime_fixture()

    for step in fixture["steps"]:
        assert step["local_proof_binding"]["proof_object_kind"] == (
            PROOF_OBJECT_KIND[step["topology_kind"]]
        )
        assert step["local_proof_binding"][
            "realizes_exact_topology_move"
        ] is True


def test_every_local_normalized_value_and_marked_pair_value_agrees() -> None:
    fixture = build_invariant_runtime_fixture()

    for step in fixture["steps"]:
        for case in step["alpha_cases"]:
            assert case["source_state"]["normalized_value"] == (
                case["target_state"]["normalized_value"]
            )
    for case in fixture["marked_pair_system"]["cases"]:
        assert case["chosen_value"] == case["target_value"]


def test_stale_content_hash_and_mutable_alias_fail_closed() -> None:
    fixture = build_invariant_runtime_fixture()
    fixture["runtime_id"] = "changed-without-rehash"
    with pytest.raises(ValueError, match="stale"):
        validate_invariant_runtime(fixture)

    alias = build_invariant_runtime_fixture()
    alias["latest_alias"] = "current"
    rehash(alias)
    with pytest.raises(ValueError, match="schema mismatch"):
        validate_invariant_runtime(alias)


def test_mixed_category_snapshot_or_uncertified_scalarization_fails() -> None:
    mixed = build_invariant_runtime_fixture()
    mixed["category"]["single_snapshot_coherent"] = False
    rehash(mixed)
    with pytest.raises(ValueError, match="one-snapshot coherent"):
        validate_invariant_runtime(mixed)

    scalar = build_invariant_runtime_fixture()
    scalar["category"]["scalarization_matches_ground_field"] = False
    rehash(scalar)
    with pytest.raises(ValueError, match="scalarization"):
        validate_invariant_runtime(scalar)


def test_wrong_proof_object_kind_fails_closed() -> None:
    fixture = build_invariant_runtime_fixture()
    binding = fixture["steps"][1]["local_proof_binding"]
    binding["proof_object_kind"] = PROOF_OBJECT_KIND["two_over_one"]
    binding_body = dict(binding)
    binding_body.pop("graphical_certificate_hash")
    from twisted_yetter.homologically_twisted_invariant_v1 import (
        _sha256_payload,
    )

    binding["graphical_certificate_hash"] = _sha256_payload(binding_body)
    rehash(fixture)
    with pytest.raises(ValueError, match="wrong proof object kind"):
        validate_invariant_runtime(fixture)


def test_slide_kind_orientation_and_move_id_mismatches_fail_closed() -> None:
    kind = build_invariant_runtime_fixture()
    binding = kind["steps"][1]["local_proof_binding"]
    binding["graphical_slide_kind"] = "two_over_one"
    _rehash_binding(binding)
    rehash(kind)
    with pytest.raises(ValueError, match="graphical kind"):
        validate_invariant_runtime(kind)

    orientation = build_invariant_runtime_fixture()
    binding = orientation["steps"][1]["local_proof_binding"]
    binding["graphical_orientation"] = "negative"
    _rehash_binding(binding)
    rehash(orientation)
    with pytest.raises(ValueError, match="graphical orientation"):
        validate_invariant_runtime(orientation)

    move_id = build_invariant_runtime_fixture()
    binding = move_id["steps"][1]["local_proof_binding"]
    binding["move_id"] = "proof-for-a-different-step"
    _rehash_binding(binding)
    rehash(move_id)
    with pytest.raises(ValueError, match="proof move ID"):
        validate_invariant_runtime(move_id)


def test_stale_graphical_endpoint_hash_fails_closed() -> None:
    fixture = build_invariant_runtime_fixture()
    binding = fixture["steps"][2]["local_proof_binding"]
    binding["source_presentation_hash"] = (
        "sha256:" + "1" * 64
    )
    _rehash_binding(binding)
    rehash(fixture)
    with pytest.raises(ValueError, match="proof source hash"):
        validate_invariant_runtime(fixture)


def test_handwritten_target_alpha_fails_closed() -> None:
    fixture = build_invariant_runtime_fixture()
    fixture["steps"][1]["alpha_cases"][1][
        "target_alpha_derived"
    ] = [1, 1]
    rehash(fixture)
    with pytest.raises(ValueError, match="target alpha handwritten"):
        validate_invariant_runtime(fixture)


def test_wrong_signed_denominator_fails_closed() -> None:
    fixture = build_invariant_runtime_fixture()
    fixture["steps"][0]["alpha_cases"][0]["source_state"][
        "denominator"
    ] = {"numerator": 1, "denominator": 1}
    rehash(fixture)
    with pytest.raises(ValueError, match="signed-exponent denominator"):
        validate_invariant_runtime(fixture)


def test_wrong_cancellation_factor_or_direction_fails_closed() -> None:
    fixture = build_invariant_runtime_fixture()
    birth_case = fixture["steps"][4]["alpha_cases"][0]
    birth_case["target_state"]["raw_numerator"] = (
        birth_case["source_state"]["raw_numerator"]
    )
    raw = _read_fraction(birth_case["target_state"]["raw_numerator"])
    denominator = _read_fraction(
        birth_case["target_state"]["denominator"]
    )
    birth_case["target_state"]["normalized_value"] = _fraction_json(
        raw / denominator
    )
    rehash(fixture)
    with pytest.raises(ValueError, match="raw factor/direction"):
        validate_invariant_runtime(fixture)


def test_incomplete_alpha_denominator_fails_closed() -> None:
    fixture = build_invariant_runtime_fixture()
    fixture["steps"][0]["alpha_cases"].pop()
    rehash(fixture)
    with pytest.raises(ValueError, match="alpha denominator incomplete"):
        validate_invariant_runtime(fixture)


def test_direct_equality_or_crane_yetter_injection_fails_closed() -> None:
    equality = build_invariant_runtime_fixture()
    equality["steps"][0]["local_proof_binding"][
        "normalized_equality_input"
    ] = "left=right"
    _rehash_binding(equality["steps"][0]["local_proof_binding"])
    rehash(equality)
    with pytest.raises(ValueError, match="forbidden equality"):
        validate_invariant_runtime(equality)

    identification = build_invariant_runtime_fixture()
    identification["claim_boundary"][
        "crane_yetter_identification"
    ] = True
    rehash(identification)
    with pytest.raises(ValueError, match="forbidden equality or claim"):
        validate_invariant_runtime(identification)


def test_marked_target_coordinate_and_nonclaims_fail_closed() -> None:
    target = build_invariant_runtime_fixture()
    target["marked_pair_system"]["cases"][1][
        "target_coordinate_derived"
    ][0] ^= 1
    rehash(target)
    with pytest.raises(ValueError, match="target coordinate was handwritten"):
        validate_invariant_runtime(target)

    nonclaim = build_invariant_runtime_fixture()
    nonclaim["claim_boundary"]["explicit_non_claims"] = [
        item
        for item in nonclaim["claim_boundary"]["explicit_non_claims"]
        if "Crane-Yetter" not in item
    ]
    rehash(nonclaim)
    with pytest.raises(ValueError, match="missing non-claim"):
        validate_invariant_runtime(nonclaim)


def test_lean_source_has_closed_bridge_and_no_equality_escape_hatch() -> None:
    source = LEAN_SOURCE.read_text()
    bridge = source.split(
        "inductive EvaluatedTableTwoStep", 1
    )[1].split("namespace EvaluatedTableTwoStep", 1)[0]

    for constructor in (
        "framedIsotopy",
        "oneOverOne",
        "twoOverOne",
        "twoOverTwo",
        "oneTwoBirth",
        "oneTwoDeath",
        "twoThreeBirth",
        "twoThreeDeath",
    ):
        assert f"| {constructor}" in bridge
    assert "fromEquality" not in bridge
    assert "normalizedEquality" not in bridge
    assert "finalInvariant" not in source
    assert "craneYetterIdentification" not in source
    assert "graphical_kind_sound" in bridge
    assert "graphical_orientation_sound" in bridge
    assert "marked_transport_sound" in source


def _rehash_binding(binding: dict[str, object]) -> None:
    from twisted_yetter.homologically_twisted_invariant_v1 import (
        _sha256_payload,
    )

    body = dict(binding)
    body.pop("graphical_certificate_hash", None)
    binding["graphical_certificate_hash"] = _sha256_payload(body)


def _read_fraction(value: dict[str, int]) -> Fraction:
    return Fraction(value["numerator"], value["denominator"])


def _fraction_json(value: Fraction) -> dict[str, int]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
    }
