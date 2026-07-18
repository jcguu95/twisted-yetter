import pytest

from twisted_yetter.linking_matrix import KirbyMatrixPresentation, cp2_sum_cp2
from twisted_yetter.presentation_moves import (
    PresentationPair,
    inverse_unimodular,
    make_presentation_pair,
    small_presentation_pairs,
)


def test_small_presentation_pairs_are_valid_certificates() -> None:
    pairs = small_presentation_pairs()

    assert {pair.name for pair in pairs} == {
        "hyperbolic-shear",
        "odd-indefinite-swap",
        "odd-positive-shear",
    }

    for pair in pairs:
        pair.assert_valid()
        assert pair.metadata["node"] == "n45-presentation-pair-generator"
        assert pair.metadata["scope"] == "matrix-level basis change fixture"
        assert pair.basis_matrix
        assert pair.inverse_basis_matrix == inverse_unimodular(pair.basis_matrix)
        assert pair.target.signature_triple == pair.source.signature_triple
        assert pair.target.rank == pair.source.rank
        assert pair.target.determinant == pair.source.determinant
        assert pair.transformed_decorations_mod2() == pair.target.decorations_mod2


def test_hyperbolic_shear_records_exact_basis_and_decoration_transform() -> None:
    pair = next(pair for pair in small_presentation_pairs() if pair.name == "hyperbolic-shear")

    assert pair.source.matrix == ((0, 1), (1, 0))
    assert pair.basis_matrix == ((1, 1), (0, 1))
    assert pair.inverse_basis_matrix == ((1, -1), (0, 1))
    assert pair.decoration_transform_mod2 == ((1, 1), (0, 1))
    assert pair.target.matrix == ((0, 1), (1, 2))
    assert pair.target.component_ids == ("a", "a+b")
    assert pair.source.decorations_mod2 == ((1, 0), (0, 1), (1, 1))
    assert pair.target.decorations_mod2 == ((1, 0), (1, 1), (0, 1))


def test_make_presentation_pair_uses_change_basis_convention() -> None:
    source = KirbyMatrixPresentation(
        [[1, 0], [0, 1]],
        component_ids=["u", "v"],
        decorations_mod2=[(1, 0), (0, 1)],
    )

    pair = make_presentation_pair(
        "positive-shear",
        source,
        [[1, 1], [0, 1]],
        target_component_ids=["u", "u+v"],
        metadata={"move": "test shear"},
    )

    assert pair.target == source.change_basis([[1, 1], [0, 1]], component_ids=["u", "u+v"])
    assert pair.metadata["move"] == "test shear"


def test_non_unimodular_basis_is_rejected() -> None:
    with pytest.raises(ValueError, match=r"GL\(n,Z\)"):
        make_presentation_pair("bad", cp2_sum_cp2(), [[2, 0], [0, 1]])


def test_assert_valid_detects_tampered_decoration_transform() -> None:
    pair = next(pair for pair in small_presentation_pairs() if pair.name == "odd-positive-shear")
    tampered = PresentationPair(
        name=pair.name,
        source=pair.source,
        target=pair.target,
        basis_matrix=pair.basis_matrix,
        inverse_basis_matrix=pair.inverse_basis_matrix,
        decoration_transform_mod2=((1, 0), (0, 1)),
        character_transform_mod2=pair.character_transform_mod2,
        metadata=pair.metadata,
    )

    with pytest.raises(ValueError, match="decoration transform"):
        tampered.assert_valid()


def test_character_transform_is_dual_and_preserves_every_mod2_pairing() -> None:
    pair = next(
        pair for pair in small_presentation_pairs()
        if pair.name == "hyperbolic-shear"
    )

    assert pair.character_transform_mod2 == ((1, 0), (1, 1))
    for character in ((0, 0), (1, 0), (0, 1), (1, 1)):
        for decoration in ((0, 0), (1, 0), (0, 1), (1, 1)):
            pair.assert_pairing_preserved(character, decoration)


def test_tampered_character_transform_is_rejected() -> None:
    pair = next(
        pair for pair in small_presentation_pairs()
        if pair.name == "odd-positive-shear"
    )
    tampered = PresentationPair(
        name=pair.name,
        source=pair.source,
        target=pair.target,
        basis_matrix=pair.basis_matrix,
        inverse_basis_matrix=pair.inverse_basis_matrix,
        decoration_transform_mod2=pair.decoration_transform_mod2,
        character_transform_mod2=((1, 0), (0, 1)),
        metadata=pair.metadata,
    )

    with pytest.raises(ValueError, match="character transform"):
        tampered.assert_valid()
