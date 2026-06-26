import pytest

from twisted_yetter.linking_matrix import (
    KirbyMatrixPresentation,
    anti_cp2,
    cp2,
    cp2_sum_anti_cp2,
    cp2_sum_cp2,
    s2x_s2,
    s4,
)


@pytest.mark.parametrize(
    ("presentation", "expected"),
    [
        (s4(), (0, 1, (0, 0, 0), 0, "even")),
        (cp2(), (1, 1, (1, 0, 0), 1, "odd")),
        (anti_cp2(), (1, -1, (0, 1, 0), -1, "odd")),
        (s2x_s2(), (2, -1, (1, 1, 0), 0, "even")),
        (cp2_sum_anti_cp2(), (2, -1, (1, 1, 0), 0, "odd")),
        (cp2_sum_cp2(), (2, 1, (2, 0, 0), 2, "odd")),
    ],
)
def test_standard_small_presentations_are_exact(
    presentation: KirbyMatrixPresentation,
    expected: tuple[int, int, tuple[int, int, int], int, str],
) -> None:
    expected_rank, expected_det, expected_sig_triple, expected_sig, expected_parity = expected

    assert presentation.rank == expected_rank
    assert presentation.determinant == expected_det
    assert presentation.signature_triple == expected_sig_triple
    assert presentation.signature == expected_sig
    assert presentation.parity == expected_parity


def test_component_metadata_and_framings_are_recorded() -> None:
    presentation = KirbyMatrixPresentation(
        [[2, -1], [-1, 0]],
        component_ids=["left", "right"],
        orientation_labels=["+", "-"],
        decorations_mod2=[(1, 0), (0, 1)],
    )

    assert presentation.component_ids == ("left", "right")
    assert presentation.orientation_labels == ("+", "-")
    assert presentation.framings == (2, 0)
    assert presentation.decorations_mod2 == ((1, 0), (0, 1))


def test_basis_change_uses_column_new_basis_convention() -> None:
    presentation = KirbyMatrixPresentation(
        [[0, 1], [1, 0]],
        component_ids=["a", "b"],
        decorations_mod2=[(1, 0), (0, 1), (1, 1)],
    )

    changed = presentation.change_basis([[1, 1], [0, 1]], component_ids=["a", "a+b"])

    assert changed.matrix == ((0, 1), (1, 2))
    assert changed.component_ids == ("a", "a+b")
    assert changed.rank == presentation.rank
    assert changed.determinant == presentation.determinant
    assert changed.signature_triple == presentation.signature_triple
    assert changed.decorations_mod2 == ((1, 0), (1, 1), (0, 1))


def test_basis_change_requires_gl_n_z() -> None:
    presentation = cp2_sum_cp2()

    with pytest.raises(ValueError, match=r"GL\(n,Z\)"):
        presentation.change_basis([[2, 0], [0, 1]])


def test_rejects_non_symmetric_or_mismatched_data() -> None:
    with pytest.raises(ValueError, match="symmetric"):
        KirbyMatrixPresentation([[0, 1], [0, 0]])

    with pytest.raises(TypeError, match="integers"):
        KirbyMatrixPresentation([[1.5]])

    with pytest.raises(ValueError, match="component_ids"):
        KirbyMatrixPresentation([[1]], component_ids=["x", "y"])

    with pytest.raises(ValueError, match="decoration"):
        KirbyMatrixPresentation([[1]], decorations_mod2=[(1, 0)])
