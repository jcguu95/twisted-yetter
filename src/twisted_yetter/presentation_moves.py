"""Matrix-level equivalent presentation fixtures.

This module records small GL(n,Z) basis changes for Kirby matrix
presentations.  It is deliberately not a link-diagram handle-slide parser and
does not evaluate any invariant.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from numbers import Integral
from typing import Mapping, Sequence

from twisted_yetter.linking_matrix import (
    KirbyMatrixPresentation,
    cp2_sum_anti_cp2,
    cp2_sum_cp2,
    determinant,
    s2x_s2,
)


def _as_int(value: object) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError("basis matrix entries must be integers")
    return int(value)


def _as_square_int_matrix(rows: Sequence[Sequence[int]]) -> tuple[tuple[int, ...], ...]:
    matrix = tuple(tuple(_as_int(value) for value in row) for row in rows)
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("basis matrix must be square")
    return matrix


def _identity(size: int) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(1 if i == j else 0 for j in range(size)) for i in range(size))


def inverse_unimodular(
    matrix: Sequence[Sequence[int]],
) -> tuple[tuple[int, ...], ...]:
    """Return the exact integer inverse of a GL(n,Z) matrix."""

    basis = _as_square_int_matrix(matrix)
    size = len(basis)
    if abs(determinant(basis)) != 1:
        raise ValueError("basis matrix must lie in GL(n,Z)")

    left = [[Fraction(value) for value in row] for row in basis]
    right = [[Fraction(value) for value in row] for row in _identity(size)]

    for col in range(size):
        pivot_row = next((row for row in range(col, size) if left[row][col] != 0), None)
        if pivot_row is None:
            raise ValueError("basis matrix must be invertible")
        if pivot_row != col:
            left[col], left[pivot_row] = left[pivot_row], left[col]
            right[col], right[pivot_row] = right[pivot_row], right[col]
        pivot = left[col][col]
        left[col] = [value / pivot for value in left[col]]
        right[col] = [value / pivot for value in right[col]]
        for row in range(size):
            if row != col and left[row][col] != 0:
                factor = left[row][col]
                left[row] = [left[row][i] - factor * left[col][i] for i in range(size)]
                right[row] = [right[row][i] - factor * right[col][i] for i in range(size)]

    inverse: list[tuple[int, ...]] = []
    for row in right:
        if any(value.denominator != 1 for value in row):
            raise ValueError("basis matrix must be unimodular over Z")
        inverse.append(tuple(int(value) for value in row))
    return tuple(inverse)


def _matrix_mod2(matrix: Sequence[Sequence[int]]) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(value % 2 for value in row) for row in matrix)


def _transpose(
    matrix: Sequence[Sequence[int]],
) -> tuple[tuple[int, ...], ...]:
    square = _as_square_int_matrix(matrix)
    return tuple(
        tuple(square[row][col] for row in range(len(square)))
        for col in range(len(square))
    )


def _matvec_mod2(
    matrix: Sequence[Sequence[int]], vector: Sequence[int]
) -> tuple[int, ...]:
    return tuple(sum(row[j] * vector[j] for j in range(len(vector))) % 2 for row in matrix)


@dataclass(frozen=True)
class PresentationPair:
    """Certificate for two equivalent matrix presentations.

    ``basis_matrix`` follows ``KirbyMatrixPresentation.change_basis``:
    columns are the new basis vectors written in the source basis.  Decoration
    coordinates transform by ``basis_matrix^{-1}``, reduced modulo 2.
    """

    name: str
    source: KirbyMatrixPresentation
    target: KirbyMatrixPresentation
    basis_matrix: tuple[tuple[int, ...], ...]
    inverse_basis_matrix: tuple[tuple[int, ...], ...]
    decoration_transform_mod2: tuple[tuple[int, ...], ...]
    character_transform_mod2: tuple[tuple[int, ...], ...]
    metadata: Mapping[str, str]

    def transformed_decorations_mod2(self) -> tuple[tuple[int, ...], ...]:
        """Return source decorations transformed into the target basis."""

        return tuple(
            _matvec_mod2(self.decoration_transform_mod2, vector)
            for vector in self.source.decorations_mod2
        )

    def transformed_character_mod2(
        self, character: Sequence[int]
    ) -> tuple[int, ...]:
        """Return source character coordinates in the target dual basis."""

        if len(character) != self.source.size:
            raise ValueError("character length must match presentation size")
        return _matvec_mod2(self.character_transform_mod2, character)

    @staticmethod
    def pairing_mod2(character: Sequence[int], decoration: Sequence[int]) -> int:
        if len(character) != len(decoration):
            raise ValueError("character and decoration lengths must match")
        return sum(
            int(character[index]) * int(decoration[index])
            for index in range(len(character))
        ) % 2

    def assert_pairing_preserved(
        self, character: Sequence[int], decoration: Sequence[int]
    ) -> None:
        """Check the class/character dual transforms preserve evaluation."""

        if len(decoration) != self.source.size:
            raise ValueError("decoration length must match presentation size")
        source_pairing = self.pairing_mod2(character, decoration)
        target_pairing = self.pairing_mod2(
            self.transformed_character_mod2(character),
            _matvec_mod2(self.decoration_transform_mod2, decoration),
        )
        if target_pairing != source_pairing:
            raise ValueError("class/character pairing changed under basis transport")

    def assert_valid(self) -> None:
        """Raise if the recorded pair is not a machine-checkable equivalence."""

        if len(self.basis_matrix) != self.source.size:
            raise ValueError("basis matrix size must match source presentation")
        if abs(determinant(self.basis_matrix)) != 1:
            raise ValueError("basis matrix must lie in GL(n,Z)")

        expected_inverse = inverse_unimodular(self.basis_matrix)
        if self.inverse_basis_matrix != expected_inverse:
            raise ValueError("recorded inverse basis matrix is incorrect")
        if self.decoration_transform_mod2 != _matrix_mod2(expected_inverse):
            raise ValueError("recorded decoration transform must be inverse basis mod 2")
        expected_character_transform = _matrix_mod2(_transpose(self.basis_matrix))
        if self.character_transform_mod2 != expected_character_transform:
            raise ValueError(
                "recorded character transform must be transpose basis mod 2"
            )

        expected_target = self.source.change_basis(
            self.basis_matrix,
            component_ids=self.target.component_ids,
        )
        if self.target.matrix != expected_target.matrix:
            raise ValueError("target matrix is not the recorded basis change")
        if self.target.decorations_mod2 != expected_target.decorations_mod2:
            raise ValueError("target decorations do not match recorded basis change")
        if self.target.signature_triple != self.source.signature_triple:
            raise ValueError("intersection form signature changed")
        if self.target.rank != self.source.rank:
            raise ValueError("intersection form rank changed")
        if self.target.determinant != self.source.determinant:
            raise ValueError("intersection form determinant changed")

        for character_bits in range(1 << self.source.size):
            character = tuple(
                (character_bits >> index) & 1
                for index in range(self.source.size)
            )
            for decoration_bits in range(1 << self.source.size):
                decoration = tuple(
                    (decoration_bits >> index) & 1
                    for index in range(self.source.size)
                )
                self.assert_pairing_preserved(character, decoration)


def make_presentation_pair(
    name: str,
    source: KirbyMatrixPresentation,
    basis_matrix: Sequence[Sequence[int]],
    *,
    target_component_ids: Sequence[str] | None = None,
    metadata: Mapping[str, str] | None = None,
) -> PresentationPair:
    """Build and validate a matrix-level presentation-pair certificate."""

    basis = _as_square_int_matrix(basis_matrix)
    inverse = inverse_unimodular(basis)
    target = source.change_basis(basis, component_ids=target_component_ids)
    pair = PresentationPair(
        name=name,
        source=source,
        target=target,
        basis_matrix=basis,
        inverse_basis_matrix=inverse,
        decoration_transform_mod2=_matrix_mod2(inverse),
        character_transform_mod2=_matrix_mod2(_transpose(basis)),
        metadata={
            "node": "n45-presentation-pair-generator",
            "scope": "matrix-level basis change fixture",
            **dict(metadata or {}),
        },
    )
    pair.assert_valid()
    return pair


def small_presentation_pairs() -> tuple[PresentationPair, ...]:
    """Return small equivalent presentation fixtures for downstream gates."""

    hyperbolic = KirbyMatrixPresentation(
        s2x_s2().matrix,
        component_ids=["a", "b"],
        decorations_mod2=[(1, 0), (0, 1), (1, 1)],
    )
    odd_indefinite = KirbyMatrixPresentation(
        cp2_sum_anti_cp2().matrix,
        component_ids=["plus", "minus"],
        decorations_mod2=[(1, 0), (0, 1), (1, 1)],
    )
    odd_positive = KirbyMatrixPresentation(
        cp2_sum_cp2().matrix,
        component_ids=["x", "y"],
        decorations_mod2=[(1, 0), (0, 1), (1, 1)],
    )

    return (
        make_presentation_pair(
            "hyperbolic-shear",
            hyperbolic,
            [[1, 1], [0, 1]],
            target_component_ids=["a", "a+b"],
            metadata={"move": "elementary shear", "source_form": "S2xS2 hyperbolic"},
        ),
        make_presentation_pair(
            "odd-indefinite-swap",
            odd_indefinite,
            [[0, 1], [1, 0]],
            target_component_ids=["minus", "plus"],
            metadata={"move": "basis swap", "source_form": "CP2#anti-CP2"},
        ),
        make_presentation_pair(
            "odd-positive-shear",
            odd_positive,
            [[1, 1], [0, 1]],
            target_component_ids=["x", "x+y"],
            metadata={"move": "elementary shear", "source_form": "CP2#CP2"},
        ),
    )


__all__ = [
    "PresentationPair",
    "inverse_unimodular",
    "make_presentation_pair",
    "small_presentation_pairs",
]
