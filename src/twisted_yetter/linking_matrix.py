"""Exact integer matrix presentations for small Kirby examples.

This module is intentionally matrix-level only.  It records the symmetric
integer linking/intersection matrix and enough component metadata to test basis
changes before any link-diagram parser or invariant formula exists.

Basis convention
----------------
If the columns of a unimodular matrix ``P`` are the new basis vectors written
in the old basis, then the form matrix changes by

    Q_new = P^T Q_old P.

A decoration coordinate column vector ``x`` for the same homology class changes
contravariantly: ``x_old = P x_new``, so ``x_new = P^{-1} x_old``.  For the
current toy A = Z/2 decorations this inverse is reduced modulo 2.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
from numbers import Integral
from typing import Iterable, Literal, Sequence

Parity = Literal["even", "odd"]


def _as_int(value: object) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError("matrix entries and decoration coordinates must be integers")
    return int(value)


def _as_square_int_matrix(rows: Sequence[Sequence[int]]) -> tuple[tuple[int, ...], ...]:
    matrix = tuple(tuple(_as_int(value) for value in row) for row in rows)
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("matrix must be square")
    return matrix


def _check_symmetric(matrix: tuple[tuple[int, ...], ...]) -> None:
    for i, row in enumerate(matrix):
        for j in range(i + 1, len(matrix)):
            if row[j] != matrix[j][i]:
                raise ValueError("linking/intersection matrix must be symmetric")


def _identity(size: int) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(1 if i == j else 0 for j in range(size)) for i in range(size))


def _transpose(matrix: Sequence[Sequence[int]]) -> tuple[tuple[int, ...], ...]:
    if not matrix:
        return ()
    return tuple(tuple(row[i] for row in matrix) for i in range(len(matrix[0])))


def _matmul(
    left: Sequence[Sequence[int]], right: Sequence[Sequence[int]]
) -> tuple[tuple[int, ...], ...]:
    if not left:
        return ()
    width = len(right[0]) if right else 0
    return tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(len(right))) for j in range(width))
        for i in range(len(left))
    )


def _matvec(matrix: Sequence[Sequence[int]], vector: Sequence[int]) -> tuple[int, ...]:
    return tuple(sum(row[j] * vector[j] for j in range(len(vector))) for row in matrix)


def determinant(rows: Sequence[Sequence[int]]) -> int:
    """Return the exact determinant using fraction-free Bareiss elimination."""

    matrix = [list(row) for row in _as_square_int_matrix(rows)]
    size = len(matrix)
    if size == 0:
        return 1

    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        pivot_row = next(
            (row for row in range(pivot_index, size) if matrix[row][pivot_index] != 0),
            None,
        )
        if pivot_row is None:
            return 0
        if pivot_row != pivot_index:
            matrix[pivot_index], matrix[pivot_row] = matrix[pivot_row], matrix[pivot_index]
            sign *= -1

        pivot = matrix[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for col in range(pivot_index + 1, size):
                matrix[row][col] = (
                    matrix[row][col] * pivot
                    - matrix[row][pivot_index] * matrix[pivot_index][col]
                ) // previous
        previous = pivot
        for row in range(pivot_index + 1, size):
            matrix[row][pivot_index] = 0
        for col in range(pivot_index + 1, size):
            matrix[pivot_index][col] = 0

    return sign * matrix[-1][-1]


def rank(rows: Sequence[Sequence[int]]) -> int:
    """Return the exact rank over Q."""

    matrix = [[Fraction(value) for value in row] for row in rows]
    if not matrix:
        return 0

    row_count = len(matrix)
    col_count = len(matrix[0])
    pivot_row = 0
    for col in range(col_count):
        nonzero_row = next(
            (row for row in range(pivot_row, row_count) if matrix[row][col] != 0),
            None,
        )
        if nonzero_row is None:
            continue
        matrix[pivot_row], matrix[nonzero_row] = matrix[nonzero_row], matrix[pivot_row]
        pivot = matrix[pivot_row][col]
        matrix[pivot_row] = [value / pivot for value in matrix[pivot_row]]
        for row in range(row_count):
            if row != pivot_row and matrix[row][col] != 0:
                factor = matrix[row][col]
                matrix[row] = [
                    matrix[row][i] - factor * matrix[pivot_row][i] for i in range(col_count)
                ]
        pivot_row += 1
        if pivot_row == row_count:
            break
    return pivot_row


def signature(rows: Sequence[Sequence[int]]) -> tuple[int, int, int]:
    """Return ``(positive, negative, zero)`` for a symmetric matrix over Q."""

    matrix = [[Fraction(value) for value in row] for row in _as_square_int_matrix(rows)]
    _check_symmetric(tuple(tuple(int(value) for value in row) for row in rows))

    positive = 0
    negative = 0
    zero = 0

    while matrix:
        size = len(matrix)
        pivot_index = next((i for i in range(size) if matrix[i][i] != 0), None)
        if pivot_index is None:
            pair = next(
                (
                    (i, j)
                    for i in range(size)
                    for j in range(i + 1, size)
                    if matrix[i][j] != 0
                ),
                None,
            )
            if pair is None:
                zero += size
                break
            i, j = pair
            for k in range(size):
                matrix[i][k] += matrix[j][k]
            for k in range(size):
                matrix[k][i] = matrix[i][k]
            pivot_index = i

        if pivot_index != 0:
            matrix[0], matrix[pivot_index] = matrix[pivot_index], matrix[0]
            for row in matrix:
                row[0], row[pivot_index] = row[pivot_index], row[0]

        pivot = matrix[0][0]
        if pivot > 0:
            positive += 1
        else:
            negative += 1

        next_matrix: list[list[Fraction]] = []
        for i in range(1, size):
            next_row: list[Fraction] = []
            for j in range(1, size):
                next_row.append(matrix[i][j] - matrix[i][0] * matrix[0][j] / pivot)
            next_matrix.append(next_row)
        matrix = next_matrix

    return positive, negative, zero


def _inverse_unimodular(matrix: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
    size = len(matrix)
    left = [[Fraction(value) for value in row] for row in matrix]
    right = [[Fraction(value) for value in row] for row in _identity(size)]

    for col in range(size):
        pivot_row = next((row for row in range(col, size) if left[row][col] != 0), None)
        if pivot_row is None:
            raise ValueError("basis change matrix must be invertible")
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
            raise ValueError("basis change matrix must be unimodular over Z")
        inverse.append(tuple(int(value) for value in row))
    return tuple(inverse)


@dataclass(frozen=True)
class KirbyMatrixPresentation:
    """Small integer matrix presentation for Kirby-level toy computations."""

    matrix: tuple[tuple[int, ...], ...]
    component_ids: tuple[str, ...]
    orientation_labels: tuple[str, ...]
    decorations_mod2: tuple[tuple[int, ...], ...] = ()

    def __init__(
        self,
        matrix: Sequence[Sequence[int]],
        component_ids: Sequence[str] | None = None,
        orientation_labels: Sequence[str] | None = None,
        decorations_mod2: Iterable[Sequence[int]] = (),
    ) -> None:
        normalized = _as_square_int_matrix(matrix)
        _check_symmetric(normalized)
        size = len(normalized)

        ids = (
            tuple(component_ids)
            if component_ids is not None
            else tuple(f"h{i + 1}" for i in range(size))
        )
        if len(ids) != size:
            raise ValueError("component_ids length must match matrix size")

        orientations = (
            tuple(orientation_labels)
            if orientation_labels is not None
            else tuple("+" for _ in range(size))
        )
        if len(orientations) != size:
            raise ValueError("orientation_labels length must match matrix size")

        decorations = tuple(
            tuple(_as_int(value) % 2 for value in vector) for vector in decorations_mod2
        )
        if any(len(vector) != size for vector in decorations):
            raise ValueError("each mod-2 decoration vector must match matrix size")

        object.__setattr__(self, "matrix", normalized)
        object.__setattr__(self, "component_ids", ids)
        object.__setattr__(self, "orientation_labels", orientations)
        object.__setattr__(self, "decorations_mod2", decorations)

    @property
    def size(self) -> int:
        return len(self.matrix)

    @property
    def framings(self) -> tuple[int, ...]:
        return tuple(self.matrix[i][i] for i in range(self.size))

    @property
    def rank(self) -> int:
        return rank(self.matrix)

    @property
    def determinant(self) -> int:
        return determinant(self.matrix)

    @property
    def signature_triple(self) -> tuple[int, int, int]:
        return signature(self.matrix)

    @property
    def signature(self) -> int:
        positive, negative, _zero = self.signature_triple
        return positive - negative

    @property
    def parity(self) -> Parity:
        return "even" if all(frame % 2 == 0 for frame in self.framings) else "odd"

    def change_basis(
        self,
        basis_matrix: Sequence[Sequence[int]],
        component_ids: Sequence[str] | None = None,
    ) -> "KirbyMatrixPresentation":
        """Return the presentation in a new GL(n,Z) basis.

        Columns of ``basis_matrix`` are new basis vectors in old coordinates.
        Decorations are coordinate vectors, transformed by the inverse matrix
        and then reduced modulo 2.
        """

        basis = _as_square_int_matrix(basis_matrix)
        if len(basis) != self.size:
            raise ValueError("basis matrix size must match presentation size")
        if abs(determinant(basis)) != 1:
            raise ValueError("basis matrix must lie in GL(n,Z)")

        new_matrix = _matmul(_matmul(_transpose(basis), self.matrix), basis)
        inverse = _inverse_unimodular(basis)
        new_decorations = tuple(
            tuple(value % 2 for value in _matvec(inverse, vector))
            for vector in self.decorations_mod2
        )
        new_ids = tuple(component_ids) if component_ids is not None else self.component_ids
        return replace(
            self,
            matrix=new_matrix,
            component_ids=new_ids,
            decorations_mod2=new_decorations,
        )


def s4() -> KirbyMatrixPresentation:
    return KirbyMatrixPresentation([], component_ids=[])


def cp2() -> KirbyMatrixPresentation:
    return KirbyMatrixPresentation([[1]], component_ids=["cp2_h"])


def anti_cp2() -> KirbyMatrixPresentation:
    return KirbyMatrixPresentation([[-1]], component_ids=["anti_cp2_h"])


def s2x_s2() -> KirbyMatrixPresentation:
    return KirbyMatrixPresentation([[0, 1], [1, 0]], component_ids=["s2_a", "s2_b"])


def cp2_sum_anti_cp2() -> KirbyMatrixPresentation:
    return KirbyMatrixPresentation([[1, 0], [0, -1]], component_ids=["cp2_h", "anti_cp2_h"])


def cp2_sum_cp2() -> KirbyMatrixPresentation:
    return KirbyMatrixPresentation([[1, 0], [0, 1]], component_ids=["cp2_h1", "cp2_h2"])


__all__ = [
    "KirbyMatrixPresentation",
    "anti_cp2",
    "cp2",
    "cp2_sum_anti_cp2",
    "cp2_sum_cp2",
    "determinant",
    "rank",
    "s2x_s2",
    "s4",
    "signature",
]
