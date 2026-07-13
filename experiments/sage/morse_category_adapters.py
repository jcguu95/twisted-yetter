"""Category adapters for the native Morse fusion-tree evaluator.

Adapters wrap the repository's already calibrated F/R backends.  This keeps
the Morse engine independent of category names and, importantly, preserves
fusion multiplicity data for Drinfeld-double categories.

These adapters remain experimental outside explicitly recorded controls.
Loaded payloads whose fusion spaces use Frobenius-normalized SVD intertwiners
are converted to the corresponding orthonormal path basis before use.
"""

from __future__ import annotations

from functools import lru_cache
import math
import numpy as np


def _inverse(matrix):
    return np.linalg.inv(np.asarray(matrix, dtype=np.complex128))


def _cost_profile(f_blocks, r_blocks):
    f_nnz = [np.count_nonzero(np.abs(block) > 1e-14) for block in f_blocks]
    r_nnz = [np.count_nonzero(np.abs(block) > 1e-14) for block in r_blocks]
    return {
        "f": float(sum(f_nnz) / len(f_nnz)) if f_nnz else 1.0,
        "r": float(sum(r_nnz) / len(r_nnz)) if r_nnz else 1.0,
        "source": "mean nonzero entries in loaded local F/R blocks",
    }


class BaseMorseCategoryAdapter:
    # The adapters below expose F/R data in the evaluator's orthonormal path
    # basis.  Vacuum projection must fail closed for adapters that do not make
    # this convention explicit.
    path_basis_is_orthonormal = True

    def fusion_multiplicity(self, left, right, output) -> int:
        return next(
            (int(mult) for target, mult in self.fusion_outputs(left, right) if target == output),
            0,
        )

    @lru_cache(maxsize=None)
    def dual(self, label):
        candidates = [
            other
            for other in self.labels
            if self.fusion_multiplicity(label, other, self.unit)
        ]
        if len(candidates) != 1:
            raise ValueError(f"simple object {label!r} has non-unique dual candidates {candidates!r}")
        return candidates[0]

    @lru_cache(maxsize=None)
    def reverse_bend(self, label):
        """Gauge correction for a reversed coevaluation of a simple object."""

        dual = self.dual(label)
        block = self.f_block(label, dual, label, label)
        left = (self.unit, 0, 0)
        right = (self.unit, 0, 0)
        coefficient = complex(
            block["right_to_left"][block["left_index"][left], block["right_index"][right]]
        )
        mu = complex(self.dimension(label)) * coefficient
        if abs(mu) < 1e-12:
            raise ValueError(f"vanishing pivotal bend coefficient for {label!r}")
        return 1.0 / mu


class SU2KMorseAdapter(BaseMorseCategoryAdapter):
    """Adapter for ``SU2KBraidEvaluator`` at any supported level."""

    def __init__(self, evaluator):
        self.backend = evaluator
        self.labels = tuple(evaluator.labels)
        self.unit = 0

    def dimension(self, label):
        return complex(self.backend.dimension(label)).real

    def twist(self, label):
        return complex(self.backend.twist(label))

    def fusion_outputs(self, left, right):
        return tuple((target, 1) for target in self.backend.fusion_outputs(left, right))

    @lru_cache(maxsize=None)
    def f_block(self, a, b, c, d):
        left_basis = tuple(
            (x, 0, 0)
            for x in self.backend.fusion_outputs(a, b)
            if self.backend.admissible(x, c, d)
        )
        right_basis = tuple(
            (y, 0, 0)
            for y in self.backend.fusion_outputs(b, c)
            if self.backend.admissible(a, y, d)
        )
        matrix = np.array(
            [
                [complex(self.backend.f_symbol(a, b, c, d, x[0], y[0])) for y in right_basis]
                for x in left_basis
            ],
            dtype=np.complex128,
        )
        return {
            "left_basis": left_basis,
            "right_basis": right_basis,
            "left_index": {basis: index for index, basis in enumerate(left_basis)},
            "right_index": {basis: index for index, basis in enumerate(right_basis)},
            "right_to_left": matrix,
            "left_to_right": _inverse(matrix),
        }

    def r_matrix(self, a, b, c, positive):
        return np.array([[complex(self.backend.r_symbol(a, b, c, positive))]], dtype=np.complex128)

    def character(self, character_label, simple_label):
        return complex(self.backend.character(character_label, simple_label))

    def cost_profile(self):
        f_blocks = [self.f_block(a, b, c, d)["right_to_left"] for a in self.labels for b in self.labels for c in self.labels for d in self.labels if any(
            self.fusion_multiplicity(x, c, d) for x, _ in self.fusion_outputs(a, b)
        )]
        r_blocks = [self.r_matrix(a, b, c, True) for a in self.labels for b in self.labels for c, _ in self.fusion_outputs(a, b)]
        return _cost_profile(f_blocks, r_blocks)


class LoadedFRMorseAdapter(BaseMorseCategoryAdapter):
    """Adapter for the repository's numeric multiplicity-aware FR evaluator.

    This accepts both ``SU32AnyonWikiFRBraidEvaluator`` and the historical
    ``DA4FRBraidEvaluator`` class.  The latter is generic despite its old name
    and is also the backend used with the D(Dic_12)=D(Dic_3) payload.
    """

    def __init__(
        self,
        evaluator,
        *,
        character=None,
        adapter_name=None,
        orthonormalize_svd_intertwiners=None,
    ):
        self.backend = evaluator
        self.labels = tuple(evaluator.labels)
        self.unit = evaluator.unit
        self._character = character
        self.name = adapter_name or type(evaluator).__name__
        if orthonormalize_svd_intertwiners is None:
            payload = getattr(evaluator, "payload", {})
            fusion_space = payload.get("basis_convention", {}).get(
                "fusion_space", ""
            )
            orthonormalize_svd_intertwiners = (
                "SVD nullspace basis" in fusion_space
            )
        self.orthonormalize_svd_intertwiners = bool(
            orthonormalize_svd_intertwiners
        )

    def dimension(self, label):
        return float(self.backend.dimension(label))

    def twist(self, label):
        return complex(self.backend.twist(label))

    def fusion_outputs(self, left, right):
        return tuple((target, int(mult)) for target, mult in self.backend.fusion_outputs(left, right))

    @lru_cache(maxsize=None)
    def f_block(self, a, b, c, d):
        block = self.backend.f_blocks[(a, b, c, d)]
        matrix = np.asarray(block["matrix"], dtype=np.complex128)
        inverse = self.backend.f_inv_blocks[(a, b, c, d)]
        if self.orthonormalize_svd_intertwiners:
            left_scale = np.asarray(
                [
                    1.0 / math.sqrt(self.dimension(channel))
                    for channel, _, _ in block["left_basis"]
                ],
                dtype=np.float64,
            )
            right_scale = np.asarray(
                [
                    math.sqrt(self.dimension(channel))
                    for channel, _, _ in block["right_basis"]
                ],
                dtype=np.float64,
            )
            matrix = (
                left_scale[:, np.newaxis]
                * matrix
                * right_scale[np.newaxis, :]
            )
            inverse = _inverse(matrix)
        return {
            "left_basis": block["left_basis"],
            "right_basis": block["right_basis"],
            "left_index": block["left_index"],
            "right_index": block["right_index"],
            "right_to_left": matrix,
            "left_to_right": inverse,
        }

    def r_matrix(self, a, b, c, positive):
        table = self.backend.r_positive if positive else self.backend.r_negative
        return table[(a, b, c)]

    def character(self, character_label, simple_label):
        if self._character is not None:
            return complex(self._character(character_label, simple_label))
        if character_label in {0, "0", None, "untwisted"}:
            return 1.0 + 0.0j
        raise ValueError(
            f"{self.name} adapter has no nontrivial character callback; "
            "fixed-label and untwisted Omega evaluation remain available"
        )

    def cost_profile(self):
        return _cost_profile(
            [block["matrix"] for block in self.backend.f_blocks.values()],
            list(self.backend.r_positive.values()),
        )
