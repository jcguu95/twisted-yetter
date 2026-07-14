"""Fail-closed numerical contract for finite semisimple ribbon categories.

The historical Morse evaluator accepted an F/R backend plus a prose pivotal
profile.  That is sufficient for the calibrated unitary controls, but it is
not a category-independent contract: it silently identifies inverse and dual
bases and assumes a positive square-root normalization for bends.

This module defines the data boundary used by the generic ribbon-graph
contractor.  The boundary is intentionally algebraic.  Degenerate braiding,
complex dimensions, non-orthogonal fusion bases, and fusion multiplicities
are all allowed.  Missing data is rejected before graph evaluation begins.
"""

from __future__ import annotations

from dataclasses import dataclass
import cmath
import hashlib
import json
from typing import Any, Protocol, runtime_checkable

import numpy as np

from experiments.sage.morse_pivotal_contract import (
    require_pivotal_capabilities,
    reverse_bend_scalar,
)


RIBBON_CATEGORY_CONTRACT_VERSION = "twisted-yetter.ribbon-fusion-category.v2"


class RibbonCategoryContractError(ValueError):
    """Raised when category data cannot define the requested ribbon graph."""


@runtime_checkable
class RibbonFusionCategoryV2(Protocol):
    """Runtime protocol consumed by the generic ribbon-graph contractor."""

    contract_version: str
    category_id: str
    category_data_hash: str
    labels: tuple[Any, ...]
    unit: Any
    numeric_tolerance: float

    def dual(self, label: Any) -> Any: ...

    def dimension(self, label: Any) -> complex: ...

    def twist(self, label: Any) -> complex: ...

    def pivotal_scalar(self, label: Any) -> complex: ...

    def fusion_multiplicity(self, left: Any, right: Any, output: Any) -> int: ...

    def fusion_basis_id(
        self, left: Any, right: Any, output: Any, multiplicity: int
    ) -> str: ...

    def f_block(self, a: Any, b: Any, c: Any, d: Any) -> dict[str, Any]: ...

    def r_matrix(
        self, a: Any, b: Any, c: Any, positive: bool
    ) -> Any: ...

    def fusion_pairing(self, a: Any, b: Any, c: Any) -> Any: ...

    def fusion_pairing_inverse(self, a: Any, b: Any, c: Any) -> Any: ...

    def left_evaluation(self, label: Any) -> complex: ...

    def left_coevaluation(self, label: Any) -> complex: ...

    def right_evaluation(self, label: Any) -> complex: ...

    def right_coevaluation(self, label: Any) -> complex: ...

    def coherence_certificate(self) -> dict[str, Any]: ...


def _matrix(value: Any) -> np.ndarray:
    result = np.asarray(value, dtype=np.complex128)
    if result.ndim != 2:
        raise RibbonCategoryContractError("category block is not a matrix")
    return result


def _complex_pair(value: complex) -> list[float]:
    number = complex(value)
    return [float(number.real), float(number.imag)]


def _stable_hash(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _fusion_basis(category: Any, a: Any, b: Any, c: Any) -> tuple[str, ...]:
    return tuple(
        category.fusion_basis_id(a, b, c, copy)
        for copy in range(category.fusion_multiplicity(a, b, c))
    )


@dataclass(frozen=True)
class RibbonCategoryValidationReport:
    category_id: str
    category_data_hash: str
    label_count: int
    fusion_space_count: int
    maximum_inverse_residual: float
    maximum_pairing_residual: float
    coherence_status: str
    tolerance: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "schema": "twisted-yetter.ribbon-category-validation.v1",
            "status": "PASS_RIBBON_FUSION_CATEGORY_V2_CONTRACT",
            "category_id": self.category_id,
            "category_data_hash": self.category_data_hash,
            "label_count": self.label_count,
            "fusion_space_count": self.fusion_space_count,
            "maximum_inverse_residual": self.maximum_inverse_residual,
            "maximum_pairing_residual": self.maximum_pairing_residual,
            "coherence_status": self.coherence_status,
            "tolerance": self.tolerance,
        }


def validate_ribbon_category_v2(
    category: RibbonFusionCategoryV2,
    *,
    require_full_coherence: bool = True,
) -> RibbonCategoryValidationReport:
    """Validate all local data needed by a numerical ribbon contraction.

    Full pentagon/hexagon enumeration can be expensive and belongs to the
    category-data producer.  Production evaluation therefore requires a
    hash-bound numeric coherence certificate.  This validator independently
    checks dimensions, duals, all fusion pairings, F inverses, R inverses,
    and the certificate/data-hash binding.
    """

    if getattr(category, "contract_version", None) != RIBBON_CATEGORY_CONTRACT_VERSION:
        raise RibbonCategoryContractError("category does not implement RibbonFusionCategoryV2")
    labels = tuple(category.labels)
    if not labels or len(set(labels)) != len(labels):
        raise RibbonCategoryContractError("category labels must be nonempty and unique")
    if category.unit not in labels:
        raise RibbonCategoryContractError("tensor unit is absent from category labels")
    if not isinstance(category.category_id, str) or not category.category_id:
        raise RibbonCategoryContractError("category_id must be nonempty")
    if not isinstance(category.category_data_hash, str) or not category.category_data_hash.startswith("sha256:"):
        raise RibbonCategoryContractError("category_data_hash must be a sha256 identifier")
    tolerance = float(category.numeric_tolerance)
    if not (0.0 < tolerance < 1e-2):
        raise RibbonCategoryContractError("numeric_tolerance is outside the supported range")

    fusion_spaces = 0
    max_pairing_residual = 0.0
    for label in labels:
        dual = category.dual(label)
        if dual not in labels or category.dual(dual) != label:
            raise RibbonCategoryContractError(f"invalid duality for {label!r}")
        for value, name in (
            (category.dimension(label), "dimension"),
            (category.twist(label), "twist"),
            (category.pivotal_scalar(label), "pivotal scalar"),
            (category.left_evaluation(label), "left evaluation"),
            (category.left_coevaluation(label), "left coevaluation"),
            (category.right_evaluation(label), "right evaluation"),
            (category.right_coevaluation(label), "right coevaluation"),
        ):
            number = complex(value)
            if not np.isfinite(number.real) or not np.isfinite(number.imag):
                raise RibbonCategoryContractError(f"non-finite {name} for {label!r}")
        if abs(complex(category.dimension(label))) <= tolerance:
            raise RibbonCategoryContractError(f"vanishing quantum dimension for {label!r}")
        if abs(complex(category.twist(label))) <= tolerance:
            raise RibbonCategoryContractError(f"vanishing twist for {label!r}")

    for a in labels:
        for b in labels:
            for c in labels:
                multiplicity = category.fusion_multiplicity(a, b, c)
                if not isinstance(multiplicity, int) or multiplicity < 0:
                    raise RibbonCategoryContractError(
                        f"invalid fusion multiplicity N[{a!r},{b!r}]^{c!r}"
                    )
                basis = _fusion_basis(category, a, b, c)
                if len(set(basis)) != multiplicity:
                    raise RibbonCategoryContractError(
                        f"fusion basis ids are not unique for {(a, b, c)!r}"
                    )
                if multiplicity == 0:
                    continue
                fusion_spaces += 1
                pairing = _matrix(category.fusion_pairing(a, b, c))
                pairing_inverse = _matrix(category.fusion_pairing_inverse(a, b, c))
                if pairing.shape != (multiplicity, multiplicity):
                    raise RibbonCategoryContractError(
                        f"pairing shape mismatch for {(a, b, c)!r}: {pairing.shape!r}"
                    )
                residual = float(
                    np.max(np.abs(pairing @ pairing_inverse - np.eye(multiplicity)))
                )
                max_pairing_residual = max(max_pairing_residual, residual)

                positive = _matrix(category.r_matrix(a, b, c, True))
                negative = _matrix(category.r_matrix(b, a, c, False))
                expected_shape = (
                    category.fusion_multiplicity(b, a, c), multiplicity
                )
                if positive.shape != expected_shape or negative.shape != expected_shape[::-1]:
                    raise RibbonCategoryContractError(
                        f"R block shape mismatch for {(a, b, c)!r}"
                    )
                r_residual = float(
                    np.max(np.abs(negative @ positive - np.eye(multiplicity)))
                )
                max_pairing_residual = max(max_pairing_residual, r_residual)

    max_inverse_residual = 0.0
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    left_size = sum(
                        category.fusion_multiplicity(a, b, x)
                        * category.fusion_multiplicity(x, c, d)
                        for x in labels
                    )
                    right_size = sum(
                        category.fusion_multiplicity(b, c, y)
                        * category.fusion_multiplicity(a, y, d)
                        for y in labels
                    )
                    if left_size == right_size == 0:
                        continue
                    if left_size != right_size:
                        raise RibbonCategoryContractError(
                            f"fusion associativity dimension mismatch for {(a, b, c, d)!r}"
                        )
                    block = category.f_block(a, b, c, d)
                    forward = _matrix(block["right_to_left"])
                    inverse = _matrix(block["left_to_right"])
                    if forward.shape != (left_size, right_size) or inverse.shape != (
                        right_size,
                        left_size,
                    ):
                        raise RibbonCategoryContractError(
                            f"F block shape mismatch for {(a, b, c, d)!r}"
                        )
                    residual = float(
                        np.max(np.abs(forward @ inverse - np.eye(left_size)))
                    )
                    max_inverse_residual = max(max_inverse_residual, residual)

    certificate = category.coherence_certificate()
    if not isinstance(certificate, dict):
        raise RibbonCategoryContractError("coherence certificate must be an object")
    if certificate.get("category_data_hash") != category.category_data_hash:
        raise RibbonCategoryContractError("coherence certificate is not bound to category data")
    coherence_status = str(certificate.get("status", "MISSING"))
    if require_full_coherence and coherence_status != "PASS_FULL_NUMERIC_RIBBON_COHERENCE":
        raise RibbonCategoryContractError(
            f"category lacks a full numeric coherence certificate: {coherence_status}"
        )
    reported_residual = float(certificate.get("maximum_residual", float("inf")))
    if require_full_coherence and reported_residual > tolerance:
        raise RibbonCategoryContractError(
            f"coherence residual {reported_residual} exceeds tolerance {tolerance}"
        )
    if max(max_inverse_residual, max_pairing_residual) > tolerance:
        raise RibbonCategoryContractError(
            "local category inverse/pairing residual exceeds numeric tolerance"
        )
    return RibbonCategoryValidationReport(
        category_id=category.category_id,
        category_data_hash=category.category_data_hash,
        label_count=len(labels),
        fusion_space_count=fusion_spaces,
        maximum_inverse_residual=max_inverse_residual,
        maximum_pairing_residual=max_pairing_residual,
        coherence_status=coherence_status,
        tolerance=tolerance,
    )


class LegacyRibbonCategoryV2Adapter:
    """Strict bridge for calibrated orthonormal historical category adapters.

    This bridge does not infer a pivotal normalization.  It only accepts a
    historical profile that explicitly records orthonormal fusion spaces and
    ``sqrt(quantum_dimension)`` evaluation/coevaluation.  Such categories may
    be used for structural development and oracle comparisons; production
    still requires a full hash-bound coherence certificate.
    """

    contract_version = RIBBON_CATEGORY_CONTRACT_VERSION

    def __init__(
        self,
        category: Any,
        *,
        numeric_tolerance: float = 1e-10,
        coherence_certificate: dict[str, Any] | None = None,
    ):
        require_pivotal_capabilities(
            category,
            {"rigid_bends", "trivalent_pairing", "vacuum_projector", "ribbon_twist"},
        )
        profile = category.pivotal_profile
        pairing = profile["fusion_space_pairing"]
        normalization = profile["evaluation_coevaluation"].get("normalization")
        if pairing.get("orthonormal") is not True:
            raise RibbonCategoryContractError(
                "legacy bridge only accepts explicitly orthonormal fusion spaces"
            )
        if normalization != "sqrt(quantum_dimension)":
            raise RibbonCategoryContractError(
                "legacy bridge requires an explicit sqrt(quantum_dimension) normalization"
            )
        self.legacy = category
        self.labels = tuple(category.labels)
        self.unit = category.unit
        self.category_id = str(category.category_id)
        self.numeric_tolerance = float(numeric_tolerance)
        summary = {
            "contract": RIBBON_CATEGORY_CONTRACT_VERSION,
            "category_id": self.category_id,
            "labels": [repr(label) for label in self.labels],
            "unit": repr(self.unit),
            "pivotal_profile": profile,
            "fusion": [
                [repr(a), repr(b), repr(c), category.fusion_multiplicity(a, b, c)]
                for a in self.labels
                for b in self.labels
                for c in self.labels
            ],
        }
        self.category_data_hash = _stable_hash(summary)
        self._coherence_certificate = coherence_certificate or {
            "status": "LEGACY_PROFILE_STRUCTURAL_ONLY",
            "category_data_hash": self.category_data_hash,
            "maximum_residual": 0.0,
        }

    def dual(self, label: Any) -> Any:
        return self.legacy.dual(label)

    def dimension(self, label: Any) -> complex:
        return complex(self.legacy.dimension(label))

    def twist(self, label: Any) -> complex:
        return complex(self.legacy.twist(label))

    def pivotal_scalar(self, label: Any) -> complex:
        return complex(reverse_bend_scalar(self.legacy, label))

    def fusion_multiplicity(self, left: Any, right: Any, output: Any) -> int:
        return int(self.legacy.fusion_multiplicity(left, right, output))

    def fusion_basis_id(
        self, left: Any, right: Any, output: Any, multiplicity: int
    ) -> str:
        if not (0 <= multiplicity < self.fusion_multiplicity(left, right, output)):
            raise RibbonCategoryContractError("fusion basis multiplicity is out of range")
        return f"Hom({left!r}*{right!r}->{output!r})[{multiplicity}]"

    def f_block(self, a: Any, b: Any, c: Any, d: Any) -> dict[str, Any]:
        return self.legacy.f_block(a, b, c, d)

    def r_matrix(self, a: Any, b: Any, c: Any, positive: bool) -> Any:
        return self.legacy.r_matrix(a, b, c, positive)

    def fusion_pairing(self, a: Any, b: Any, c: Any) -> np.ndarray:
        size = self.fusion_multiplicity(a, b, c)
        return np.eye(size, dtype=np.complex128)

    def fusion_pairing_inverse(self, a: Any, b: Any, c: Any) -> np.ndarray:
        size = self.fusion_multiplicity(a, b, c)
        return np.eye(size, dtype=np.complex128)

    def _bend_normalization(self, label: Any) -> complex:
        return cmath.sqrt(self.dimension(label))

    def left_evaluation(self, label: Any) -> complex:
        return self._bend_normalization(label)

    def left_coevaluation(self, label: Any) -> complex:
        return self._bend_normalization(label)

    def right_evaluation(self, label: Any) -> complex:
        return self.pivotal_scalar(label) * self._bend_normalization(label)

    def right_coevaluation(self, label: Any) -> complex:
        return self.pivotal_scalar(label) ** -1 * self._bend_normalization(label)

    def coherence_certificate(self) -> dict[str, Any]:
        return dict(self._coherence_certificate)


def category_contract_snapshot(category: RibbonFusionCategoryV2) -> dict[str, Any]:
    """Return a small, deterministic public snapshot for run identities."""

    return {
        "contract_version": category.contract_version,
        "category_id": category.category_id,
        "category_data_hash": category.category_data_hash,
        "labels": [repr(label) for label in category.labels],
        "unit": repr(category.unit),
        "numeric_tolerance": category.numeric_tolerance,
        "dimensions": {
            repr(label): _complex_pair(category.dimension(label))
            for label in category.labels
        },
        "twists": {
            repr(label): _complex_pair(category.twist(label))
            for label in category.labels
        },
    }
