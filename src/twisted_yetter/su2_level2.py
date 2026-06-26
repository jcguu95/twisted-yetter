"""Minimal exact SU(2)_2 category-data certificate.

This module records only data needed for n15 sanity checks: simple labels,
fusion multiplicities, quantum dimensions in Q(sqrt(2)), and the global
dimension.  Formula-level omega/theta, twist, braiding, F-symbol, and R-symbol
data are intentionally not guessed.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Final

from twisted_yetter.exact import ExactNumber, exact

LEDGER_REFERENCE: Final = "wiki/understandings/formula-conventions.org"
SIMPLE_LABELS: Final[tuple[str, ...]] = ("0", "1", "2")


@dataclass(frozen=True, order=True)
class QuadraticSurd:
    """Exact element ``a + b sqrt(2)`` with rational coefficients."""

    rational: ExactNumber = 0
    sqrt2: ExactNumber = 0

    def __post_init__(self) -> None:
        object.__setattr__(self, "rational", exact(self.rational))
        object.__setattr__(self, "sqrt2", exact(self.sqrt2))

    def __add__(self, other: object) -> QuadraticSurd:
        rhs = _coerce_surd(other)
        return QuadraticSurd(
            _as_fraction(self.rational) + _as_fraction(rhs.rational),
            _as_fraction(self.sqrt2) + _as_fraction(rhs.sqrt2),
        )

    def __radd__(self, other: object) -> QuadraticSurd:
        return self + other

    def __neg__(self) -> QuadraticSurd:
        return QuadraticSurd(-_as_fraction(self.rational), -_as_fraction(self.sqrt2))

    def __sub__(self, other: object) -> QuadraticSurd:
        return self + (-_coerce_surd(other))

    def __rsub__(self, other: object) -> QuadraticSurd:
        return _coerce_surd(other) - self

    def __mul__(self, other: object) -> QuadraticSurd:
        rhs = _coerce_surd(other)
        a = _as_fraction(self.rational)
        b = _as_fraction(self.sqrt2)
        c = _as_fraction(rhs.rational)
        d = _as_fraction(rhs.sqrt2)
        return QuadraticSurd(a * c + 2 * b * d, a * d + b * c)

    def __rmul__(self, other: object) -> QuadraticSurd:
        return self * other

    def to_jsonable(self) -> dict[str, dict[str, str] | str]:
        return {
            "kind": "Q(sqrt2)",
            "rational": _json_exact(self.rational),
            "sqrt2": _json_exact(self.sqrt2),
        }


ONE: Final = QuadraticSurd(1)
SQRT2: Final = QuadraticSurd(0, 1)
ZERO: Final = QuadraticSurd(0)

QUANTUM_DIMENSIONS: Final[dict[str, QuadraticSurd]] = {
    "0": ONE,
    "1": SQRT2,
    "2": ONE,
}

FUSION_RULES: Final[dict[tuple[str, str], dict[str, int]]] = {
    ("0", "0"): {"0": 1},
    ("0", "1"): {"1": 1},
    ("0", "2"): {"2": 1},
    ("1", "0"): {"1": 1},
    ("1", "1"): {"0": 1, "2": 1},
    ("1", "2"): {"1": 1},
    ("2", "0"): {"2": 1},
    ("2", "1"): {"1": 1},
    ("2", "2"): {"0": 1},
}

GLOBAL_DIMENSION: Final = QuadraticSurd(4)

OMEGA_THETA_CONVENTION: Final = {
    "status": "source-needed/working",
    "ledger": LEDGER_REFERENCE,
    "ordinary_color": "ledger records omega = sum_i Delta_i i as WORKING UNDERSTANDING",
    "decorated_color": "ledger records theta = sum_i (-1)^i Delta_i i as WORKING UNDERSTANDING",
    "reason_numeric_coefficients_absent": (
        "ledger marks Delta_i versus quantum dimension and parity convention as SOURCE NEEDED"
    ),
}

UNSUPPORTED_DATA: Final = {
    "twists": "absent: root-of-unity and orientation conventions not yet source-audited",
    "braiding": "absent: R-symbol convention not recorded for this repo",
    "f_symbols": "absent: F-symbol gauge not recorded for this repo",
    "r_symbols": "absent: R-symbol gauge not recorded for this repo",
    "invariant_formula": "absent: n15 is category data only, not a Kirby formula node",
    "numeric_omega_theta_coefficients": (
        "absent: formula-conventions ledger still marks Delta_i/parity as SOURCE NEEDED"
    ),
}


def fusion(left: str, right: str) -> dict[str, int]:
    """Return fusion multiplicities for two simple labels."""

    _check_label(left)
    _check_label(right)
    return dict(FUSION_RULES[(left, right)])


def global_dimension_from_simples() -> QuadraticSurd:
    """Compute sum_i d_i^2 exactly in Q(sqrt(2))."""

    total = ZERO
    for dimension in QUANTUM_DIMENSIONS.values():
        total += dimension * dimension
    return total


def validate_certificate() -> None:
    """Raise if the encoded SU(2)_2 certificate violates internal checks."""

    if tuple(QUANTUM_DIMENSIONS) != SIMPLE_LABELS:
        raise ValueError("quantum dimensions must use the simple-label order")
    if set(FUSION_RULES) != {
        (left, right) for left in SIMPLE_LABELS for right in SIMPLE_LABELS
    }:
        raise ValueError("fusion table must contain every ordered pair")
    if global_dimension_from_simples() != GLOBAL_DIMENSION:
        raise ValueError("global dimension sanity check failed")
    for (left, right), output in FUSION_RULES.items():
        for label, multiplicity in output.items():
            _check_label(left)
            _check_label(right)
            _check_label(label)
            if not isinstance(multiplicity, int) or multiplicity < 0:
                raise ValueError("fusion multiplicities must be nonnegative integers")


def certificate_payload() -> dict[str, object]:
    """Return a deterministic JSON-ready category-data certificate payload."""

    validate_certificate()
    return {
        "schema": "twisted-yetter.su2-level2-category-data.v1",
        "status": "pass",
        "node_id": "n15-su2-level2-certificate",
        "simple_labels": list(SIMPLE_LABELS),
        "quantum_dimensions": {
            label: QUANTUM_DIMENSIONS[label].to_jsonable() for label in SIMPLE_LABELS
        },
        "fusion_rules": {
            f"{left}*{right}": FUSION_RULES[(left, right)]
            for left in SIMPLE_LABELS
            for right in SIMPLE_LABELS
        },
        "global_dimension": GLOBAL_DIMENSION.to_jsonable(),
        "omega_theta_convention": OMEGA_THETA_CONVENTION,
        "unsupported_data": UNSUPPORTED_DATA,
    }


def _check_label(label: str) -> None:
    if label not in SIMPLE_LABELS:
        raise ValueError(f"unknown SU(2)_2 simple label: {label!r}")


def _coerce_surd(value: object) -> QuadraticSurd:
    if isinstance(value, QuadraticSurd):
        return value
    if isinstance(value, int | Fraction | str):
        return QuadraticSurd(value)
    return NotImplemented  # type: ignore[return-value]


def _as_fraction(value: ExactNumber) -> Fraction:
    exact_value = exact(value)
    if isinstance(exact_value, int):
        return Fraction(exact_value, 1)
    return exact_value


def _json_exact(value: ExactNumber) -> dict[str, str]:
    exact_value = exact(value)
    if isinstance(exact_value, int):
        return {"type": "integer", "value": str(exact_value)}
    return {
        "type": "rational",
        "numerator": str(exact_value.numerator),
        "denominator": str(exact_value.denominator),
    }


validate_certificate()
