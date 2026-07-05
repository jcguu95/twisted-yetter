"""Minimal exact SU(2)_2 category/link-data certificate.

This module records only data needed for n15 sanity checks: simple labels,
fusion multiplicities, quantum dimensions in Q(sqrt(2)), the global dimension,
and local-convention RT link controls for the next evaluator gate.

The S-matrix and twist table below are exact local working targets.  Their
claim level remains source-needed until the RT/Kauffman source record has
page-level labels.  Formula-level omega/theta, braiding, F-symbol, R-symbol,
and link evaluation are intentionally not implemented here.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Final

from twisted_yetter.exact import ExactNumber, exact
from twisted_yetter.legacy_prose import legacy_prose_member_ref

FORMULA_LEDGER_REFERENCE: Final = legacy_prose_member_ref(
    "wiki/understandings/formula-conventions.org"
)
RT_LINK_LEDGER_REFERENCE: Final = legacy_prose_member_ref(
    "wiki/understandings/rt-link-conventions.org"
)
RT_LINK_SOURCE_REFERENCE: Final = legacy_prose_member_ref(
    "wiki/references/rt-or-kauffman-link-source.org"
)
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


@dataclass(frozen=True, order=True)
class RootOfUnityPower:
    """Exact symbolic root of unity power ``zeta_order^exponent``."""

    order: int
    exponent: int

    def __post_init__(self) -> None:
        if (
            isinstance(self.order, bool)
            or isinstance(self.exponent, bool)
            or not isinstance(self.order, int)
            or not isinstance(self.exponent, int)
        ):
            raise TypeError("root-of-unity order and exponent must be integers")
        if self.order <= 0:
            raise ValueError("root-of-unity order must be positive")
        object.__setattr__(self, "exponent", self.exponent % self.order)

    def to_jsonable(self) -> dict[str, int | str]:
        return {
            "kind": "root_of_unity_power",
            "symbol": f"zeta_{self.order}",
            "order": self.order,
            "exponent": self.exponent,
        }


ONE: Final = QuadraticSurd(1)
SQRT2: Final = QuadraticSurd(0, 1)
ZERO: Final = QuadraticSurd(0)
HALF: Final = QuadraticSurd(Fraction(1, 2))
SQRT2_OVER_2: Final = QuadraticSurd(0, Fraction(1, 2))
NEG_SQRT2_OVER_2: Final = QuadraticSurd(0, Fraction(-1, 2))

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

S_MATRIX: Final[tuple[tuple[QuadraticSurd, ...], ...]] = (
    (HALF, SQRT2_OVER_2, HALF),
    (SQRT2_OVER_2, ZERO, NEG_SQRT2_OVER_2),
    (HALF, NEG_SQRT2_OVER_2, HALF),
)

TWIST_VALUES: Final[dict[str, RootOfUnityPower]] = {
    "0": RootOfUnityPower(16, 0),
    "1": RootOfUnityPower(16, 3),
    "2": RootOfUnityPower(16, 8),
}

LINK_DATA_CLAIM_LEVELS: Final = {
    "fusion_dimension_algebra": {
        "claim_level": "computed evidence/schema-test-safe",
        "ledger": FORMULA_LEDGER_REFERENCE,
    },
    "s_matrix": {
        "claim_level": "SOURCE NEEDED/local-convention",
        "ledger": RT_LINK_LEDGER_REFERENCE,
        "source_record": RT_LINK_SOURCE_REFERENCE,
        "normalization": "S_00 = 1/2 and d_i = S_0i / S_00",
    },
    "hopf_control": {
        "claim_level": "SOURCE NEEDED/local-convention",
        "ledger": RT_LINK_LEDGER_REFERENCE,
        "source_record": RT_LINK_SOURCE_REFERENCE,
        "working_target": "positive 0-framed Hopf value S_ij / S_00",
    },
    "twists": {
        "claim_level": "SOURCE NEEDED/local-convention",
        "ledger": RT_LINK_LEDGER_REFERENCE,
        "source_record": RT_LINK_SOURCE_REFERENCE,
        "positive_framing_sign": "SOURCE NEEDED",
        "root_symbol": "zeta_16 = exp(2 pi i / 16), recorded symbolically",
    },
}

OMEGA_THETA_CONVENTION: Final = {
    "status": "source-needed/working",
    "ledger": FORMULA_LEDGER_REFERENCE,
    "ordinary_color": "ledger records omega = sum_i Delta_i i as WORKING UNDERSTANDING",
    "decorated_color": "ledger records theta = sum_i (-1)^i Delta_i i as WORKING UNDERSTANDING",
    "reason_numeric_coefficients_absent": (
        "ledger marks Delta_i versus quantum dimension and parity convention as SOURCE NEEDED"
    ),
}

UNSUPPORTED_DATA: Final = {
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


def s_matrix_entry(left: str, right: str) -> QuadraticSurd:
    """Return the local-convention modular S-matrix entry."""

    return S_MATRIX[_label_index(left)][_label_index(right)]


def hopf_control_entry(left: str, right: str) -> QuadraticSurd:
    """Return the local target ``S_ij / S_00`` for the positive Hopf control."""

    return QuadraticSurd(2) * s_matrix_entry(left, right)


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
    if len(S_MATRIX) != len(SIMPLE_LABELS):
        raise ValueError("S-matrix must have one row per simple label")
    if tuple(TWIST_VALUES) != SIMPLE_LABELS:
        raise ValueError("twist table must use the simple-label order")
    for (left, right), output in FUSION_RULES.items():
        for label, multiplicity in output.items():
            _check_label(left)
            _check_label(right)
            _check_label(label)
            if not isinstance(multiplicity, int) or multiplicity < 0:
                raise ValueError("fusion multiplicities must be nonnegative integers")
    for left in SIMPLE_LABELS:
        if len(S_MATRIX[_label_index(left)]) != len(SIMPLE_LABELS):
            raise ValueError("S-matrix rows must have one entry per simple label")
        for right in SIMPLE_LABELS:
            if s_matrix_entry(left, right) != s_matrix_entry(right, left):
                raise ValueError("S-matrix must be symmetric")
            if left == "0":
                expected = s_matrix_entry("0", "0") * QUANTUM_DIMENSIONS[right]
                if s_matrix_entry("0", right) != expected:
                    raise ValueError("S_0i dimension relation failed")
    if _s_matrix_square() != _identity_matrix():
        raise ValueError("S-matrix self-dual square check failed")


def certificate_payload() -> dict[str, object]:
    """Return a deterministic JSON-ready category-data certificate payload."""

    validate_certificate()
    return {
        "schema": "twisted-yetter.su2-level2-category-data.v1",
        "status": "pass",
        "node_id": "n15-su2-level2-link-data",
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
        "s_matrix": [
            [entry.to_jsonable() for entry in row]
            for row in S_MATRIX
        ],
        "twists": {
            label: TWIST_VALUES[label].to_jsonable() for label in SIMPLE_LABELS
        },
        "hopf_control": {
            f"{left},{right}": hopf_control_entry(left, right).to_jsonable()
            for left in SIMPLE_LABELS
            for right in SIMPLE_LABELS
        },
        "link_data_claim_levels": LINK_DATA_CLAIM_LEVELS,
        "omega_theta_convention": OMEGA_THETA_CONVENTION,
        "unsupported_data": UNSUPPORTED_DATA,
    }


def _check_label(label: str) -> None:
    if label not in SIMPLE_LABELS:
        raise ValueError(f"unknown SU(2)_2 simple label: {label!r}")


def _label_index(label: str) -> int:
    _check_label(label)
    return SIMPLE_LABELS.index(label)


def _s_matrix_square() -> tuple[tuple[QuadraticSurd, ...], ...]:
    return tuple(
        tuple(
            sum(
                S_MATRIX[row][middle] * S_MATRIX[middle][column]
                for middle in range(len(SIMPLE_LABELS))
            )
            for column in range(len(SIMPLE_LABELS))
        )
        for row in range(len(SIMPLE_LABELS))
    )


def _identity_matrix() -> tuple[tuple[QuadraticSurd, ...], ...]:
    return tuple(
        tuple(ONE if row == column else ZERO for column in range(len(SIMPLE_LABELS)))
        for row in range(len(SIMPLE_LABELS))
    )


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
