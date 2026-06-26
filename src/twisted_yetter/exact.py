"""Small exact arithmetic helpers for certificate-level outputs.

The n10 backend deliberately stays in Python's standard library: integers are
Python ``int`` values and rationals are ``fractions.Fraction`` values.  Floats
are rejected at the boundary so official outputs cannot silently depend on
rounding.
"""

from __future__ import annotations

from fractions import Fraction
import json
from math import prod
from typing import Any, TypeAlias

ExactNumber: TypeAlias = int | Fraction
JsonExact: TypeAlias = dict[str, str] | list["JsonExact"] | dict[str, "JsonExact"]


def exact(value: int | str | Fraction | tuple[int, int]) -> ExactNumber:
    """Return a canonical exact number.

    Integral rationals are canonicalized back to ``int`` so equal exact values
    have a single JSON representation.
    """

    if isinstance(value, bool):
        raise TypeError("booleans are not exact arithmetic scalars")
    if isinstance(value, int):
        return value
    if isinstance(value, Fraction):
        return _canonical_fraction(value)
    if isinstance(value, str):
        return _canonical_fraction(Fraction(value))
    if isinstance(value, tuple) and len(value) == 2:
        numerator, denominator = value
        if isinstance(numerator, bool) or isinstance(denominator, bool):
            raise TypeError("booleans are not exact arithmetic scalars")
        return _canonical_fraction(Fraction(numerator, denominator))
    raise TypeError(f"unsupported exact scalar: {type(value).__name__}")


def rational(numerator: int, denominator: int = 1) -> ExactNumber:
    """Build a canonical exact rational from integer numerator/denominator."""

    return exact((numerator, denominator))


def exact_sum(values: Any) -> ExactNumber:
    """Sum exact scalars without introducing floats."""

    return exact(sum(_as_fraction(value) for value in values))


def exact_product(values: Any) -> ExactNumber:
    """Multiply exact scalars without introducing floats."""

    return exact(prod(_as_fraction(value) for value in values))


def to_jsonable(value: Any) -> Any:
    """Convert exact values and containers to deterministic JSON-ready data."""

    if isinstance(value, bool):
        raise TypeError("booleans are not exact arithmetic scalars")
    if isinstance(value, float):
        raise TypeError("floats are not allowed in exact JSON output")
    if isinstance(value, int):
        return {"type": "integer", "value": str(value)}
    if isinstance(value, Fraction):
        canonical = exact(value)
        if isinstance(canonical, int):
            return to_jsonable(canonical)
        return {
            "type": "rational",
            "numerator": str(canonical.numerator),
            "denominator": str(canonical.denominator),
        }
    if isinstance(value, tuple):
        return [to_jsonable(item) for item in value]
    if isinstance(value, list):
        return [to_jsonable(item) for item in value]
    if isinstance(value, dict):
        return {str(key): to_jsonable(value[key]) for key in sorted(value)}
    raise TypeError(f"unsupported exact JSON value: {type(value).__name__}")


def from_jsonable(value: Any) -> Any:
    """Recover exact values from :func:`to_jsonable` output."""

    if isinstance(value, list):
        return [from_jsonable(item) for item in value]
    if isinstance(value, dict):
        value_type = value.get("type")
        if value_type == "integer":
            return int(value["value"])
        if value_type == "rational":
            return rational(int(value["numerator"]), int(value["denominator"]))
        return {key: from_jsonable(item) for key, item in value.items()}
    raise TypeError(f"unsupported exact JSON payload: {type(value).__name__}")


def dumps(value: Any) -> str:
    """Serialize exact data as stable, compact JSON."""

    return json.dumps(to_jsonable(value), sort_keys=True, separators=(",", ":"))


def _canonical_fraction(value: Fraction) -> ExactNumber:
    if value.denominator == 1:
        return value.numerator
    return value


def _as_fraction(value: Any) -> Fraction:
    exact_value = exact(value)
    if isinstance(exact_value, int):
        return Fraction(exact_value, 1)
    return exact_value
