from fractions import Fraction
import json

import pytest

from twisted_yetter.exact import (
    dumps,
    exact,
    exact_product,
    exact_sum,
    from_jsonable,
    rational,
    to_jsonable,
)


def test_rational_arithmetic_is_exact() -> None:
    assert rational(1, 3) + rational(1, 6) == Fraction(1, 2)
    assert exact_sum([rational(1, 3), rational(1, 6), rational(-1, 2)]) == 0
    assert exact_product([rational(2, 3), rational(9, 4)]) == rational(3, 2)


def test_integral_rationals_have_canonical_representation() -> None:
    assert exact(Fraction(6, 3)) == 2
    assert exact("10/5") == 2
    assert dumps(Fraction(6, 3)) == dumps(2)


def test_exact_equality_uses_fraction_not_float() -> None:
    left = rational(1, 10) + rational(2, 10)
    right = rational(3, 10)

    assert left == right
    assert left != 0.1 + 0.2


def test_json_serialization_is_deterministic() -> None:
    payload_a = {"b": rational(2, 5), "a": [3, rational(-4, 7)]}
    payload_b = {"a": [3, rational(-4, 7)], "b": rational(2, 5)}

    encoded = dumps(payload_a)

    assert encoded == dumps(payload_b)
    assert encoded == (
        '{"a":[{"type":"integer","value":"3"},'
        '{"denominator":"7","numerator":"-4","type":"rational"}],'
        '"b":{"denominator":"5","numerator":"2","type":"rational"}}'
    )


def test_json_round_trip_preserves_exact_values() -> None:
    payload = {"answer": rational(42), "sector": [rational(1, 2), rational(-3, 8)]}
    decoded = from_jsonable(json.loads(dumps(payload)))

    assert decoded == payload
    assert isinstance(decoded["sector"][0], Fraction)


def test_float_inputs_are_rejected() -> None:
    with pytest.raises(TypeError, match="unsupported exact scalar"):
        exact(0.5)  # type: ignore[arg-type]

    with pytest.raises(TypeError, match="floats are not allowed"):
        to_jsonable({"bad": 0.5})


def test_booleans_are_rejected_as_scalars() -> None:
    with pytest.raises(TypeError, match="booleans"):
        exact(True)  # type: ignore[arg-type]

    with pytest.raises(TypeError, match="booleans"):
        to_jsonable(False)
