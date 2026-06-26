from fractions import Fraction

import twisted_yetter


def test_package_import_and_version() -> None:
    assert twisted_yetter.__version__ == "0.1.0"


def test_stdlib_fraction_exact_arithmetic_sanity() -> None:
    assert Fraction(1, 3) + Fraction(1, 6) == Fraction(1, 2)
