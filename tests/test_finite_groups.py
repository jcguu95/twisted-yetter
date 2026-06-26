import json

import pytest

from twisted_yetter.finite_groups import (
    TRIVIAL_GROUP,
    Z2_GROUP,
    certificate_payload,
    character_table,
    character_value,
    column_inner_product,
    cyclic_group,
    row_inner_product,
    validate_character_table,
)


def test_supported_groups_have_deterministic_ordering() -> None:
    assert cyclic_group(1) == TRIVIAL_GROUP
    assert cyclic_group(2) == Z2_GROUP
    assert TRIVIAL_GROUP.elements == ((),)
    assert TRIVIAL_GROUP.characters == ((),)
    assert Z2_GROUP.elements == ((0,), (1,))
    assert Z2_GROUP.characters == ((0,), (1,))


def test_trivial_group_character_table_is_exact() -> None:
    table = character_table(TRIVIAL_GROUP)

    assert table == {(): {(): 1}}
    assert character_value(TRIVIAL_GROUP, (), ()) == 1
    assert isinstance(character_value(TRIVIAL_GROUP, (), ()), int)


def test_z2_character_table_has_trivial_and_sign_rows() -> None:
    table = character_table(Z2_GROUP)

    assert table[(0,)] == {(0,): 1, (1,): 1}
    assert table[(1,)] == {(0,): 1, (1,): -1}
    assert character_value(Z2_GROUP, (1,), (0,)) == 1
    assert character_value(Z2_GROUP, (1,), (1,)) == -1


def test_character_values_do_not_use_float() -> None:
    for row in character_table(Z2_GROUP).values():
        for value in row.values():
            assert isinstance(value, int)
            assert not isinstance(value, float)


def test_row_and_column_orthogonality() -> None:
    validate_character_table(TRIVIAL_GROUP)
    validate_character_table(Z2_GROUP)

    assert row_inner_product(Z2_GROUP, (0,), (0,)) == 2
    assert row_inner_product(Z2_GROUP, (0,), (1,)) == 0
    assert row_inner_product(Z2_GROUP, (1,), (1,)) == 2
    assert column_inner_product(Z2_GROUP, (0,), (0,)) == 2
    assert column_inner_product(Z2_GROUP, (0,), (1,)) == 0
    assert column_inner_product(Z2_GROUP, (1,), (1,)) == 2


def test_unknown_element_and_character_are_rejected() -> None:
    with pytest.raises(ValueError, match="unknown element"):
        character_value(Z2_GROUP, (0,), (2,))

    with pytest.raises(ValueError, match="unknown character"):
        character_value(Z2_GROUP, (2,), (0,))


def test_z3_is_not_silently_approximated() -> None:
    with pytest.raises(ValueError, match="unsupported exact cyclic character table"):
        cyclic_group(3)


def test_certificate_payload_is_stable_json_data() -> None:
    payload = certificate_payload(Z2_GROUP)
    encoded = json.dumps(payload, sort_keys=True)

    assert payload["schema"] == "twisted-yetter.finite-abelian-character-data.v1"
    assert payload["status"] == "pass"
    assert payload["group"] == {
        "name": "Z/2",
        "invariant_factors": [2],
        "order": 2,
        "elements": ["0", "1"],
        "characters": ["chi_0", "chi_1"],
    }
    assert payload["character_table"]["chi_1"]["1"] == {
        "type": "integer",
        "value": "-1",
    }
    assert ".0" not in encoded
