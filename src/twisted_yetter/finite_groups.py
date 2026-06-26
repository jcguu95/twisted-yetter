"""Tiny exact finite abelian character tables.

This n11 module intentionally supports only the cases needed for first
Omega_a candidate tests: the trivial group and Z/2.  Character values are exact
integers, so no floating point or approximate roots of unity enter the
certificate-level data.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from twisted_yetter.exact import ExactNumber, exact, to_jsonable

GroupElement = tuple[int, ...]
CharacterLabel = tuple[int, ...]

SUPPORTED_INVARIANT_FACTORS: Final = {(), (2,)}


@dataclass(frozen=True, order=True)
class FiniteAbelianGroup:
    """Finite abelian group recorded by invariant factors.

    Elements and character labels use deterministic coordinate tuples.  The
    trivial group has the single empty tuple element and character.
    """

    invariant_factors: tuple[int, ...]
    elements: tuple[GroupElement, ...]
    characters: tuple[CharacterLabel, ...]

    @property
    def order(self) -> int:
        return len(self.elements)

    @property
    def name(self) -> str:
        if self.invariant_factors == ():
            return "trivial"
        return " x ".join(f"Z/{factor}" for factor in self.invariant_factors)


TRIVIAL_GROUP: Final = FiniteAbelianGroup((), ((),), ((),))
Z2_GROUP: Final = FiniteAbelianGroup((2,), ((0,), (1,)), ((0,), (1,)))


def cyclic_group(order: int) -> FiniteAbelianGroup:
    """Return supported cyclic groups with deterministic ordering."""

    if order == 1:
        return TRIVIAL_GROUP
    if order == 2:
        return Z2_GROUP
    raise ValueError(f"unsupported exact cyclic character table: Z/{order}")


def character_value(
    group: FiniteAbelianGroup,
    character: CharacterLabel,
    element: GroupElement,
) -> ExactNumber:
    """Evaluate a supported character exactly."""

    validate_supported_group(group)
    _check_character(group, character)
    _check_element(group, element)

    if group.invariant_factors == ():
        return 1
    if group.invariant_factors == (2,):
        return 1 if (character[0] * element[0]) % 2 == 0 else -1
    raise ValueError(f"unsupported exact character table: {group.name}")


def character_table(
    group: FiniteAbelianGroup,
) -> dict[CharacterLabel, dict[GroupElement, ExactNumber]]:
    """Return rows indexed by characters and columns indexed by elements."""

    validate_supported_group(group)
    return {
        character: {
            element: character_value(group, character, element)
            for element in group.elements
        }
        for character in group.characters
    }


def row_inner_product(
    group: FiniteAbelianGroup,
    left: CharacterLabel,
    right: CharacterLabel,
) -> ExactNumber:
    """Compute sum_g chi_left(g) chi_right(g)^* for supported real tables."""

    return exact(
        sum(
            character_value(group, left, element)
            * character_value(group, right, element)
            for element in group.elements
        )
    )


def column_inner_product(
    group: FiniteAbelianGroup,
    left: GroupElement,
    right: GroupElement,
) -> ExactNumber:
    """Compute sum_chi chi(left) chi(right)^* for supported real tables."""

    return exact(
        sum(
            character_value(group, character, left)
            * character_value(group, character, right)
            for character in group.characters
        )
    )


def validate_supported_group(group: FiniteAbelianGroup) -> None:
    """Raise if the group is outside the exact n11 support boundary."""

    if group.invariant_factors not in SUPPORTED_INVARIANT_FACTORS:
        raise ValueError(f"unsupported exact finite abelian group: {group.name}")
    if len(group.elements) != len(group.characters):
        raise ValueError("finite abelian character table must be square")
    if tuple(sorted(group.elements)) != group.elements:
        raise ValueError("group elements must be deterministically sorted")
    if tuple(sorted(group.characters)) != group.characters:
        raise ValueError("characters must be deterministically sorted")


def validate_character_table(group: FiniteAbelianGroup) -> None:
    """Check exact row and column orthogonality for supported groups."""

    validate_supported_group(group)
    for left in group.characters:
        for right in group.characters:
            expected = group.order if left == right else 0
            if row_inner_product(group, left, right) != expected:
                raise ValueError("character row orthogonality failed")
    for left in group.elements:
        for right in group.elements:
            expected = group.order if left == right else 0
            if column_inner_product(group, left, right) != expected:
                raise ValueError("character column orthogonality failed")


def certificate_payload(group: FiniteAbelianGroup) -> dict[str, object]:
    """Return deterministic JSON-ready character-data certificate payload."""

    validate_character_table(group)
    table = character_table(group)
    return {
        "schema": "twisted-yetter.finite-abelian-character-data.v1",
        "status": "pass",
        "node_id": "n11-finite-a-character-data",
        "group": {
            "name": group.name,
            "invariant_factors": list(group.invariant_factors),
            "order": group.order,
            "elements": [_element_label(element) for element in group.elements],
            "characters": [
                _character_label(character) for character in group.characters
            ],
        },
        "character_table": {
            _character_label(character): {
                _element_label(element): to_jsonable(table[character][element])
                for element in group.elements
            }
            for character in group.characters
        },
    }


def _check_element(group: FiniteAbelianGroup, element: GroupElement) -> None:
    if element not in group.elements:
        raise ValueError(f"unknown element for {group.name}: {element!r}")


def _check_character(group: FiniteAbelianGroup, character: CharacterLabel) -> None:
    if character not in group.characters:
        raise ValueError(f"unknown character for {group.name}: {character!r}")


def _element_label(element: GroupElement) -> str:
    if element == ():
        return "e"
    return ",".join(str(coordinate) for coordinate in element)


def _character_label(character: CharacterLabel) -> str:
    if character == ():
        return "trivial"
    if all(coordinate == 0 for coordinate in character):
        return "chi_0"
    return "chi_" + "_".join(str(coordinate) for coordinate in character)


for _group in (TRIVIAL_GROUP, Z2_GROUP):
    validate_character_table(_group)
