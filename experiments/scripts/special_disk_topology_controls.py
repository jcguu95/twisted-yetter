"""Small category-independent topology controls for special-disk lifts."""

from __future__ import annotations

from experiments.scripts.morse_dsl import MorseBuilder


EXPECTED_TAU_VACUUM_RANKS = {1: 0, 2: 1, 3: 1, 4: 2, 5: 3, 6: 5}


def build_hopf_star(valence: int) -> tuple[tuple[dict, ...], dict[str, str]]:
    """Return one special red unknot Hopf-linked with ``valence`` unknots."""

    if valence < 1:
        raise ValueError("Hopf-star valence must be positive")
    builder = MorseBuilder()
    ordinary = [f"C{index}" for index in range(1, valence + 1)]
    builder.cup(ordinary[0], at="far-left")
    for previous, component in zip(ordinary, ordinary[1:]):
        builder.cup(
            component,
            between=(f"{previous}.left", f"{previous}.right"),
        )
    builder.cup("red1", at="far-right")
    for component in ordinary:
        builder.cross(over=f"{component}.right", under="red1.left")
    for component in reversed(ordinary):
        builder.cross(over="red1.left", under=f"{component}.right")
    builder.cap("red1")
    for component in reversed(ordinary):
        builder.cap(component)
    if builder.order:
        raise AssertionError(
            f"Hopf-star builder left active strands: {builder.order!r}"
        )
    component_by_piece = {component: component for component in ordinary}
    component_by_piece["red1"] = "red"
    return tuple(builder.forms), component_by_piece


def build_hopf_winding(punctures: int) -> tuple[tuple[dict, ...], dict[str, str]]:
    """Return one ordinary circle passing through the red disk repeatedly."""

    if punctures < 1:
        raise ValueError("Hopf-winding puncture count must be positive")
    builder = MorseBuilder()
    builder.cup("C1", at="far-left")
    builder.cup("red1", at="far-right")
    for _index in range(punctures):
        builder.cross(over="C1.right", under="red1.left")
        builder.cross(over="red1.left", under="C1.right")
    builder.cap("red1")
    builder.cap("C1")
    if builder.order:
        raise AssertionError(
            f"Hopf-winding builder left active strands: {builder.order!r}"
        )
    return tuple(builder.forms), {"C1": "C1", "red1": "red"}
