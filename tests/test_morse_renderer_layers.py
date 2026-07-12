from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.render_morse_svg import (
    StableLayout,
    cap_piece,
    cup_piece,
    dependency_layers,
    scheduled_replay_layers,
)


def test_dependency_scheduler_aligns_parallel_nested_chains():
    m = MorseBuilder()
    m.cup("A1", at="far-left")
    m.cup("A2", between=("A1.left", "A1.right"))
    m.cup("A3", between=("A2.right", "A1.right"))
    m.nested_cups(["L1", "L2"], between=("A1.left", "A2.left"))
    m.nested_cups(["R1", "R2"], between=("A2.right", "A3.left"))
    m.cap("L2")
    m.cap("L1")
    m.cap("R2")
    m.cap("R1")

    layout = StableLayout(m.trace, margin=90.0, step=24.0, layout_mode="unoptimized")
    layers = dependency_layers(layout.rows)
    row_to_layer = {id(row): i for i, layer in enumerate(layers) for row in layer}
    cup_layers = {}
    cap_layers = {}
    for row in layout.rows:
        piece = cup_piece(row["form"])
        if piece is not None:
            cup_layers[piece] = row_to_layer[id(row)]
        piece = cap_piece(row["form"])
        if piece is not None:
            cap_layers[piece] = row_to_layer[id(row)]

    assert cup_layers["L1"] == cup_layers["R1"]
    assert cup_layers["L2"] == cup_layers["R2"]
    assert cup_layers["L1"] < cup_layers["L2"]
    assert cap_layers["L2"] == cap_layers["R2"]
    assert cap_layers["L1"] == cap_layers["R1"]
    assert cap_layers["L2"] < cap_layers["L1"]


def test_scheduled_replay_recomputes_states_after_reordering():
    m = MorseBuilder()
    m.cup("A1", at="far-left")
    m.cup("A2", between=("A1.left", "A1.right"))
    m.cup("A3", between=("A2.right", "A1.right"))
    m.nested_cups(["L1", "L2"], between=("A1.left", "A2.left"))
    m.nested_cups(["R1", "R2"], between=("A2.right", "A3.left"))
    m.cap("L2")
    m.cap("L1")
    m.cap("R2")
    m.cap("R1")
    m.cap(strands=("A1.left", "A2.left"))
    m.cap(strands=("A2.right", "A3.left"))
    m.cap(strands=("A1.right", "A3.right"))

    layout = StableLayout(m.trace, margin=90.0, step=24.0, layout_mode="unoptimized")
    layers, _ = scheduled_replay_layers(
        layout.rows,
        cup_widths=layout.cup_widths,
        margin=90.0,
        step=24.0,
    )

    assert layers[-1][-1]["after"] == []
