"""Draft builder for Gompf-Stipsicz Figure 8.15 Morse inputs.

This is transcription/rendering infrastructure only.  The generated Morse
forms are active-order consistent but are not yet verified against the printed
Kirby diagram.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    from experiments.scripts.morse_dsl import MorseBuilder
except ModuleNotFoundError:  # Direct script execution from experiments/scripts.
    from morse_dsl import MorseBuilder


def l_components(wheel_count: int) -> list[str]:
    return [f"L{i}" for i in range(1, wheel_count + 1)]


def r_components(wheel_count: int) -> list[str]:
    return [f"R{i}" for i in range(1, wheel_count + 1)]


def add_hard_weave(builder: MorseBuilder, wheel_count: int) -> None:
    """Add the 100-intersection hard weaving block.

    Pattern from the working draft:

    - R_i.left moves left over L_i.right, ..., L_10.right.
    - L_i.right moves right over R_{i+1}.left, ..., R_10.left.

    The second family is empty for i=10, giving
    10 + 2*(9+...+1) = 100 crossings.
    """
    for i in range(1, wheel_count + 1):
        builder.over_left(f"R{i}.left", times=wheel_count + 1 - i)
        if i < wheel_count:
            builder.over_right(f"L{i}.right", times=wheel_count - i)


def add_easy_weave_and_exit(builder: MorseBuilder, wheel_count: int) -> None:
    """Add the provisional 140-intersection easy weaving + exit block.

    Working interpretation of the draft:

    - L_m.right, ..., L_1.right each moves left over m+2 current strands.
    - R_10.left, ..., R_1.left each moves right over 2 current strands.

    This is deliberately state-dependent; if the active order disagrees with
    the intended picture, the builder will fail or the trace will expose it.
    """
    for i in range(wheel_count, 0, -1):
        builder.over_left(f"L{i}.right", times=wheel_count + 2)
    for i in range(wheel_count, 0, -1):
        builder.over_right(f"R{i}.left", times=2)


def add_left_full_twist(builder: MorseBuilder, wheel_count: int) -> None:
    """Add the draft L-family -1 full twist block."""
    for i in range(wheel_count, 0, -1):
        builder.over_left(f"L{i}.left", times=wheel_count - 1)


def add_left_component_framings(builder: MorseBuilder, wheel_count: int, self_twist: int) -> None:
    """Add the extra negative self twist/framing data on each L component."""
    for i in range(1, wheel_count + 1):
        builder.kink(f"L{i}.left", sign="-", times=self_twist)


def add_left_close(builder: MorseBuilder, wheel_count: int) -> None:
    """Close L_10, ..., L_1 as drafted."""
    for i in range(wheel_count, 0, -1):
        builder.cap(f"L{i}")


def add_right_full_twist(builder: MorseBuilder, wheel_count: int) -> None:
    """Add the draft R-family -1 full twist block."""
    for i in range(1, wheel_count + 1):
        builder.over_left(f"R{i}.right", times=wheel_count - 1)


def add_right_component_framings(builder: MorseBuilder, wheel_count: int, self_twist: int) -> None:
    """Add the extra negative self twist/framing data on each R component."""
    for i in range(1, wheel_count + 1):
        builder.kink(f"R{i}.right", sign="-", times=self_twist)


def add_right_close(builder: MorseBuilder, wheel_count: int) -> None:
    """Close R_10, ..., R_1 as drafted."""
    for i in range(wheel_count, 0, -1):
        builder.cap(f"R{i}")


def add_a_component_framing_correction(builder: MorseBuilder) -> None:
    """Add A's -3 self twist from the current Figure 8.15 transcription."""
    builder.kink("A1.left", sign="-", times=3)


def add_final_caps(builder: MorseBuilder) -> None:
    """Add the final three A caps from the working draft."""
    builder.cap(strands=("A1.left", "A3.left"))
    builder.cap(strands=("A2.right", "A1.right"))
    builder.cap(strands=("A2.left", "A3.right"))


def figure_parameter_n(wheel_count: int) -> int:
    """Recover Figure 8.15's n from the wheel count 6n-2."""
    quotient, remainder = divmod(wheel_count + 2, 6)
    if remainder or quotient < 1:
        raise ValueError("wheel_count must have the Figure 8.15 form 6n-2")
    return quotient


def build_checkable_prefix(
    *,
    wheel_count: int = 10,
    component_self_twist: int = 2,
    b_framing: int | None = None,
) -> MorseBuilder:
    """Build the currently checkable draft transcription."""
    if b_framing is None:
        b_framing = figure_parameter_n(wheel_count)
    m = MorseBuilder()

    m.cup("A1", at="far-left")
    m.cup("A2", between=("A1.left", "A1.right"))
    m.cup("A3", between=("A2.right", "A1.right"))
    m.cup("B", at="far-right")

    m.over_left("B.left", under=("A1.right",))
    m.over_right("A1.right", under=("B.right",))
    m.kink("B.left", sign="-", times=b_framing)
    m.cap("B")
    m.over_left("A1.right", under=("A3.right",))

    m.nested_cups(l_components(wheel_count), between=("A1.left", "A2.left"))

    m.over_right("A1.left", under=tuple(f"L{i}.left" for i in range(1, wheel_count + 1)))
    m.over_left("A2.left", under=tuple(f"L{i}.right" for i in range(1, wheel_count + 1)))
    m.over_left("A2.left", under=("A1.left",))

    m.nested_cups(r_components(wheel_count), between=("A2.right", "A3.left"))

    m.over_right("A2.right", under=tuple(f"R{i}.left" for i in range(1, wheel_count + 1)))
    m.over_left("A3.left", under=tuple(f"R{i}.right" for i in range(1, wheel_count + 1)))
    m.over_left("A3.left", under=("A2.right",))

    add_hard_weave(m, wheel_count)
    add_easy_weave_and_exit(m, wheel_count)
    add_left_full_twist(m, wheel_count)
    add_left_component_framings(m, wheel_count, component_self_twist)
    add_left_close(m, wheel_count)
    add_right_full_twist(m, wheel_count)
    add_right_component_framings(m, wheel_count, component_self_twist)
    add_right_close(m, wheel_count)
    add_a_component_framing_correction(m)
    add_final_caps(m)

    return m


def write_snapshot(
    path: Path,
    *,
    wheel_count: int = 10,
    component_self_twist: int = 2,
    b_framing: int | None = None,
    name: str = "K3/E(2)",
) -> Path:
    if b_framing is None:
        b_framing = figure_parameter_n(wheel_count)
    builder = build_checkable_prefix(
        wheel_count=wheel_count,
        component_self_twist=component_self_twist,
        b_framing=b_framing,
    )
    payload = {
        "schema": "twisted-yetter.morse-dsl.expanded-prefix.v1",
        "status": "DRAFT_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM",
        "source": f"Gompf-Stipsicz Figure 8.15 {name} hand transcription draft",
        "parameters": {
            "wheel_count": wheel_count,
            "component_self_twist": -component_self_twist,
            "b_framing": -b_framing,
            "a_self_twist": -3,
        },
        "notes": [
            f"This is a draft Morse transcription of the {name} Figure 8.15-style diagram.",
            "The transcription is active-order consistent, but it is not yet a mathematical proof of agreement with the printed diagram.",
            "This artifact is input/rendering infrastructure, not a link or Crane-Yetter evaluator.",
            f"The B component has the Figure 8.15 framing -n = -{b_framing}.",
            f"Each L_i and R_i carries an added -{component_self_twist} self twist/framing datum.",
            "Component A is currently recorded with a -3 self twist in this draft transcription.",
        ],
        **builder.snapshot(),
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write",
        type=Path,
        default=Path("/tmp/k3-figure815-morse-prefix-expanded-v1.json"),
        help="Path for expanded fundamental-form JSON.",
    )
    parser.add_argument("--wheel-count", type=int, default=10)
    parser.add_argument("--component-self-twist", "--self-twist", type=int, default=2)
    parser.add_argument("--b-framing", type=int)
    parser.add_argument("--name", default="K3/E(2)")
    args = parser.parse_args()
    print(
        write_snapshot(
            args.write,
            wheel_count=args.wheel_count,
            component_self_twist=args.component_self_twist,
            b_framing=args.b_framing,
            name=args.name,
        ).resolve()
    )


if __name__ == "__main__":
    main()
