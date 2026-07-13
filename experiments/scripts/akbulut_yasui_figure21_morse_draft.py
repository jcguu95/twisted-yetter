"""User-transcribed Morse input for Akbulut--Yasui Figure 21 (right).

The transcription is a draft research input.  Internal topology checks do
not by themselves prove that it agrees with the printed Kirby diagram.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

from experiments.scripts.morse_dsl import MorseBuilder


SOURCE_REF = "subject:twisted-yetter:paper:akbulut-yasui-0806-3010"
SOURCE_LOCATOR = "Figure 21, right"
STATUS = "DRAFT_USER_TRANSCRIPTION_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM"

COMPONENT_BY_PIECE = {
    "red1": "red",
    "purple1": "purple",
    "purple2": "purple",
    "mint1": "mint",
    "mint2": "mint",
    "pink1": "pink1",
    "pink2": "pink2",
    "pink3": "pink3",
    "pink4": "pink4",
    **{f"orange{i}": "orange" for i in range(1, 7)},
    **{f"blue{i}": "blue" for i in range(1, 8)},
    "beige1": "beige",
    "green1": "green",
    "black1": "black",
}

COMPONENT_ORDER = [
    "red",
    "purple",
    "mint",
    "pink1",
    "pink2",
    "pink3",
    "pink4",
    "orange",
    "blue",
    "beige",
    "green",
    "black",
]

FRAMING_LABELS = {
    "red": 0,
    "purple": -5,
    "mint": -1,
    "pink1": -2,
    "pink2": -2,
    "pink3": -2,
    "pink4": -2,
    "orange": 1,
    "blue": -1,
    "beige": 4,
    "green": 2,
    "black": -1,
}


def _repeat_full_twist(
    builder: MorseBuilder, *, start: str, end: str, sign: str, times: int
) -> None:
    for _ in range(times):
        builder.full_twist(start=start, end=end, direction="left", sign=sign)


def build_figure21_right() -> MorseBuilder:
    m = MorseBuilder()

    m.cup("red1", at="far-left")
    m.cup("purple1", at="far-right")
    _repeat_full_twist(
        m, start="red1.right", end="purple1.left", sign="-", times=4
    )

    m.cup("mint1", between=("purple1.left", "purple1.right"))
    m.cup("mint2", between=("mint1.left", "mint1.right"))
    m.over_left("mint1.left", under=("purple1.left", "red1.right"))
    m.under_left("mint2.left", over=("purple1.left", "red1.right"))

    m.cup("pink1", between=("red1.left", "mint1.left"))
    m.cup("pink2", between=("red1.left", "pink1.left"))
    m.cup("pink3", between=("red1.left", "pink2.left"))
    m.cup("pink4", between=("red1.left", "pink3.left"))
    _repeat_full_twist(
        m, start="pink2.right", end="pink1.left", sign="-", times=1
    )
    _repeat_full_twist(
        m, start="pink3.right", end="pink2.left", sign="-", times=1
    )
    _repeat_full_twist(
        m, start="pink4.right", end="pink3.left", sign="-", times=1
    )
    m.cap("pink2")
    m.cap("pink3")
    m.cap("pink4")
    m.under_right("pink1.right", over=("mint1.left",))
    m.over_right("pink1.right", under=("mint2.left",))
    m.cap(strands=("mint1.left", "mint2.left"))
    m.cap("pink1")

    m.cup("purple2", between=("purple1.left", "mint2.right"))
    m.nested_cups(
        [f"orange{i}" for i in range(1, 7)],
        between=("purple2.left", "purple2.right"),
    )
    m.over_left(
        "orange1.left",
        under=("purple2.left", "purple1.left", "red1.right"),
    )
    m.over_left("orange2.left", under=("purple2.left",))
    m.under_left("orange2.left", over=("purple1.left", "red1.right"))
    m.cap(strands=("purple1.left", "purple2.left"))
    m.over_left("orange3.left", under=("red1.right",))
    m.under_left("orange4.left", over=("red1.right",))
    m.over_left("orange5.left", under=("red1.right",))
    m.under_left("orange6.left", over=("red1.right",))
    m.cap(strands=("orange2.left", "orange3.left"))
    m.cap(strands=("orange4.left", "orange5.left"))

    m.nested_cups(
        [f"blue{i}" for i in range(1, 7)],
        between=("red1.right", "orange6.right"),
    )
    m.under_left("blue1.left", over=("red1.right",))
    m.under_left("blue2.left", over=("red1.right",))
    m.over_left("blue3.left", under=("red1.right",))
    m.over_left("blue4.left", under=("red1.right",))
    m.cap(strands=("blue2.left", "blue3.left"))
    m.cap(strands=("blue1.left", "blue4.left"))
    for blue in ("blue5.left", "blue6.left"):
        m.under_left(blue, over=("red1.right",))
        m.over_left(blue, under=("orange6.left",))
        m.under_left(blue, over=("orange1.left",))
    m.cap(strands=("orange1.left", "orange6.left"))

    m.cup("green1", between=("red1.right", "blue6.right"))
    m.cup("beige1", between=("blue6.left", "red1.right"))
    _repeat_full_twist(
        m, start="beige1.right", end="green1.left", sign="+", times=3
    )
    m.cup("black1", between=("green1.left", "green1.right"))
    m.over_left(
        "black1.left", under=("green1.left", "red1.right", "beige1.right")
    )
    m.under_left(
        "black1.right", over=("green1.left", "red1.right", "beige1.right")
    )
    m.cap("black1")
    _repeat_full_twist(
        m, start="beige1.right", end="red1.right", sign="+", times=2
    )
    m.cap("beige1")
    m.cup("blue7", between=("red1.right", "green1.left"))
    m.under_left("blue7.left", over=("red1.right",))
    m.over_left("blue7.right", under=("red1.right",))
    m.cap(strands=("blue6.left", "blue7.left"))
    m.cap(strands=("blue5.left", "blue7.right"))
    m.under_left("green1.left", over=("red1.right", "red1.left"))
    m.under_left("green1.right", over=("red1.right",))
    m.over_left("green1.right", under=("red1.left",))
    m.cap("green1")

    m.under_left("blue6.right", times=2)
    m.under_left("blue5.right", times=2)
    for blue in ("blue4.right", "blue3.right", "blue2.right"):
        m.under_left(blue, times=1)
        m.over_left(blue, times=1)
    m.under_left("blue1.right", times=2)
    m.cap(strands=("blue5.right", "blue4.right"))
    m.cap(strands=("blue6.right", "blue3.right"))
    m.cap(strands=("blue2.right", "blue1.right"))

    m.under_left("orange6.right", times=2)
    m.under_left("orange5.right", times=1)
    m.over_left("orange5.right", times=1)
    m.under_left("orange4.right", times=2)
    m.under_left("orange3.right", times=1)
    m.over_left("orange3.right", times=1)
    m.under_left("orange2.right", times=2)
    m.under_left("orange1.right", times=1)
    m.over_left("orange1.right", times=1)
    m.cap(strands=("orange6.right", "orange5.right"))
    m.cap(strands=("orange4.right", "orange3.right"))
    m.cap(strands=("orange2.right", "orange1.right"))

    m.under_left("purple2.right", times=2)
    m.under_left("mint2.right", times=2)
    m.under_left("mint1.right", times=1)
    m.over_left("mint1.right", times=1)
    m.under_left("purple1.right", times=1)
    m.over_left("purple1.right", times=1)
    m.cap(strands=("mint2.right", "mint1.right"))
    m.cap(strands=("purple2.right", "purple1.right"))
    m.cap("red1")
    if m.order:
        raise AssertionError(f"nonempty final order: {m.order!r}")
    return m


def payload() -> dict:
    builder = build_figure21_right()
    return {
        "schema": "twisted-yetter.morse-dsl.input.v1",
        "status": STATUS,
        "source_ref": SOURCE_REF,
        "source_locator": SOURCE_LOCATOR,
        "special_components": ["red"],
        "component_order": COMPONENT_ORDER,
        "component_by_piece": COMPONENT_BY_PIECE,
        "framing_labels": FRAMING_LABELS,
        "forms": builder.forms,
        "trace": builder.trace,
        "final_order": builder.order,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    generated = payload()
    repo = Path(__file__).resolve().parents[2]
    generated.update(
        {
            "generator_script": str(Path(__file__).resolve().relative_to(repo)),
            "reproduce_command": (
                "PYTHONPATH=. uv run python "
                "experiments/scripts/akbulut_yasui_figure21_morse_draft.py "
                f"--output {args.output}"
                if args.output
                else "PYTHONPATH=. uv run python experiments/scripts/"
                "akbulut_yasui_figure21_morse_draft.py"
            ),
            "generated_at": datetime.now(timezone.utc)
            .replace(microsecond=0)
            .isoformat()
            .replace("+00:00", "Z"),
            "repo_root": str(repo),
            "git_commit": subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repo, text=True
            ).strip(),
            "git_dirty": bool(
                subprocess.check_output(
                    ["git", "status", "--porcelain"], cwd=repo, text=True
                ).strip()
            ),
        }
    )
    encoded = json.dumps(generated, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
