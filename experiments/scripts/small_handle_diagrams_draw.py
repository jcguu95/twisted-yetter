#!/usr/bin/env python3
"""Draw concrete SVG fixtures for small special-handle Kirby candidates."""

from __future__ import annotations

import argparse
from html import escape
from pathlib import Path
import sys
import time
from typing import Any, Mapping, Sequence

from twisted_yetter.artifacts import (
    LogReference,
    default_tool_versions,
    dumps_certificate,
    file_sha256,
    git_metadata,
    hash_bytes,
    make_certificate,
    utc_now_iso,
)
from twisted_yetter.small_handle_examples import analyze_catalog, load_catalog


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_INPUT = (
    REPO_ROOT
    / "experiments/inputs/small-handle-examples/special-handle-catalog-v1.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments/results/small-handle-examples/kirby-diagram-svg-manifest-v1.json"
)
DEFAULT_DIAGRAM_DIR = (
    REPO_ROOT / "experiments/results/small-handle-examples/diagrams-v1"
)
DIAGRAM_SCHEMA = "twisted-yetter.small-special-handle-kirby-svg-diagrams.v1"


COLORS = [
    "#2563eb",
    "#dc2626",
    "#059669",
    "#7c3aed",
    "#d97706",
    "#0891b2",
]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--diagram-dir", type=Path, default=DEFAULT_DIAGRAM_DIR)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)

    started = utc_now_iso()
    start_monotonic = time.monotonic()
    payload = load_catalog(args.input)
    analysis = analyze_catalog(payload)
    exact_output, svg_texts = build_manifest(payload, analysis, args.diagram_dir)
    finished = utc_now_iso()

    if args.write:
        args.diagram_dir.mkdir(parents=True, exist_ok=True)
        for path, text in svg_texts.items():
            path.write_text(text)

    log_references = [
        LogReference(
            path=str(path.relative_to(REPO_ROOT)),
            sha256=hash_bytes(text.encode()),
            bytes=len(text.encode()),
            description="generated SVG Kirby diagram fixture",
        )
        for path, text in sorted(svg_texts.items())
    ]
    command = (
        "PYTHONPATH=src python experiments/scripts/"
        "small_handle_diagrams_draw.py --write"
    )
    certificate = make_certificate(
        status="pass" if analysis["status"] == "pass" else "fail",
        command=command,
        argv=sys.argv[1:],
        git=git_metadata(REPO_ROOT),
        tool_versions=default_tool_versions(),
        input_hash=file_sha256(args.input.resolve()),
        exact_output=exact_output,
        generator_script="experiments/scripts/small_handle_diagrams_draw.py",
        reproduce_command=command,
        started_at_utc=started,
        finished_at_utc=finished,
        elapsed_seconds=time.monotonic() - start_monotonic,
        repo_root=str(REPO_ROOT),
        log_references=[item.to_json() for item in log_references],
        notes=[
            "Generated SVGs are concrete special-dotted Kirby diagram fixtures.",
            "They are not Kirby-slide recognition proofs and not RT evaluation outputs.",
        ],
    )
    text = dumps_certificate(certificate)
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")
    return 0 if analysis["status"] == "pass" else 1


def build_manifest(
    payload: Mapping[str, Any],
    analysis: Mapping[str, Any],
    diagram_dir: Path,
) -> tuple[dict[str, Any], dict[Path, str]]:
    analyses = {item["id"]: item for item in analysis["examples"]}
    diagrams: list[dict[str, Any]] = []
    svg_texts: dict[Path, str] = {}
    for example in payload["examples"]:
        svg_text = draw_example(example, analyses[example["id"]])
        path = diagram_dir / f"{example['id']}.svg"
        svg_hash = hash_bytes(svg_text.encode())
        svg_texts[path] = svg_text
        diagrams.append(
            {
                "example_id": example["id"],
                "path": str(path.relative_to(REPO_ROOT)),
                "sha256": svg_hash,
                "diagram_status": "CONCRETE_SVG_KIRBY_FIXTURE_NOT_SLIDE_PROOF",
                "handle_counts": analyses[example["id"]]["handle_counts"],
                "one_handles": list(example["one_handles"]),
                "two_handles": list(example["two_handles"]),
                "three_handles": list(example["three_handles"]),
                "d2_matrix_c2_to_c1": example["d2_matrix"],
                "d3_matrix_c3_to_c2": example["d3_matrix"],
                "q2_matrix": example["q2_matrix"],
            }
        )
    return (
        {
            "schema": DIAGRAM_SCHEMA,
            "status": "pass" if analysis["status"] == "pass" else "fail",
            "mathematical_status": (
                "KIRBY_DIAGRAM_FIXTURES_NOT_THEOREM_LEVEL_RECOGNITION"
            ),
            "claim_boundary": {
                "not_rt_evaluation": True,
                "not_closed_4d_invariant": True,
                "not_kirby_slide_proof": True,
                "purpose": (
                    "make every small special-handle algebra fixture visible "
                    "as a fixed dotted Kirby diagram input"
                ),
            },
            "catalog_id": payload["catalog_id"],
            "diagram_count": len(diagrams),
            "diagrams": diagrams,
        },
        svg_texts,
    )


def draw_example(example: Mapping[str, Any], analysis: Mapping[str, Any]) -> str:
    one_handles = list(example["one_handles"])
    two_handles = list(example["two_handles"])
    three_handles = list(example["three_handles"])
    d2 = _matrix(example["d2_matrix"])
    d3 = _matrix(example["d3_matrix"])
    q2 = _matrix(example["q2_matrix"])

    width = 980
    y_one = 150
    y_two_start = 300 if one_handles else 210
    two_gap = 84
    y_three_start = y_two_start + max(len(two_handles), 1) * two_gap + 70
    height = y_three_start + max(len(three_handles), 1) * 56 + 90
    one_positions = _spread_positions(len(one_handles), 180, width - 180)
    two_rows = [y_two_start + index * two_gap for index in range(len(two_handles))]

    parts = [
        _svg_header(width, height),
        _text(36, 42, example["id"], 20, "font-weight:700"),
        _text(
            36,
            72,
            "Concrete special-dotted Kirby fixture; not a Kirby-slide proof.",
            13,
            "fill:#475569",
        ),
        _text(36, 100, _handles_summary(one_handles, two_handles, three_handles), 13),
    ]

    if one_handles:
        for index, label in enumerate(one_handles):
            x = one_positions[index]
            parts.extend(
                [
                    f'<circle cx="{x}" cy="{y_one}" r="42" fill="none" '
                    'stroke="#111827" stroke-width="2.5" stroke-dasharray="2 7"/>',
                    _text(x - 34, y_one + 68, f"dotted {label}", 13),
                ]
            )
    else:
        parts.append(_text(36, 150, "no dotted one-handles", 13, "fill:#475569"))

    for index, label in enumerate(two_handles):
        color = COLORS[index % len(COLORS)]
        y = two_rows[index]
        incidence = [d2[row][index] for row in range(len(one_handles))]
        parts.extend(_two_handle_path(label, index, y, color, one_positions, incidence, q2[index][index]))

    parts.extend(_pairing_marks(two_handles, q2, two_rows))

    if three_handles:
        for index, label in enumerate(three_handles):
            relation = [d3[row][index] for row in range(len(two_handles))]
            y = y_three_start + index * 56
            parts.extend(_three_handle_box(label, relation, two_handles, y))
    else:
        parts.append(_text(36, y_three_start, "no 3-handle relations", 13, "fill:#475569"))

    parts.extend(
        [
            _text(36, height - 48, f"H2 form {analysis['forms']['q_on_h2_quotient_basis']}", 13),
            _text(36, height - 26, f"Z2 characters {analysis['z2_character_cohomology']['h2_character_count']}", 13),
            "</svg>\n",
        ]
    )
    return "\n".join(parts)


def _two_handle_path(
    label: str,
    index: int,
    y: int,
    color: str,
    one_positions: Sequence[int],
    incidence: Sequence[int],
    framing: int,
) -> list[str]:
    parts: list[str] = []
    x_left = 78
    x_right = 902
    parts.append(
        f'<path d="M {x_left} {y} C 150 {y - 58}, 260 {y - 58}, 330 {y} '
        f'C 455 {y + 72}, 615 {y + 72}, {x_right} {y}" '
        f'fill="none" stroke="{color}" stroke-width="3.2" stroke-linecap="round"/>'
    )
    parts.append(
        f'<path d="M {x_right} {y} C 830 {y + 88}, 180 {y + 88}, {x_left} {y}" '
        f'fill="none" stroke="{color}" stroke-width="2.4" stroke-linecap="round" '
        'stroke-opacity="0.78"/>'
    )
    parts.append(
        f'<rect x="{x_left - 20}" y="{y - 18}" width="96" height="36" rx="6" '
        'fill="#ffffff" stroke="#cbd5e1"/>'
    )
    parts.append(_text(x_left - 10, y + 5, f"{label}, fr {framing}", 13, f"fill:{color};font-weight:700"))

    if one_positions:
        for one_index, incidence_number in enumerate(incidence):
            if incidence_number == 0:
                continue
            x = one_positions[one_index]
            direction = 1 if incidence_number > 0 else -1
            pass_y = 150 + (index - len(incidence) // 2) * 8
            y_offset = 18 * direction
            parts.append(
                f'<path d="M {x - 55} {pass_y} C {x - 20} {pass_y - y_offset}, '
                f'{x + 20} {pass_y + y_offset}, {x + 55} {pass_y}" '
                f'fill="none" stroke="{color}" stroke-width="3" stroke-linecap="round"/>'
            )
            multiplicity = abs(incidence_number)
            suffix = f" x{multiplicity}" if multiplicity != 1 else ""
            parts.append(_text(x - 26, pass_y - 50, f"{label}{suffix}", 12, f"fill:{color}"))
    else:
        parts.append(
            f'<ellipse cx="492" cy="{y + 20}" rx="{130 + 10 * index}" ry="34" '
            f'fill="none" stroke="{color}" stroke-width="2.2" stroke-opacity="0.6"/>'
        )
    return parts


def _pairing_marks(
    two_handles: Sequence[str],
    q2: Sequence[Sequence[int]],
    two_rows: Sequence[int],
) -> list[str]:
    parts: list[str] = []
    for i in range(len(two_handles)):
        for j in range(i + 1, len(two_handles)):
            linking = q2[i][j]
            if linking == 0:
                continue
            x = 850 - 34 * (j - i)
            y1 = two_rows[i] + 18
            y2 = two_rows[j] - 18
            parts.append(
                f'<path d="M {x} {y1} C {x + 42} {(y1 + y2) // 2}, '
                f'{x - 42} {(y1 + y2) // 2}, {x} {y2}" '
                'fill="none" stroke="#334155" stroke-width="1.8" '
                'stroke-dasharray="5 5"/>'
            )
            parts.append(
                _text(
                    x + 12,
                    (y1 + y2) // 2,
                    f"lk({two_handles[i]},{two_handles[j]})={linking}",
                    12,
                    "fill:#334155",
                )
            )
    return parts


def _three_handle_box(
    label: str,
    relation: Sequence[int],
    two_handles: Sequence[str],
    y: int,
) -> list[str]:
    relation_text = _format_relation(relation, two_handles)
    return [
        f'<rect x="64" y="{y - 24}" width="852" height="42" rx="8" '
        'fill="#f8fafc" stroke="#64748b" stroke-dasharray="6 5"/>',
        _text(84, y + 3, f"3-handle {label}: {relation_text}", 13, "fill:#334155"),
    ]


def _format_relation(relation: Sequence[int], two_handles: Sequence[str]) -> str:
    terms = []
    for coefficient, label in zip(relation, two_handles, strict=True):
        if coefficient == 0:
            continue
        sign = "+" if coefficient > 0 else "-"
        magnitude = abs(coefficient)
        body = label if magnitude == 1 else f"{magnitude}{label}"
        if not terms:
            terms.append(body if coefficient > 0 else f"-{body}")
        else:
            terms.append(f"{sign} {body}")
    return " ".join(terms) + " = 0" if terms else "0 = 0"


def _spread_positions(count: int, left: int, right: int) -> list[int]:
    if count == 0:
        return []
    if count == 1:
        return [(left + right) // 2]
    step = (right - left) / (count - 1)
    return [round(left + index * step) for index in range(count)]


def _handles_summary(
    one_handles: Sequence[str],
    two_handles: Sequence[str],
    three_handles: Sequence[str],
) -> str:
    return (
        f"1-handles {list(one_handles)}; "
        f"2-handles {list(two_handles)}; "
        f"3-handles {list(three_handles)}"
    )


def _matrix(rows: Sequence[Sequence[Any]]) -> list[list[int]]:
    return [[int(value) for value in row] for row in rows]


def _text(x: int, y: int, text: str, size: int, style: str = "") -> str:
    return (
        f'<text x="{x}" y="{y}" font-family="Arial, Helvetica, sans-serif" '
        f'font-size="{size}" style="{style}">{escape(text)}</text>'
    )


def _svg_header(width: int, height: int) -> str:
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">\n'
        '<rect width="100%" height="100%" fill="#ffffff"/>'
    )


if __name__ == "__main__":
    raise SystemExit(main())
