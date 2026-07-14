#!/usr/bin/env python3
"""Recover the framed Figure 21 ledger from the frozen blackboard run.

The expensive fixed-label contractions at commit 30d00ff omitted the total
Kirby framings.  Framing changes act diagonally in the simple-label basis, so
those contractions can be recovered sector by sector by the ribbon twist
phase without repeating any tensor contraction.
"""

from __future__ import annotations

import argparse
from collections import Counter
import cmath
from datetime import UTC, datetime
import gzip
import hashlib
import json
import math
from pathlib import Path
import platform
import socket
import subprocess
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_INPUT = (
    REPO_ROOT
    / "experiments/inputs/akbulut-yasui/figure21-right-morse-draft-v1.json"
)
EXPECTED_INPUT_SHA256 = (
    "b6f8459547a7cec415eb6c70acb89a40c37ab4cabd364330206685d8e579cbc5"
)
EXPECTED_SOURCE_LEDGER_SHA256 = (
    "9cb126f76f23932b159d2dac0e88c2522087c60af9e32c38d2957e02a6b3714f"
)
EXPECTED_SOURCE_EVALUATION_ID = (
    "sha256:1a23fccc262f3f523a686254c8e0553925c903169688b76afc9d12ca9116b1f2"
)
EXPECTED_COMPONENT_ORDER = (
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
)
EXPECTED_STANDARD_VALUE = -1024.0 + 0.0j
MATCH_TOLERANCE = 1e-8
SUMMATION_ORDER_TOLERANCE = 1e-10
NUMERIC_ZERO_TOLERANCE = 1e-13


def utc_now() -> str:
    return datetime.now(UTC).isoformat()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def stable_hash(value: Any) -> str:
    return "sha256:" + sha256_bytes(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    )


def complex_json(value: complex) -> list[float]:
    return [float(value.real), float(value.imag)]


def visible_self_writhe(source_input: dict[str, Any]) -> dict[str, int]:
    component_by_piece = source_input["component_by_piece"]

    def component(strand: str) -> str:
        return component_by_piece[strand.rsplit(".", 1)[0]]

    writhe = Counter()
    for form in source_input["forms"]:
        if form["kind"] == "cross":
            over = component(form["over"])
            under = component(form["under"])
            if over == under:
                writhe[over] += int(form["sign"])
        elif form["kind"] == "kink":
            sign = 1 if form["sign"] == "+" else -1
            writhe[component(form["strand"])] += sign * int(
                form.get("times", 1)
            )
    return dict(writhe)


def su2_k2_twists() -> dict[int, complex]:
    return {
        label: cmath.exp(
            2j * math.pi * label * (label + 2) / (4 * (2 + 2))
        )
        for label in (0, 1, 2)
    }


def sector_framing_phase(
    labels: Iterable[int],
    component_order: Iterable[str],
    framing_corrections: dict[str, int],
    twists: dict[int, complex],
) -> complex:
    labels = tuple(int(label) for label in labels)
    components = tuple(component_order)
    if len(labels) != len(components):
        raise ValueError("sector labels do not match component order")
    phase = 1.0 + 0.0j
    for component, label in zip(components, labels, strict=True):
        if label not in twists:
            raise ValueError(f"unsupported SU(2)_2 label {label!r}")
        phase *= twists[label] ** int(framing_corrections[component])
    return phase


def _framed_status(value: complex) -> str:
    if value == 0.0 + 0.0j:
        return "EVALUATED_EXACT_ZERO"
    if abs(value) <= NUMERIC_ZERO_TOLERANCE:
        return "NUMERICALLY_SMALL"
    return "EVALUATED_NONZERO"


def reweight_record(
    source: dict[str, Any],
    *,
    component_order: tuple[str, ...],
    framing_corrections: dict[str, int],
    twists: dict[int, complex],
    evaluation_id: str,
) -> dict[str, Any]:
    record = dict(source)
    if "evaluation_id" not in source:
        raise ValueError("source record lacks its inherited evaluation identity")
    record["source_evaluation_id"] = source["evaluation_id"]
    record["evaluation_id"] = evaluation_id
    if source["status"] == "PRUNED_NO_VACUUM":
        return record
    if "weighted_contribution" not in source or "raw_graph_scalar" not in source:
        raise ValueError(f"sector {source['sector_id']} lacks a source contribution")

    phase = sector_framing_phase(
        source["labels"], component_order, framing_corrections, twists
    )
    blackboard_raw = complex(*source["raw_graph_scalar"])
    blackboard_weighted = complex(*source["weighted_contribution"])
    framed_raw = phase * blackboard_raw
    framed_weighted = phase * blackboard_weighted
    record.update(
        {
            "blackboard_status": source["status"],
            "blackboard_raw_graph_scalar": source["raw_graph_scalar"],
            "blackboard_weighted_contribution": source["weighted_contribution"],
            "framing_phase": complex_json(phase),
            "framing_corrections": framing_corrections,
            "raw_graph_scalar": complex_json(framed_raw),
            "weighted_contribution": complex_json(framed_weighted),
            "imaginary_residual": abs(framed_raw.imag),
            "status": _framed_status(framed_raw),
        }
    )
    contributions = []
    for source_item in source.get("special_label_contributions", ()):
        item = dict(source_item)
        blackboard_source = complex(*source_item["source_value"])
        blackboard_weighted_source = complex(
            *source_item["weighted_source_value"]
        )
        item.update(
            {
                "blackboard_source_value": source_item["source_value"],
                "blackboard_weighted_source_value": source_item[
                    "weighted_source_value"
                ],
                "framing_phase": complex_json(phase),
                "source_value": complex_json(phase * blackboard_source),
                "weighted_source_value": complex_json(
                    phase * blackboard_weighted_source
                ),
            }
        )
        contributions.append(item)
    record["special_label_contributions"] = contributions
    return record


def _git_metadata(allow_dirty: bool) -> dict[str, Any]:
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True
    ).strip()
    status = subprocess.check_output(
        ["git", "status", "--short"], cwd=REPO_ROOT, text=True
    ).splitlines()
    if status and not allow_dirty:
        raise ValueError("framing recovery requires a clean git worktree")
    return {"commit": commit, "dirty": bool(status), "status_short": status}


def _relative_or_absolute(path: Path) -> str:
    path = path.resolve()
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def recover(args: argparse.Namespace) -> dict[str, Any]:
    started = utc_now()
    git = _git_metadata(args.allow_dirty)
    input_bytes = args.input.read_bytes()
    input_sha256 = sha256_bytes(input_bytes)
    if input_sha256 != EXPECTED_INPUT_SHA256:
        raise ValueError("Figure 21 frozen input hash changed")
    source_sha256 = sha256_file(args.source_ledger)
    if source_sha256 != EXPECTED_SOURCE_LEDGER_SHA256:
        raise ValueError("source blackboard ledger hash changed")
    source_input = json.loads(input_bytes)
    total_framings = {
        component: int(framing)
        for component, framing in source_input["framing_labels"].items()
    }
    visible = visible_self_writhe(source_input)
    framing_corrections = {
        component: total_framings[component] - visible.get(component, 0)
        for component in total_framings
    }
    if framing_corrections["red"] != 0:
        raise ValueError("special red component cannot receive a framing phase")
    twists = su2_k2_twists()
    generator_sha256 = sha256_file(Path(__file__))
    identity = {
        "schema": "twisted-yetter.figure21-su2-2-framing-recovery-identity.v1",
        "source_evaluation_id": EXPECTED_SOURCE_EVALUATION_ID,
        "source_ledger_sha256": source_sha256,
        "input_sha256": input_sha256,
        "category_id": "su2-k2",
        "component_order": list(EXPECTED_COMPONENT_ORDER),
        "total_framings": total_framings,
        "visible_self_writhe": visible,
        "framing_corrections": framing_corrections,
        "twists": {
            str(label): complex_json(value) for label, value in twists.items()
        },
        "generator_commit": git["commit"],
        "generator_sha256": generator_sha256,
    }
    evaluation_id = stable_hash(identity)
    source_contributions = []
    framed_contributions = []
    source_statuses = Counter()
    framed_statuses = Counter()
    args.output_ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger_tmp = args.output_ledger.with_suffix(args.output_ledger.suffix + ".tmp")
    record_count = 0
    with gzip.open(args.source_ledger, "rt") as source_handle:
        header = json.loads(source_handle.readline())
        if header.get("evaluation_id") != EXPECTED_SOURCE_EVALUATION_ID:
            raise ValueError("unexpected source evaluation id")
        if tuple(header.get("component_order", ())) != EXPECTED_COMPONENT_ORDER:
            raise ValueError("unexpected source component order")
        expected_count = int(header["sector_count"])
        with gzip.open(ledger_tmp, "wt") as output_handle:
            output_handle.write(
                json.dumps(
                    {
                        "record_kind": "header",
                        "schema": (
                            "twisted-yetter.figure21-su2-2-framed-sector-ledger.v1"
                        ),
                        "evaluation_id": evaluation_id,
                        "source_evaluation_id": EXPECTED_SOURCE_EVALUATION_ID,
                        "source_ledger_sha256": source_sha256,
                        "component_order": list(EXPECTED_COMPONENT_ORDER),
                        "sector_count": expected_count,
                        "framing_corrections": framing_corrections,
                    },
                    sort_keys=True,
                )
                + "\n"
            )
            for line in source_handle:
                source = json.loads(line)
                source_record_id = source.get("evaluation_id")
                if (
                    source_record_id is None
                    and source.get("status") == "PRUNED_NO_VACUUM"
                ):
                    source["evaluation_id"] = header["evaluation_id"]
                    source_record_id = source["evaluation_id"]
                if source_record_id != EXPECTED_SOURCE_EVALUATION_ID:
                    raise ValueError("mixed evaluation identities in source ledger")
                if source.get("sector_id") != record_count:
                    raise ValueError(
                        "source sectors are not complete and ordered exactly once"
                    )
                source_statuses[source["status"]] += 1
                record = reweight_record(
                    source,
                    component_order=EXPECTED_COMPONENT_ORDER,
                    framing_corrections=framing_corrections,
                    twists=twists,
                    evaluation_id=evaluation_id,
                )
                framed_statuses[record["status"]] += 1
                output_handle.write(
                    json.dumps(record, sort_keys=True, separators=(",", ":"))
                    + "\n"
                )
                if "weighted_contribution" in source:
                    source_contributions.append(
                        complex(*source["weighted_contribution"])
                    )
                    framed_contributions.append(
                        complex(*record["weighted_contribution"])
                    )
                record_count += 1
    if record_count != expected_count:
        raise ValueError(
            f"source ledger coverage mismatch: {record_count} != {expected_count}"
        )

    def compensated(values: list[complex]) -> complex:
        return complex(
            math.fsum(value.real for value in values),
            math.fsum(value.imag for value in values),
        )

    source_value = compensated(source_contributions)
    framed_value = compensated(framed_contributions)
    reverse_value = compensated(list(reversed(framed_contributions)))
    order_difference = abs(framed_value - reverse_value)
    absolute_difference = abs(framed_value - EXPECTED_STANDARD_VALUE)
    match = (
        order_difference <= SUMMATION_ORDER_TOLERANCE
        and absolute_difference <= MATCH_TOLERANCE
        and abs(framed_value.imag) <= MATCH_TOLERANCE
        and not framed_statuses.get("FAILED")
        and not framed_statuses.get("TIMEOUT")
    )

    ledger_tmp.replace(args.output_ledger)
    output_ledger_sha256 = sha256_file(args.output_ledger)

    payload = {
        "schema": "twisted-yetter.figure21-su2-2-framing-recovery.v1",
        "status": "YES" if match else "NO",
        "mathematical_status": "DRAFT_TRANSCRIPTION_NUMERIC_COMPARISON",
        "purpose": (
            "Recover the frozen Figure 21 SU(2)_2 sector contractions by "
            "applying the total-framing ribbon twist omitted by the source run."
        ),
        "evaluation_id": evaluation_id,
        "evaluation_identity": identity,
        "source_blackboard_run": {
            "status": "SUPERSEDED_FRAMING_OMISSION_FAILURE",
            "evaluation_id": EXPECTED_SOURCE_EVALUATION_ID,
            "ledger": _relative_or_absolute(args.source_ledger),
            "ledger_sha256": source_sha256,
            "value": complex_json(source_value),
            "git_commit": "30d00ffa992e8067ea1830c62c7276e5e6852b4b",
            "root_cause": (
                "The runner did not pass input framing_labels to "
                "RibbonGraphEvaluator, so it evaluated the blackboard link."
            ),
        },
        "framing_contract": {
            "total_framings": total_framings,
            "visible_self_writhe": visible,
            "framing_corrections": framing_corrections,
            "twists": {
                str(label): complex_json(value)
                for label, value in twists.items()
            },
            "derivation": (
                "Each fixed-label sector is multiplied by product_c "
                "theta(label_c)^(total_framing_c-visible_self_writhe_c)."
            ),
        },
        "result": {
            "value": complex_json(framed_value),
            "reverse_order_value": complex_json(reverse_value),
            "summation_order_difference": order_difference,
            "standard_value": complex_json(EXPECTED_STANDARD_VALUE),
            "absolute_difference": absolute_difference,
            "imaginary_residual": abs(framed_value.imag),
            "match_tolerance": MATCH_TOLERANCE,
            "match": "YES" if match else "NO",
        },
        "coverage": {
            "sector_count": record_count,
            "evaluated_sector_count": len(framed_contributions),
            "source_status_counts": dict(sorted(source_statuses.items())),
            "framed_status_counts": dict(sorted(framed_statuses.items())),
            "complete_exactly_once": True,
        },
        "artifacts": {
            "framed_sector_ledger": {
                "path": _relative_or_absolute(args.output_ledger),
                "sha256": output_ledger_sha256,
                "bytes": args.output_ledger.stat().st_size,
            }
        },
        "generator_script": str(Path(__file__).relative_to(REPO_ROOT)),
        "generator_script_sha256": generator_sha256,
        "git": git,
        "environment": {
            "python": platform.python_version(),
            "host": socket.gethostname(),
        },
        "utc_start": started,
        "utc_finish": utc_now(),
        "reproduce_command": (
            f"python {Path(__file__).relative_to(REPO_ROOT)} "
            f"--source-ledger {_relative_or_absolute(args.source_ledger)} "
            f"--output-ledger {_relative_or_absolute(args.output_ledger)} "
            f"--output-result {_relative_or_absolute(args.output_result)}"
        ),
        "interpretation": {
            "established": (
                "The corrected untwisted SU(2)_2 numerical value matches the "
                "standard CP2#9CP2bar value under the frozen projector contract."
            ),
            "not_established": [
                "The draft Morse transcription is proved identical to Figure 21.",
                "The special-dotted projector hypothesis is a theorem.",
                "Twisted Crane-Yetter detects this exotic pair.",
            ],
        },
    }
    args.output_result.parent.mkdir(parents=True, exist_ok=True)
    result_tmp = args.output_result.with_suffix(args.output_result.suffix + ".tmp")
    result_tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    result_tmp.replace(args.output_result)
    return payload


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser()
    result.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    result.add_argument("--source-ledger", type=Path, required=True)
    result.add_argument("--output-ledger", type=Path, required=True)
    result.add_argument("--output-result", type=Path, required=True)
    result.add_argument("--allow-dirty", action="store_true")
    return result


if __name__ == "__main__":
    print(json.dumps(recover(parser().parse_args()), indent=2, sort_keys=True))
