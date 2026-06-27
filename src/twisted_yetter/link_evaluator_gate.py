"""Minimal colored framed link evaluator gate.

This module is a gate over already-audited toy controls, not a general link
evaluator.  It reads the n16/n17 machine-readable fixtures, records exact
expected values, and refuses diagrams outside the elementary/Hopf baseline.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Final, Literal, Mapping, Sequence

from twisted_yetter.hopf_controls import hopf_control_certificate
from twisted_yetter.link_controls import control_certificate
from twisted_yetter.link_diagram import LinkDiagram

GATE_SCHEMA: Final = "twisted-yetter.colored-framed-link-evaluator-gate.v1"
TOY_FIXTURE_DIR: Final = Path("experiments/inputs/toy-diagrams")

GATE_CLAIM_LEVEL: Final = {
    "claim_level": "computed evidence/schema-test-safe",
    "source_boundary": "SOURCE NEEDED/local-convention controls inherited from n16/n17",
    "scope": (
        "colored framed link evaluator baseline over empty, framed unknot, "
        "split unlink, and positive 0-framed Hopf fixtures"
    ),
    "not_scope": (
        "general colored framed link evaluator, Kirby color, 4D Kirby formula, "
        "closed 4-manifold invariant, twisted Yetter formula, or exotic claim"
    ),
    "unblocks": [
        "n21-ordinary-kirby-color-source-capture",
        "n22-ordinary-kirby-color-implementation",
    ],
}

ControlKind = Literal["empty", "unknot", "unlink", "hopf"]


@dataclass(frozen=True)
class GateFixture:
    """A single fixture/control entry in the n18 gate manifest."""

    fixture_path: Path
    control_kind: ControlKind
    labels_by_component: Mapping[str, str]
    note: str


DEFAULT_GATE_FIXTURES: Final[tuple[GateFixture, ...]] = (
    GateFixture(
        TOY_FIXTURE_DIR / "s4-empty.json",
        "empty",
        {},
        "empty link normalization control",
    ),
    GateFixture(
        TOY_FIXTURE_DIR / "cp2-plus-one-framed-unknot.json",
        "unknot",
        {"cp2_h": "2"},
        "+1-framed unknot symbolic twist control",
    ),
    GateFixture(
        TOY_FIXTURE_DIR / "unlink-two-component.json",
        "unlink",
        {"u1": "1", "u2": "1"},
        "split unlink multiplicativity control",
    ),
    GateFixture(
        TOY_FIXTURE_DIR / "hopf-link.json",
        "hopf",
        {"h1": "1", "h2": "2"},
        "positive 0-framed Hopf S_ij/S_00 control",
    ),
    GateFixture(
        TOY_FIXTURE_DIR / "s2x-s2-hopf-zero-framed.json",
        "hopf",
        {"s2_a": "2", "s2_b": "2"},
        "S2xS2 toy Hopf fixture control",
    ),
)


def run_default_gate(repo_root: str | Path = ".") -> dict[str, object]:
    """Run the deterministic n18 fixture gate from ``repo_root``."""

    return run_gate(DEFAULT_GATE_FIXTURES, repo_root=repo_root)


def run_gate(
    fixtures: Sequence[GateFixture],
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Run a deterministic fixture manifest and return a JSON-ready certificate."""

    root = Path(repo_root)
    results = [evaluate_gate_fixture(entry, root) for entry in fixtures]
    return {
        "schema": GATE_SCHEMA,
        "status": "pass",
        "node_id": "n18-colored-framed-link-evaluator-gate",
        "fixture_count": len(results),
        "results": results,
        "claim": GATE_CLAIM_LEVEL,
    }


def evaluate_gate_fixture(entry: GateFixture, repo_root: str | Path = ".") -> dict[str, object]:
    """Evaluate one manifest entry against the narrow n18 control boundary."""

    root = Path(repo_root)
    fixture_path = entry.fixture_path
    load_path = fixture_path if fixture_path.is_absolute() else root / fixture_path
    diagram = LinkDiagram.from_json(json.loads(load_path.read_text()))
    result = evaluate_supported_control(diagram, entry.labels_by_component, entry.control_kind)
    result["fixture_path"] = _stable_path(fixture_path)
    result["control_kind"] = entry.control_kind
    result["note"] = entry.note
    return _ordered_result(result)


def evaluate_supported_control(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
    control_kind: ControlKind,
) -> dict[str, object]:
    """Return the expected control certificate for one supported gate kind.

    Unsupported diagram/control combinations raise ``NotImplementedError`` so
    callers cannot accidentally treat this gate as a general evaluator.
    """

    if control_kind in {"empty", "unknot", "unlink"}:
        _check_elementary_shape(diagram, control_kind)
        return control_certificate(diagram, labels_by_component)
    if control_kind == "hopf":
        return hopf_control_certificate(diagram, labels_by_component)
    raise NotImplementedError(f"unsupported gate control kind: {control_kind!r}")


def stable_gate_json(certificate: Mapping[str, object]) -> str:
    """Serialize a gate certificate deterministically for artifact comparison."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _check_elementary_shape(diagram: LinkDiagram, control_kind: ControlKind) -> None:
    if diagram.crossings:
        raise NotImplementedError("elementary gate controls do not cover crossings")
    if control_kind == "empty" and diagram.components:
        raise NotImplementedError("empty control requires zero components")
    if control_kind == "unknot" and len(diagram.components) != 1:
        raise NotImplementedError("unknot control requires exactly one component")
    if control_kind == "unlink" and len(diagram.components) < 2:
        raise NotImplementedError("unlink control requires at least two components")


def _ordered_result(result: Mapping[str, object]) -> dict[str, object]:
    return {
        "schema": result["schema"],
        "status": result["status"],
        "fixture_path": result["fixture_path"],
        "diagram_id": result["diagram_id"],
        "control_kind": result["control_kind"],
        "labels_by_component": result["labels_by_component"],
        "expected_value": result["expected_value"],
        "claim": result["claim"],
        "note": result["note"],
        **({"component_ids": result["component_ids"]} if "component_ids" in result else {}),
        **({"framings": result["framings"]} if "framings" in result else {}),
        **({"sanity": result["sanity"]} if "sanity" in result else {}),
    }


def _stable_path(path: Path) -> str:
    return path.as_posix()


__all__ = [
    "DEFAULT_GATE_FIXTURES",
    "GATE_CLAIM_LEVEL",
    "GATE_SCHEMA",
    "GateFixture",
    "evaluate_gate_fixture",
    "evaluate_supported_control",
    "run_default_gate",
    "run_gate",
    "stable_gate_json",
]
