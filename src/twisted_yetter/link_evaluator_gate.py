"""Restricted colored framed link evaluator gate.

This module gates the n18b SU(2)_2 evaluator core, not a general planar RT
evaluator.  It reads the n16/n17 machine-readable fixtures, checks that they
pass through one evaluator entry point, and records structured blockers for
diagram features outside the restricted core.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Final, Literal, Mapping, Sequence

from twisted_yetter.link_diagram import Component, Crossing, LinkDiagram, StrandRef
from twisted_yetter.su2_link_evaluator import evaluate_su2_level2_link

GATE_SCHEMA: Final = "twisted-yetter.colored-framed-link-evaluator-gate.v1"
TOY_FIXTURE_DIR: Final = Path("experiments/inputs/toy-diagrams")

GATE_CLAIM_LEVEL: Final = {
    "claim_level": "computed evidence/restricted-evaluator-core-gate",
    "source_boundary": "SOURCE NEEDED/local-convention controls inherited from n14/n16/n17",
    "scope": (
        "restricted bare SU(2)_2 colored framed link evaluator core over empty, "
        "framed unknot, split unlink, and positive Hopf controls"
    ),
    "not_scope": (
        "general colored framed link evaluator, general planar RT recoupling "
        "evaluator, Kirby color, 4D Kirby formula, closed 4-manifold invariant, "
        "twisted Yetter formula, or exotic claim"
    ),
    "accepted_core": "n18b-su2-2-link-evaluator-core at commit 137d449",
    "core_acceptance_evidence": "pytest 219 passed; CTL verify status ok",
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


@dataclass(frozen=True)
class BlockerCheck:
    """A diagram/control pair that must block in the restricted core."""

    diagram: LinkDiagram
    labels_by_component: Mapping[str, str]
    expected_reason_id: str
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

DEFAULT_BLOCKER_CHECKS: Final[tuple[BlockerCheck, ...]] = (
    BlockerCheck(
        LinkDiagram(
            "three-component-crossing-not-planar-evaluable",
            components=(Component("a", 0), Component("b", 0), Component("c", 0)),
            crossings=(
                Crossing("x1", 1, StrandRef("a", "a1"), StrandRef("b", "b1")),
                Crossing("x2", 1, StrandRef("a", "a2"), StrandRef("b", "b2")),
            ),
        ),
        {"a": "0", "b": "1", "c": "2"},
        "general-crossing-diagram-unsupported",
        "general crossing diagram blocks until planar adjacency plus F/R data exist",
    ),
    BlockerCheck(
        LinkDiagram("dotted-unknot", components=(Component("d", 0, dotted=True),)),
        {"d": "0"},
        "dotted-components-unsupported",
        "dotted Kirby semantics are downstream of the bare link evaluator core",
    ),
)


def run_default_gate(repo_root: str | Path = ".") -> dict[str, object]:
    """Run the deterministic n18 fixture gate from ``repo_root``."""

    return run_gate(DEFAULT_GATE_FIXTURES, DEFAULT_BLOCKER_CHECKS, repo_root=repo_root)


def run_gate(
    fixtures: Sequence[GateFixture],
    blocker_checks: Sequence[BlockerCheck] = DEFAULT_BLOCKER_CHECKS,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Run a deterministic fixture manifest and return a JSON-ready certificate."""

    root = Path(repo_root)
    results = [evaluate_gate_fixture(entry, root) for entry in fixtures]
    blockers = [evaluate_blocker_check(entry) for entry in blocker_checks]
    return {
        "schema": GATE_SCHEMA,
        "status": "pass",
        "node_id": "n18-colored-framed-link-evaluator-gate",
        "fixture_count": len(results),
        "blocker_check_count": len(blockers),
        "results": results,
        "blocker_checks": blockers,
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
    """Evaluate one supported gate control through the SU(2)_2 core.

    Unsupported diagram/control combinations raise ``NotImplementedError`` so
    callers cannot accidentally treat this gate as a general evaluator.
    """

    _check_expected_shape(diagram, control_kind)
    result = evaluate_su2_level2_link(diagram, labels_by_component)
    if result["status"] != "pass":
        blocker = result.get("blocker", {})
        reason = blocker.get("reason_id", "unknown-blocker")
        raise NotImplementedError(f"gate control blocked by evaluator core: {reason}")
    expected_kind = {
        "empty": "empty",
        "unknot": "split_no_crossing",
        "unlink": "split_no_crossing",
        "hopf": "positive_hopf",
    }[control_kind]
    if result["supported_kind"] != expected_kind:
        raise NotImplementedError(
            f"gate control {control_kind!r} expected {expected_kind!r}, "
            f"got {result['supported_kind']!r}"
        )
    return result


def evaluate_blocker_check(entry: BlockerCheck) -> dict[str, object]:
    """Evaluate one expected structured blocker through the same core entry point."""

    result = evaluate_su2_level2_link(entry.diagram, entry.labels_by_component)
    if result["status"] != "blocked":
        raise AssertionError(f"expected blocked evaluator result for {entry.diagram.diagram_id}")
    blocker = result["blocker"]
    if blocker["reason_id"] != entry.expected_reason_id:
        raise AssertionError(
            f"expected blocker {entry.expected_reason_id!r}, got {blocker['reason_id']!r}"
        )
    return _ordered_blocker_result({**result, "note": entry.note})


def stable_gate_json(certificate: Mapping[str, object]) -> str:
    """Serialize a gate certificate deterministically for artifact comparison."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _check_expected_shape(diagram: LinkDiagram, control_kind: ControlKind) -> None:
    if control_kind == "empty" and diagram.components:
        raise NotImplementedError("empty control requires zero components")
    if control_kind == "unknot" and len(diagram.components) != 1:
        raise NotImplementedError("unknot control requires exactly one component")
    if control_kind == "unlink" and len(diagram.components) < 2:
        raise NotImplementedError("unlink control requires at least two components")
    if control_kind in {"empty", "unknot", "unlink"} and diagram.crossings:
        raise NotImplementedError("elementary gate controls do not cover crossings")


def _ordered_result(result: Mapping[str, object]) -> dict[str, object]:
    return {
        "schema": result["schema"],
        "status": result["status"],
        "fixture_path": result["fixture_path"],
        "diagram_id": result["diagram_id"],
        "control_kind": result["control_kind"],
        "supported_kind": result["supported_kind"],
        "labels_by_component": result["labels_by_component"],
        "value": result["value"],
        "claim": result["claim"],
        "note": result["note"],
        **({"component_ids": result["component_ids"]} if "component_ids" in result else {}),
        **({"framings": result["framings"]} if "framings" in result else {}),
        **(
            {"evaluation_details": result["evaluation_details"]}
            if "evaluation_details" in result
            else {}
        ),
        **(
            {"framing_twist_convention": result["framing_twist_convention"]}
            if "framing_twist_convention" in result
            else {}
        ),
    }


def _ordered_blocker_result(result: Mapping[str, object]) -> dict[str, object]:
    return {
        "schema": result["schema"],
        "status": result["status"],
        "diagram_id": result["diagram_id"],
        "labels_by_component": result["labels_by_component"],
        "blocker": result["blocker"],
        "claim": result["claim"],
        "note": result["note"],
        **({"component_ids": result["component_ids"]} if "component_ids" in result else {}),
        **({"framings": result["framings"]} if "framings" in result else {}),
    }


def _stable_path(path: Path) -> str:
    return path.as_posix()


__all__ = [
    "DEFAULT_GATE_FIXTURES",
    "DEFAULT_BLOCKER_CHECKS",
    "BlockerCheck",
    "GATE_CLAIM_LEVEL",
    "GATE_SCHEMA",
    "GateFixture",
    "evaluate_blocker_check",
    "evaluate_gate_fixture",
    "evaluate_supported_control",
    "run_default_gate",
    "run_gate",
    "stable_gate_json",
]
