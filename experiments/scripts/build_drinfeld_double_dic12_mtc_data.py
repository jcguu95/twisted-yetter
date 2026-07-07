#!/usr/bin/env python3
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from datetime import UTC, datetime
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
import time
from typing import Any

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT_DIR = REPO_ROOT / "experiments" / "results" / "mtc-candidates"
SKELETON_PATH = OUTPUT_DIR / "drinfeld-double-dic12-omega0-fusion-skeleton-v1.json"
FR_DATA_PATH = OUTPUT_DIR / "drinfeld-double-dic12-omega0-mtc-fr-data-v1.json"
CONSTRUCTION_PATH = OUTPUT_DIR / "drinfeld-double-dic12-construction-certificate-v1.json"
VERIFICATION_HINT_PATH = OUTPUT_DIR / "drinfeld-double-dic12-omega0-verification-run-v1.json"

MTC_ID = "omega0_untwisted_D_Dic12"
SCHEMA_FR = "twisted-yetter.mtc.fr-data.drinfeld-double-dic12.v1"
SCHEMA_SKELETON = "twisted-yetter.mtc.fusion-skeleton.drinfeld-double-dic12.v1"
SCHEMA_CONSTRUCTION = "twisted-yetter.mtc.drinfeld-double-dic12-construction-certificate.v1"
FR_TOLERANCE = 1e-10
COHERENCE_TOLERANCE = 1e-7
SPARSE_TOLERANCE = 1e-12
NULL_TOLERANCE = 1e-9

Element = tuple[int, int]


def main() -> int:
    args = parse_args()
    started = time.monotonic()
    started_utc = datetime.now(UTC).isoformat()
    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    group = Dic12Group()
    simples = build_simple_objects(group)
    modules = {simple.label: build_module(group, simple) for simple in simples}
    homs = build_all_hom_spaces(group, simples, modules)
    fusion_rules = build_fusion_rules(simples, homs)
    f_blocks, f_summary = build_f_blocks(simples, modules, homs)
    r_blocks, r_summary = build_r_blocks(group, simples, modules, homs)
    coherence = scan_coherence(simples, fusion_rules, f_blocks, r_blocks)
    skeleton = build_skeleton_payload(
        args=args,
        group=group,
        simples=simples,
        fusion_rules=fusion_rules,
        homs=homs,
        started_utc=started_utc,
        started=started,
    )
    fr_payload = build_fr_payload(
        args=args,
        group=group,
        simples=simples,
        homs=homs,
        fusion_rules=fusion_rules,
        f_blocks=f_blocks,
        r_blocks=r_blocks,
        f_summary=f_summary,
        r_summary=r_summary,
        coherence=coherence,
        started_utc=started_utc,
        started=started,
    )
    construction = build_construction_payload(
        group=group,
        simples=simples,
        skeleton_path=output_dir / SKELETON_PATH.name,
        fr_path=output_dir / FR_DATA_PATH.name,
    )

    writes = [
        (output_dir / SKELETON_PATH.name, skeleton),
        (output_dir / FR_DATA_PATH.name, fr_payload),
        (output_dir / CONSTRUCTION_PATH.name, construction),
    ]
    for path, payload in writes:
        write_json(path, payload)
        print(json.dumps({"path": rel(path), "sha256": file_sha256(path)}, sort_keys=True))

    if args.write_verification_hint:
        hint = {
            "schema": "twisted-yetter.drinfeld-double-dic12.verification-run.v1",
            "status": "not_run",
            "generator_script": "experiments/scripts/build_drinfeld_double_dic12_mtc_data.py",
            "message": "Run experiments/scripts/verify_drinfeld_double_dic12_mtc_data.py to produce the independent verification-run artifact.",
            "input_artifact": {
                "path": rel(output_dir / FR_DATA_PATH.name),
                "sha256": file_sha256(output_dir / FR_DATA_PATH.name),
            },
        }
        write_json(output_dir / VERIFICATION_HINT_PATH.name, hint)
        print(json.dumps({"path": rel(output_dir / VERIFICATION_HINT_PATH.name), "status": "not_run"}, sort_keys=True))
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build numeric F/R symbols for untwisted D(Dic_12).")
    parser.add_argument("--output-dir", type=Path, default=OUTPUT_DIR)
    parser.add_argument(
        "--write-verification-hint",
        action="store_true",
        help="Write a placeholder verification artifact before the independent verifier is run.",
    )
    return parser.parse_args()


class Dic12Group:
    def __init__(self) -> None:
        self.elements: list[Element] = [(i, j) for j in (0, 1) for i in range(6)]
        self.identity: Element = (0, 0)
        self._inverse = {g: self._find_inverse(g) for g in self.elements}
        self.classes = self._build_classes()
        self.class_by_label = {item["label"]: item for item in self.classes}

    def mul(self, left: Element, right: Element) -> Element:
        i, j = left
        k, ell = right
        twist = -k if j else k
        x_square = 3 if j and ell else 0
        return ((i + twist + x_square) % 6, (j + ell) % 2)

    def inv(self, element: Element) -> Element:
        return self._inverse[element]

    def conj(self, actor: Element, element: Element) -> Element:
        return self.mul(self.mul(actor, element), self.inv(actor))

    def fmt(self, element: Element) -> str:
        i, j = element
        if j == 0:
            if i == 0:
                return "1"
            return "a" if i == 1 else f"a^{i}"
        return "x" if i == 0 else "ax" if i == 1 else f"a^{i}x"

    def parse_power(self, generator: Element, element: Element) -> int:
        current = self.identity
        for power in range(16):
            if current == element:
                return power
            current = self.mul(current, generator)
        raise ValueError(f"{self.fmt(element)} is not a power of {self.fmt(generator)}")

    def _find_inverse(self, element: Element) -> Element:
        for candidate in self.elements:
            if self.mul(element, candidate) == self.identity and self.mul(candidate, element) == self.identity:
                return candidate
        raise ValueError(element)

    def _build_classes(self) -> list[dict[str, Any]]:
        specs = [
            ("1A", (0, 0)),
            ("aA", (1, 0)),
            ("a2A", (2, 0)),
            ("a3A", (3, 0)),
            ("xA", (0, 1)),
            ("axA", (1, 1)),
        ]
        classes = []
        for label, rep in specs:
            elements = sorted({self.conj(h, rep) for h in self.elements})
            centralizer = [h for h in self.elements if self.mul(h, rep) == self.mul(rep, h)]
            transporters = {}
            for element in elements:
                for t in self.elements:
                    if self.conj(t, rep) == element:
                        transporters[element] = t
                        break
            classes.append(
                {
                    "label": label,
                    "representative": rep,
                    "elements": elements,
                    "centralizer": centralizer,
                    "transporters": transporters,
                }
            )
        return classes


@dataclass(frozen=True)
class CentralizerRep:
    label: str
    kind: str
    dimension: int
    class_label: str
    parameter: int
    generator: Element | None = None

    def matrix(self, group: Dic12Group, element: Element) -> np.ndarray:
        if self.kind == "dic12_linear":
            i, j = element
            value = ((-1) ** (self.parameter * i)) * (1j ** (self.parameter * j))
            return np.array([[value]], dtype=complex)
        if self.kind == "dic12_2d":
            i, j = element
            zeta = np.exp(2j * np.pi / 6)
            a_matrix = np.diag([zeta ** (self.parameter * i), zeta ** (-self.parameter * i)])
            sign = (-1) ** self.parameter
            x_matrix = np.array([[0, sign], [1, 0]], dtype=complex)
            return a_matrix @ (x_matrix if j else np.eye(2, dtype=complex))
        if self.kind == "c6":
            i, j = element
            if j != 0:
                raise ValueError(f"{group.fmt(element)} is not in <a>")
            value = np.exp(2j * np.pi * self.parameter * i / 6)
            return np.array([[value]], dtype=complex)
        if self.kind == "c4":
            if self.generator is None:
                raise ValueError("C4 rep has no generator")
            power = group.parse_power(self.generator, element) % 4
            value = 1j ** (self.parameter * power)
            return np.array([[value]], dtype=complex)
        raise ValueError(self.kind)

    def twist_angle(self, group: Dic12Group, representative: Element) -> Fraction:
        matrix = self.matrix(group, representative)
        scalar = np.trace(matrix) / self.dimension
        angle = np.angle(scalar) / (2 * np.pi)
        return Fraction(round(angle * 24), 24)


@dataclass(frozen=True)
class SimpleObject:
    label: str
    class_label: str
    class_representative: Element
    class_elements: tuple[Element, ...]
    centralizer: tuple[Element, ...]
    centralizer_rep: CentralizerRep
    quantum_dimension: int
    twist: dict[str, Any]


@dataclass
class Module:
    label: str
    dimension: int
    grades: list[Element]
    basis_labels: list[str]
    action: dict[Element, np.ndarray]


def build_simple_objects(group: Dic12Group) -> list[SimpleObject]:
    simples: list[SimpleObject] = []
    for cls in group.classes:
        class_label = cls["label"]
        reps = centralizer_reps_for_class(class_label, cls["representative"])
        for rep in reps:
            qdim = len(cls["elements"]) * rep.dimension
            twist = root_payload(rep.twist_angle(group, cls["representative"]))
            simples.append(
                SimpleObject(
                    label=f"{class_label}:{rep.label}",
                    class_label=class_label,
                    class_representative=cls["representative"],
                    class_elements=tuple(cls["elements"]),
                    centralizer=tuple(cls["centralizer"]),
                    centralizer_rep=rep,
                    quantum_dimension=qdim,
                    twist=twist,
                )
            )
    return simples


def centralizer_reps_for_class(class_label: str, representative: Element) -> list[CentralizerRep]:
    if class_label in {"1A", "a3A"}:
        return [
            CentralizerRep("lin0", "dic12_linear", 1, class_label, 0),
            CentralizerRep("lin1", "dic12_linear", 1, class_label, 1),
            CentralizerRep("lin2", "dic12_linear", 1, class_label, 2),
            CentralizerRep("lin3", "dic12_linear", 1, class_label, 3),
            CentralizerRep("rho1", "dic12_2d", 2, class_label, 1),
            CentralizerRep("rho2", "dic12_2d", 2, class_label, 2),
        ]
    if class_label in {"aA", "a2A"}:
        return [CentralizerRep(f"chi{k}", "c6", 1, class_label, k) for k in range(6)]
    if class_label in {"xA", "axA"}:
        return [CentralizerRep(f"eta{k}", "c4", 1, class_label, k, generator=representative) for k in range(4)]
    raise ValueError(class_label)


def root_payload(angle: Fraction) -> dict[str, Any]:
    angle = angle % 1
    if angle == 0:
        order = 1
        exponent = 0
    else:
        order = angle.denominator
        exponent = angle.numerator % order
    return {
        "kind": "root_of_unity",
        "root_order": order,
        "exponent": exponent,
        "angle_fraction": f"{exponent}/{order}",
    }


def build_module(group: Dic12Group, simple: SimpleObject) -> Module:
    cls = group.class_by_label[simple.class_label]
    grades: list[Element] = []
    basis_labels: list[str] = []
    for element in simple.class_elements:
        for rep_idx in range(simple.centralizer_rep.dimension):
            grades.append(element)
            basis_labels.append(f"{group.fmt(element)}#v{rep_idx}")
    dimension = len(grades)
    action = {}
    basis_index = {
        (element, rep_idx): element_idx * simple.centralizer_rep.dimension + rep_idx
        for element_idx, element in enumerate(simple.class_elements)
        for rep_idx in range(simple.centralizer_rep.dimension)
    }
    for actor in group.elements:
        matrix = np.zeros((dimension, dimension), dtype=complex)
        for source_element in simple.class_elements:
            source_t = cls["transporters"][source_element]
            target_element = group.conj(actor, source_element)
            target_t = cls["transporters"][target_element]
            centralizer_element = group.mul(group.mul(group.inv(target_t), actor), source_t)
            rep_matrix = simple.centralizer_rep.matrix(group, centralizer_element)
            for source_rep in range(simple.centralizer_rep.dimension):
                source_col = basis_index[(source_element, source_rep)]
                for target_rep in range(simple.centralizer_rep.dimension):
                    target_row = basis_index[(target_element, target_rep)]
                    matrix[target_row, source_col] = rep_matrix[target_rep, source_rep]
        action[actor] = matrix
    return Module(simple.label, dimension, grades, basis_labels, action)


def build_all_hom_spaces(
    group: Dic12Group,
    simples: list[SimpleObject],
    modules: dict[str, Module],
) -> dict[tuple[str, str, str], list[np.ndarray]]:
    labels = [simple.label for simple in simples]
    tensor_cache: dict[tuple[str, str], Module] = {}
    homs: dict[tuple[str, str, str], list[np.ndarray]] = {}
    for left in labels:
        for right in labels:
            tensor = tensor_cache.setdefault(
                (left, right),
                tensor_module(group, modules[left], modules[right]),
            )
            for target in labels:
                homs[(left, right, target)] = hom_basis(group, tensor, modules[target])
    return homs


def tensor_module(group: Dic12Group, left: Module, right: Module) -> Module:
    grades = [group.mul(gl, gr) for gl in left.grades for gr in right.grades]
    basis_labels = [f"{lb}|{rb}" for lb in left.basis_labels for rb in right.basis_labels]
    action = {g: np.kron(left.action[g], right.action[g]) for g in group.elements}
    return Module(f"({left.label})*({right.label})", left.dimension * right.dimension, grades, basis_labels, action)


def hom_basis(group: Dic12Group, source: Module, target: Module) -> list[np.ndarray]:
    variables: list[tuple[int, int]] = []
    variable_index: dict[tuple[int, int], int] = {}
    for row, target_grade in enumerate(target.grades):
        for col, source_grade in enumerate(source.grades):
            if target_grade == source_grade:
                variable_index[(row, col)] = len(variables)
                variables.append((row, col))
    if not variables:
        return []
    equations: list[np.ndarray] = []
    for actor in group.elements:
        target_action = target.action[actor]
        source_action = source.action[actor]
        for row in range(target.dimension):
            for col in range(source.dimension):
                coeff = np.zeros(len(variables), dtype=complex)
                for row_prime in range(target.dimension):
                    idx = variable_index.get((row_prime, col))
                    if idx is not None:
                        coeff[idx] += target_action[row, row_prime]
                for col_prime in range(source.dimension):
                    idx = variable_index.get((row, col_prime))
                    if idx is not None:
                        coeff[idx] -= source_action[col_prime, col]
                if np.linalg.norm(coeff) > NULL_TOLERANCE:
                    equations.append(coeff)
    if not equations:
        matrix = np.zeros((0, len(variables)), dtype=complex)
    else:
        matrix = np.vstack(equations)
    _, singular_values, vh = np.linalg.svd(matrix, full_matrices=True)
    rank = int(np.sum(singular_values > NULL_TOLERANCE))
    null_vectors = vh[rank:].conj().T
    basis = []
    for vector_idx in range(null_vectors.shape[1]):
        vector = null_vectors[:, vector_idx]
        morphism = np.zeros((target.dimension, source.dimension), dtype=complex)
        for value, (row, col) in zip(vector, variables, strict=True):
            morphism[row, col] = value
        norm = np.linalg.norm(morphism)
        if norm <= NULL_TOLERANCE:
            continue
        morphism = morphism / norm
        flat = morphism.ravel()
        pivot = int(np.argmax(np.abs(flat)))
        if abs(flat[pivot]) > NULL_TOLERANCE:
            morphism *= np.exp(-1j * np.angle(flat[pivot]))
            if morphism.ravel()[pivot].real < 0:
                morphism *= -1
        basis.append(clean_matrix(morphism))
    return basis


def clean_matrix(matrix: np.ndarray, tol: float = 1e-13) -> np.ndarray:
    result = np.array(matrix, dtype=complex, copy=True)
    result.real[abs(result.real) < tol] = 0.0
    result.imag[abs(result.imag) < tol] = 0.0
    return result


def build_fusion_rules(
    simples: list[SimpleObject],
    homs: dict[tuple[str, str, str], list[np.ndarray]],
) -> list[dict[str, Any]]:
    labels = [simple.label for simple in simples]
    rules = []
    for left in labels:
        for right in labels:
            outputs = []
            for target in labels:
                multiplicity = len(homs[(left, right, target)])
                if multiplicity:
                    outputs.append({"target": target, "multiplicity": multiplicity})
            rules.append({"left": left, "right": right, "outputs": outputs})
    return rules


def fusion_lookup(fusion_rules: list[dict[str, Any]]) -> dict[tuple[str, str, str], int]:
    labels = sorted({rule["left"] for rule in fusion_rules})
    lookup = {(left, right, target): 0 for left in labels for right in labels for target in labels}
    for rule in fusion_rules:
        for output in rule["outputs"]:
            lookup[(rule["left"], rule["right"], output["target"])] = int(output["multiplicity"])
    return lookup


def build_f_blocks(
    simples: list[SimpleObject],
    modules: dict[str, Module],
    homs: dict[tuple[str, str, str], list[np.ndarray]],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    labels = [simple.label for simple in simples]
    blocks = []
    max_error = 0.0
    dim_counter: Counter[int] = Counter()
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    left_basis = [
                        x
                        for x in labels
                        if len(homs[(a, b, x)]) and len(homs[(x, c, d)])
                    ]
                    right_basis = [
                        y
                        for y in labels
                        if len(homs[(b, c, y)]) and len(homs[(a, y, d)])
                    ]
                    if not left_basis and not right_basis:
                        continue
                    if len(left_basis) != len(right_basis):
                        raise RuntimeError(f"F-basis dimension mismatch for {(a, b, c, d)}")
                    left_maps = []
                    right_maps = []
                    for x in left_basis:
                        left_maps.append(
                            homs[(x, c, d)][0]
                            @ np.kron(homs[(a, b, x)][0], np.eye(modules[c].dimension, dtype=complex))
                        )
                    for y in right_basis:
                        right_maps.append(
                            homs[(a, y, d)][0]
                            @ np.kron(np.eye(modules[a].dimension, dtype=complex), homs[(b, c, y)][0])
                        )
                    left_matrix = np.column_stack([item.reshape(-1) for item in left_maps])
                    right_matrix = np.column_stack([item.reshape(-1) for item in right_maps])
                    coeffs, *_ = np.linalg.lstsq(left_matrix, right_matrix, rcond=None)
                    residual = left_matrix @ coeffs - right_matrix
                    error = float(np.max(np.linalg.norm(residual, axis=0))) if residual.size else 0.0
                    max_error = max(max_error, error)
                    dim_counter[len(left_basis)] += 1
                    blocks.append(
                        {
                            "a": a,
                            "b": b,
                            "c": c,
                            "d": d,
                            "left_basis_labels": [[x, 0, 0] for x in left_basis],
                            "right_basis_labels": [[y, 0, 0] for y in right_basis],
                            "right_to_left": sparse_matrix_payload(clean_matrix(coeffs)),
                            "max_reconstruction_error": error,
                        }
                    )
    return blocks, {"max_reconstruction_error": max_error, "dimension_distribution": dict(sorted(dim_counter.items()))}


def build_r_blocks(
    group: Dic12Group,
    simples: list[SimpleObject],
    modules: dict[str, Module],
    homs: dict[tuple[str, str, str], list[np.ndarray]],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    labels = [simple.label for simple in simples]
    blocks = []
    max_error = 0.0
    for a in labels:
        for b in labels:
            braid = braiding_matrix(group, modules[a], modules[b])
            for c in labels:
                ab_basis = homs[(a, b, c)]
                ba_basis = homs[(b, a, c)]
                if not ab_basis and not ba_basis:
                    continue
                if len(ab_basis) != len(ba_basis):
                    raise RuntimeError(f"R-basis dimension mismatch for {(a, b, c)}")
                ab_matrix = np.column_stack([item.reshape(-1) for item in ab_basis])
                braided = np.column_stack([(item @ braid).reshape(-1) for item in ba_basis])
                coeffs, *_ = np.linalg.lstsq(ab_matrix, braided, rcond=None)
                residual = ab_matrix @ coeffs - braided
                error = float(np.max(np.linalg.norm(residual, axis=0))) if residual.size else 0.0
                max_error = max(max_error, error)
                blocks.append(
                    {
                        "a": a,
                        "b": b,
                        "c": c,
                        "domain": "Hom(b tensor a, c)",
                        "codomain": "Hom(a tensor b, c)",
                        "ba_to_ab": sparse_matrix_payload(clean_matrix(coeffs)),
                        "max_reconstruction_error": error,
                    }
                )
    return blocks, {"max_reconstruction_error": max_error}


def braiding_matrix(group: Dic12Group, left: Module, right: Module) -> np.ndarray:
    source_dim = left.dimension * right.dimension
    target_dim = right.dimension * left.dimension
    matrix = np.zeros((target_dim, source_dim), dtype=complex)
    for left_idx, grade in enumerate(left.grades):
        right_action = right.action[grade]
        for right_idx in range(right.dimension):
            source_col = left_idx * right.dimension + right_idx
            for right_target in range(right.dimension):
                target_row = right_target * left.dimension + left_idx
                matrix[target_row, source_col] = right_action[right_target, right_idx]
    return matrix


def scan_coherence(
    simples: list[SimpleObject],
    fusion_rules: list[dict[str, Any]],
    f_blocks: list[dict[str, Any]],
    r_blocks: list[dict[str, Any]],
) -> dict[str, Any]:
    labels = [simple.label for simple in simples]
    fusion = fusion_lookup(fusion_rules)
    pair_outputs = pair_output_lookup(labels, fusion)
    f_data = FData.from_blocks(f_blocks)
    r_data = RData.from_blocks(r_blocks)
    pentagon = scan_pentagon(labels, fusion, pair_outputs, f_data)
    right_hexagon = scan_right_hexagon(labels, fusion, pair_outputs, f_data, r_data)
    left_hexagon = scan_left_hexagon(labels, fusion, pair_outputs, f_data, r_data)
    scans = {
        "pentagon": pentagon,
        "right_hexagon": right_hexagon,
        "left_hexagon": left_hexagon,
    }
    status = "pass" if all(scan["max_error"] <= COHERENCE_TOLERANCE for scan in scans.values()) else "fail"
    scans["pentagon"]["total_label_tuples"] = len(labels) ** 5
    scans["pentagon"]["scanned_label_tuples"] = len(labels) ** 5
    scans["right_hexagon"]["total_label_tuples"] = len(labels) ** 4
    scans["right_hexagon"]["scanned_label_tuples"] = len(labels) ** 4
    scans["left_hexagon"]["total_label_tuples"] = len(labels) ** 4
    scans["left_hexagon"]["scanned_label_tuples"] = len(labels) ** 4
    for scan in scans.values():
        scan["failure_count_recorded"] = 0 if scan["max_error"] <= COHERENCE_TOLERANCE else 1
        scan["recorded_failures"] = [] if scan["max_error"] <= COHERENCE_TOLERANCE else [scan["worst_example"]]
        scan["max_error_within_tolerance"] = scan["max_error"] <= COHERENCE_TOLERANCE
    return {
        "kind": "floating-point all-active-label coherence scan",
        "status": status,
        "tolerance": COHERENCE_TOLERANCE,
        "label_tuple_counts": {
            "pentagon_all_label_tuples": len(labels) ** 5,
            "right_hexagon_all_label_tuples": len(labels) ** 4,
            "left_hexagon_all_label_tuples": len(labels) ** 4,
        },
        "scans": scans,
    }


def pair_output_lookup(labels: list[str], fusion: dict[tuple[str, str, str], int]) -> dict[tuple[str, str], list[str]]:
    return {
        (left, right): [target for target in labels if fusion[(left, right, target)]]
        for left in labels
        for right in labels
    }


@dataclass
class FData:
    matrices: dict[tuple[str, str, str, str], np.ndarray]
    inverse_matrices: dict[tuple[str, str, str, str], np.ndarray]
    left_labels: dict[tuple[str, str, str, str], list[str]]
    right_labels: dict[tuple[str, str, str, str], list[str]]

    @classmethod
    def from_blocks(cls, blocks: list[dict[str, Any]]) -> FData:
        matrices = {}
        left_labels = {}
        right_labels = {}
        for block in blocks:
            key = (block["a"], block["b"], block["c"], block["d"])
            matrices[key] = matrix_from_payload(block["right_to_left"])
            left_labels[key] = [item[0] for item in block["left_basis_labels"]]
            right_labels[key] = [item[0] for item in block["right_basis_labels"]]
        inverse_matrices = {key: np.linalg.inv(matrix) for key, matrix in matrices.items()}
        return cls(matrices, inverse_matrices, left_labels, right_labels)

    def matrix(self, key: tuple[str, str, str, str]) -> np.ndarray:
        return self.matrices[key]

    def left_to_right(self, key: tuple[str, str, str, str]) -> np.ndarray:
        return self.inverse_matrices[key]


@dataclass
class RData:
    matrices: dict[tuple[str, str, str], np.ndarray]
    inverse_matrices: dict[tuple[str, str, str], np.ndarray]

    @classmethod
    def from_blocks(cls, blocks: list[dict[str, Any]]) -> RData:
        matrices = {(block["a"], block["b"], block["c"]): matrix_from_payload(block["ba_to_ab"]) for block in blocks}
        inverse_matrices = {key: np.linalg.inv(matrix) for key, matrix in matrices.items()}
        return cls(matrices, inverse_matrices)

    def ab_to_ba(self, key: tuple[str, str, str]) -> np.ndarray:
        return self.inverse_matrices[key]


def scan_pentagon(
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
    pair_outputs: dict[tuple[str, str], list[str]],
    f_data: FData,
) -> dict[str, Any]:
    max_error = 0.0
    active = 0
    worst: dict[str, Any] | None = None
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    possible_e = sorted({
                        e
                        for x in pair_outputs[(a, b)]
                        for y in pair_outputs[(x, c)]
                        for e in pair_outputs[(y, d)]
                    })
                    for e in possible_e:
                        bases = pentagon_bases(pair_outputs, a, b, c, d, e)
                        if not bases["v0"] and not bases["v3"]:
                            continue
                        active += 1
                        top = (
                            pentagon_edge_v2_v3(f_data, bases, b, c, d)
                            @ pentagon_edge_v1_v2(f_data, bases, a, d, e)
                            @ pentagon_edge_v0_v1(f_data, bases, a, b, c)
                        )
                        bottom = (
                            pentagon_edge_v4_v3(f_data, bases, a, b, e)
                            @ pentagon_edge_v0_v4(f_data, bases, c, d, e)
                        )
                        error = matrix_error(top, bottom)
                        if error > max_error:
                            max_error = error
                            worst = {"a": a, "b": b, "c": c, "d": d, "e": e, "error": error}
    return {
        "status": "pass" if max_error <= COHERENCE_TOLERANCE else "fail",
        "active_tuple_count": active,
        "nonzero_fusion_spaces": active,
        "max_error": max_error,
        "worst_example": worst,
        "worst_sample": None if worst is None else [worst["a"], worst["b"], worst["c"], worst["d"], worst["e"]],
    }


def pentagon_bases(
    pair_outputs: dict[tuple[str, str], list[str]],
    a: str,
    b: str,
    c: str,
    d: str,
    e: str,
) -> dict[str, list[tuple[str, str]]]:
    return {
        "v0": [(x, y) for x in pair_outputs[(a, b)] for y in pair_outputs[(x, c)] if e in pair_outputs[(y, d)]],
        "v1": [(u, y) for u in pair_outputs[(b, c)] for y in pair_outputs[(a, u)] if e in pair_outputs[(y, d)]],
        "v2": [(u, v) for u in pair_outputs[(b, c)] for v in pair_outputs[(u, d)] if e in pair_outputs[(a, v)]],
        "v3": [(w, v) for w in pair_outputs[(c, d)] for v in pair_outputs[(b, w)] if e in pair_outputs[(a, v)]],
        "v4": [(x, w) for x in pair_outputs[(a, b)] for w in pair_outputs[(c, d)] if e in pair_outputs[(x, w)]],
    }


def pentagon_edge_v0_v1(f_data: FData, bases: dict[str, list[tuple[str, str]]], a: str, b: str, c: str) -> np.ndarray:
    result = np.zeros((len(bases["v1"]), len(bases["v0"])), dtype=complex)
    row_index = {item: idx for idx, item in enumerate(bases["v1"])}
    for col, (x, y) in enumerate(bases["v0"]):
        key = (a, b, c, y)
        matrix = f_data.left_to_right(key)
        left = f_data.left_labels[key]
        right = f_data.right_labels[key]
        for u_idx, u in enumerate(right):
            row = row_index.get((u, y))
            if row is not None:
                result[row, col] = matrix[u_idx, left.index(x)]
    return result


def pentagon_edge_v1_v2(f_data: FData, bases: dict[str, list[tuple[str, str]]], a: str, d: str, e: str) -> np.ndarray:
    result = np.zeros((len(bases["v2"]), len(bases["v1"])), dtype=complex)
    row_index = {item: idx for idx, item in enumerate(bases["v2"])}
    for col, (u, y) in enumerate(bases["v1"]):
        key = (a, u, d, e)
        matrix = f_data.left_to_right(key)
        left = f_data.left_labels[key]
        right = f_data.right_labels[key]
        for v_idx, v in enumerate(right):
            row = row_index.get((u, v))
            if row is not None:
                result[row, col] = matrix[v_idx, left.index(y)]
    return result


def pentagon_edge_v2_v3(f_data: FData, bases: dict[str, list[tuple[str, str]]], b: str, c: str, d: str) -> np.ndarray:
    result = np.zeros((len(bases["v3"]), len(bases["v2"])), dtype=complex)
    row_index = {item: idx for idx, item in enumerate(bases["v3"])}
    for col, (u, v) in enumerate(bases["v2"]):
        key = (b, c, d, v)
        matrix = f_data.left_to_right(key)
        left = f_data.left_labels[key]
        right = f_data.right_labels[key]
        for w_idx, w in enumerate(right):
            row = row_index.get((w, v))
            if row is not None:
                result[row, col] = matrix[w_idx, left.index(u)]
    return result


def pentagon_edge_v0_v4(f_data: FData, bases: dict[str, list[tuple[str, str]]], c: str, d: str, e: str) -> np.ndarray:
    result = np.zeros((len(bases["v4"]), len(bases["v0"])), dtype=complex)
    row_index = {item: idx for idx, item in enumerate(bases["v4"])}
    for col, (x, y) in enumerate(bases["v0"]):
        key = (x, c, d, e)
        matrix = f_data.left_to_right(key)
        left = f_data.left_labels[key]
        right = f_data.right_labels[key]
        for w_idx, w in enumerate(right):
            row = row_index.get((x, w))
            if row is not None:
                result[row, col] = matrix[w_idx, left.index(y)]
    return result


def pentagon_edge_v4_v3(f_data: FData, bases: dict[str, list[tuple[str, str]]], a: str, b: str, e: str) -> np.ndarray:
    result = np.zeros((len(bases["v3"]), len(bases["v4"])), dtype=complex)
    row_index = {item: idx for idx, item in enumerate(bases["v3"])}
    for col, (x, w) in enumerate(bases["v4"]):
        key = (a, b, w, e)
        matrix = f_data.left_to_right(key)
        left = f_data.left_labels[key]
        right = f_data.right_labels[key]
        for v_idx, v in enumerate(right):
            row = row_index.get((w, v))
            if row is not None:
                result[row, col] = matrix[v_idx, left.index(x)]
    return result


def scan_right_hexagon(
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
    pair_outputs: dict[tuple[str, str], list[str]],
    f_data: FData,
    r_data: RData,
) -> dict[str, Any]:
    max_error = 0.0
    active = 0
    worst = None
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    domain = [y for y in pair_outputs[(b, c)] if d in pair_outputs[(a, y)]]
                    codomain = [y for y in pair_outputs[(b, c)] if d in pair_outputs[(y, a)]]
                    if not domain and not codomain:
                        continue
                    active += 1
                    direct = right_hexagon_direct(domain, codomain, r_data, a, d)
                    path = right_hexagon_path(labels, fusion, pair_outputs, f_data, r_data, a, b, c, d, domain, codomain)
                    error = matrix_error(path, direct)
                    if error > max_error:
                        max_error = error
                        worst = {"a": a, "b": b, "c": c, "d": d, "error": error}
    return {
        "status": "pass" if max_error <= COHERENCE_TOLERANCE else "fail",
        "active_tuple_count": active,
        "nonzero_fusion_spaces": active,
        "max_error": max_error,
        "worst_example": worst,
        "worst_sample": None if worst is None else [worst["a"], worst["b"], worst["c"], worst["d"]],
    }


def right_hexagon_direct(domain: list[str], codomain: list[str], r_data: RData, a: str, d: str) -> np.ndarray:
    result = np.zeros((len(codomain), len(domain)), dtype=complex)
    row_index = {item: idx for idx, item in enumerate(codomain)}
    for col, y in enumerate(domain):
        if y in row_index:
            result[row_index[y], col] = r_data.ab_to_ba((a, y, d))[0, 0]
    return result


def right_hexagon_path(
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
    pair_outputs: dict[tuple[str, str], list[str]],
    f_data: FData,
    r_data: RData,
    a: str,
    b: str,
    c: str,
    d: str,
    domain: list[str],
    codomain: list[str],
) -> np.ndarray:
    t1 = [x for x in pair_outputs[(a, b)] if d in pair_outputs[(x, c)]]
    t2 = [x for x in pair_outputs[(b, a)] if d in pair_outputs[(x, c)]]
    t3 = [z for z in pair_outputs[(a, c)] if d in pair_outputs[(b, z)]]
    t4 = [z for z in pair_outputs[(c, a)] if d in pair_outputs[(b, z)]]
    s1 = f_data.matrix((a, b, c, d))
    s2 = diagonal_braid(t1, t2, r_data, a, b)
    s3 = f_data.left_to_right((b, a, c, d))
    s4 = diagonal_braid(t3, t4, r_data, a, c)
    s5 = f_data.matrix((b, c, a, d))
    return restrict_rows_cols(s5 @ s4 @ s3 @ s2 @ s1, f_data.left_labels[(b, c, a, d)], codomain, domain, domain)


def scan_left_hexagon(
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
    pair_outputs: dict[tuple[str, str], list[str]],
    f_data: FData,
    r_data: RData,
) -> dict[str, Any]:
    max_error = 0.0
    active = 0
    worst = None
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    domain = [x for x in pair_outputs[(a, b)] if d in pair_outputs[(x, c)]]
                    codomain = [x for x in pair_outputs[(a, b)] if d in pair_outputs[(c, x)]]
                    if not domain and not codomain:
                        continue
                    active += 1
                    direct = left_hexagon_direct(domain, codomain, r_data, c, d)
                    path = left_hexagon_path(labels, fusion, pair_outputs, f_data, r_data, a, b, c, d, domain, codomain)
                    error = matrix_error(path, direct)
                    if error > max_error:
                        max_error = error
                        worst = {"a": a, "b": b, "c": c, "d": d, "error": error}
    return {
        "status": "pass" if max_error <= COHERENCE_TOLERANCE else "fail",
        "active_tuple_count": active,
        "nonzero_fusion_spaces": active,
        "max_error": max_error,
        "worst_example": worst,
        "worst_sample": None if worst is None else [worst["a"], worst["b"], worst["c"], worst["d"]],
    }


def left_hexagon_direct(domain: list[str], codomain: list[str], r_data: RData, c: str, d: str) -> np.ndarray:
    result = np.zeros((len(codomain), len(domain)), dtype=complex)
    row_index = {item: idx for idx, item in enumerate(codomain)}
    for col, x in enumerate(domain):
        if x in row_index:
            result[row_index[x], col] = r_data.ab_to_ba((x, c, d))[0, 0]
    return result


def left_hexagon_path(
    labels: list[str],
    fusion: dict[tuple[str, str, str], int],
    pair_outputs: dict[tuple[str, str], list[str]],
    f_data: FData,
    r_data: RData,
    a: str,
    b: str,
    c: str,
    d: str,
    domain: list[str],
    codomain: list[str],
) -> np.ndarray:
    t1 = [y for y in pair_outputs[(b, c)] if d in pair_outputs[(a, y)]]
    t2 = [y for y in pair_outputs[(c, b)] if d in pair_outputs[(a, y)]]
    t3 = [z for z in pair_outputs[(a, c)] if d in pair_outputs[(z, b)]]
    t4 = [z for z in pair_outputs[(c, a)] if d in pair_outputs[(z, b)]]
    s1 = f_data.left_to_right((a, b, c, d))
    s2 = diagonal_braid(t1, t2, r_data, b, c)
    s3 = f_data.matrix((a, c, b, d))
    s4 = diagonal_braid(t3, t4, r_data, a, c)
    s5 = f_data.left_to_right((c, a, b, d))
    return restrict_rows_cols(s5 @ s4 @ s3 @ s2 @ s1, f_data.right_labels[(c, a, b, d)], codomain, domain, domain)


def diagonal_braid(source_labels: list[str], target_labels: list[str], r_data: RData, first: str, second: str) -> np.ndarray:
    result = np.zeros((len(target_labels), len(source_labels)), dtype=complex)
    row_index = {item: idx for idx, item in enumerate(target_labels)}
    for col, target in enumerate(source_labels):
        row = row_index.get(target)
        if row is not None:
            result[row, col] = r_data.ab_to_ba((first, second, target))[0, 0]
    return result


def restrict_rows_cols(
    matrix: np.ndarray,
    matrix_rows: list[str],
    desired_rows: list[str],
    matrix_cols: list[str],
    desired_cols: list[str],
) -> np.ndarray:
    row_indices = [matrix_rows.index(item) for item in desired_rows]
    col_indices = [matrix_cols.index(item) for item in desired_cols]
    return matrix[np.ix_(row_indices, col_indices)]


def matrix_error(left: np.ndarray, right: np.ndarray) -> float:
    if left.shape != right.shape:
        return float("inf")
    if left.size == 0:
        return 0.0
    return float(np.linalg.norm(left - right, ord=np.inf))


def build_skeleton_payload(
    *,
    args: argparse.Namespace,
    group: Dic12Group,
    simples: list[SimpleObject],
    fusion_rules: list[dict[str, Any]],
    homs: dict[tuple[str, str, str], list[np.ndarray]],
    started_utc: str,
    started: float,
) -> dict[str, Any]:
    labels = [simple.label for simple in simples]
    fusion_values = [len(homs[(a, b, c)]) for a in labels for b in labels for c in labels]
    identity_certificate = build_identity_certificate(group, simples)
    f_space_counter: Counter[int] = Counter()
    max_f_dim = 0
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    dim = sum(len(homs[(a, b, x)]) * len(homs[(x, c, d)]) for x in labels)
                    if dim:
                        f_space_counter[dim] += 1
                        max_f_dim = max(max_f_dim, dim)
    return {
        "schema": SCHEMA_SKELETON,
        "status": "WORKING_NUMERIC",
        "generator_script": "experiments/scripts/build_drinfeld_double_dic12_mtc_data.py",
        "argv": normalized_argv(args),
        "reproduce_command": "python experiments/scripts/build_drinfeld_double_dic12_mtc_data.py",
        "utc_start": started_utc,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "repo": repo_payload(),
        "tool_versions": tool_versions(),
        "group": group_payload(group),
        "identity_certificate": identity_certificate,
        "simple_labels": labels,
        "simple_objects": [simple_payload(group, simple) for simple in simples],
        "global_dimension_squared": sum(simple.quantum_dimension**2 for simple in simples),
        "fusion_rules": fusion_rules,
        "checks": {
            "group_order_12": len(group.elements) == 12,
            "presentation_a6": group_power(group, (1, 0), 6) == group.identity,
            "presentation_x2_a3": group.mul((0, 1), (0, 1)) == (3, 0),
            "presentation_xax_inverse": group.mul(group.mul((0, 1), (1, 0)), group.inv((0, 1))) == group.inv((1, 0)),
            "simple_count_32": len(simples) == 32,
            "global_dimension_squared_144": sum(simple.quantum_dimension**2 for simple in simples) == 144,
            "fusion_integral": all(isinstance(value, int) for value in fusion_values),
            "fusion_nonnegative": all(value >= 0 for value in fusion_values),
            "max_fusion_multiplicity_1": max(fusion_values) == 1,
            "max_three_object_fusion_space_5": max_f_dim == 5,
        },
        "fusion_summary": {
            "nonzero_triples": sum(1 for value in fusion_values if value),
            "max_fusion_multiplicity": max(fusion_values),
            "max_three_object_fusion_space_dimension": max_f_dim,
            "three_object_fusion_space_dimension_distribution": dict(sorted(f_space_counter.items())),
        },
    }


def build_fr_payload(
    *,
    args: argparse.Namespace,
    group: Dic12Group,
    simples: list[SimpleObject],
    homs: dict[tuple[str, str, str], list[np.ndarray]],
    fusion_rules: list[dict[str, Any]],
    f_blocks: list[dict[str, Any]],
    r_blocks: list[dict[str, Any]],
    f_summary: dict[str, Any],
    r_summary: dict[str, Any],
    coherence: dict[str, Any],
    started_utc: str,
    started: float,
) -> dict[str, Any]:
    labels = [simple.label for simple in simples]
    status = "WORKING_NUMERIC"
    identity_certificate = build_identity_certificate(group, simples)
    fusion = fusion_lookup(fusion_rules)
    supplementary = supplementary_checks(
        group=group,
        simples=simples,
        homs=homs,
        fusion=fusion,
        f_blocks=f_blocks,
        r_blocks=r_blocks,
        f_summary=f_summary,
        r_summary=r_summary,
        coherence=coherence,
    )
    return {
        "schema": SCHEMA_FR,
        "status": status,
        "mtc_id": MTC_ID,
        "name": "untwisted Drinfeld double D(Dic_12)",
        "generator_script": "experiments/scripts/build_drinfeld_double_dic12_mtc_data.py",
        "argv": normalized_argv(args),
        "reproduce_command": "python experiments/scripts/build_drinfeld_double_dic12_mtc_data.py",
        "utc_start": started_utc,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "repo": repo_payload(),
        "tool_versions": tool_versions(),
        "mathematical_object": {
            "family": "Drinfeld double of Dic_12",
            "group": {
                "name": "Dic_12",
                "order": 12,
                "presentation": "<a,x | a^6=1, x^2=a^3, x a x^-1=a^-1>",
                "convention": "Dic_12 means dicyclic group of order 12.",
            },
            "twisting": {"kind": "untwisted", "omega_class": 0},
        },
        "identity_certificate": identity_certificate,
        "claim_boundary": {
            "established_if_verified": (
                "Reproducible numeric F/R-symbol data for untwisted D(Dic_12), "
                "under the documented basis/gauge convention, after the independent verifier passes."
            ),
            "not_claimed": [
                "Exact arithmetic proof",
                "Twisted cocycle-family data",
                "Downstream Kirby/link evaluator integration",
                "Convention-independent universal compatibility",
                "CTL admission",
            ],
            "coherence_tolerance": COHERENCE_TOLERANCE,
            "fr_reconstruction_tolerance": FR_TOLERANCE,
        },
        "field": "complex floating point",
        "basis_convention": {
            "simple_label_order": "Conjugacy classes ordered 1A, aA, a2A, a3A, xA, axA; centralizer irreps ordered as listed in simple_objects.",
            "simple_module_basis": "For class representative r, basis vectors are transporter-selected class elements g=t r t^-1 followed by the centralizer-representation basis index.",
            "fusion_space": "Hom(a tensor b, c), maps c <- a tensor b; basis is the deterministic SVD nullspace basis of grading-preserving G-intertwiners, phase-fixed by the largest entry.",
            "F_block": "columns are right-associated tree basis vectors expressed in the left-associated tree basis",
            "R_block": "columns are Hom(b tensor a, c) basis vectors braided into Hom(a tensor b, c)",
        },
        "simple_labels": labels,
        "simple_objects": [simple_payload(group, simple) for simple in simples],
        "global_dimension_squared": sum(simple.quantum_dimension**2 for simple in simples),
        "fusion_rules": fusion_rules,
        "fr_symbols": {
            "f_blocks": f_blocks,
            "r_blocks": r_blocks,
        },
        "counts": {
            "simple_objects": len(labels),
            "nonzero_f_blocks": len(f_blocks),
            "nonzero_r_blocks": len(r_blocks),
            "max_f_block_size": supplementary["counts"]["max_f_block_size"],
            "max_r_block_size": supplementary["counts"]["max_r_block_size"],
        },
        "checks_imported_from_final_fr_artifact": supplementary["checks"],
        "max_errors": {
            "f_reconstruction": f_summary["max_reconstruction_error"],
            "r_reconstruction": r_summary["max_reconstruction_error"],
        },
        "supplementary_equation_checks": supplementary["equation_checks"],
        "f_space_dimension_distribution": f_summary["dimension_distribution"],
        "coherence_certificate": coherence,
    }


def supplementary_checks(
    *,
    group: Dic12Group,
    simples: list[SimpleObject],
    homs: dict[tuple[str, str, str], list[np.ndarray]],
    fusion: dict[tuple[str, str, str], int],
    f_blocks: list[dict[str, Any]],
    r_blocks: list[dict[str, Any]],
    f_summary: dict[str, Any],
    r_summary: dict[str, Any],
    coherence: dict[str, Any],
) -> dict[str, Any]:
    labels = [simple.label for simple in simples]
    f_sizes = [block["right_to_left"]["rows"] for block in f_blocks]
    r_sizes = [block["ba_to_ab"]["rows"] for block in r_blocks]
    hom_dims_match = all(len(homs[(a, b, c)]) == fusion[(a, b, c)] for a in labels for b in labels for c in labels)
    equation_checks = modular_equation_checks(group, simples, fusion, r_blocks)
    checks = {
        "all_f_blocks_reconstruct": f_summary["max_reconstruction_error"] <= FR_TOLERANCE,
        "all_r_blocks_reconstruct": r_summary["max_reconstruction_error"] <= FR_TOLERANCE,
        "pair_hom_dimensions_match_fusion": hom_dims_match,
        "s_from_r_matches_object_s": equation_checks["s_from_r_matches_object_s"]["max_error"] <= FR_TOLERANCE,
        "s_from_twist_fusion_matches_object_s": equation_checks["s_from_twist_fusion_matches_object_s"]["max_error"] <= FR_TOLERANCE,
        "balancing_ribbon_scalars": equation_checks["balancing_ribbon_scalars"]["max_error"] <= FR_TOLERANCE,
        "selected_pentagons": coherence["scans"]["pentagon"]["max_error"] <= COHERENCE_TOLERANCE,
        "selected_right_hexagons": coherence["scans"]["right_hexagon"]["max_error"] <= COHERENCE_TOLERANCE,
        "selected_left_hexagons": coherence["scans"]["left_hexagon"]["max_error"] <= COHERENCE_TOLERANCE,
        "t_twists_nonzero": all(simple.twist["root_order"] > 0 for simple in simples),
    }
    return {
        "checks": checks,
        "counts": {
            "max_f_block_size": max(f_sizes) if f_sizes else 0,
            "max_r_block_size": max(r_sizes) if r_sizes else 0,
        },
        "equation_checks": equation_checks,
    }


def modular_equation_checks(
    group: Dic12Group,
    simples: list[SimpleObject],
    fusion: dict[tuple[str, str, str], int],
    r_blocks: list[dict[str, Any]],
) -> dict[str, Any]:
    labels = [simple.label for simple in simples]
    simple_by_label = {simple.label: simple for simple in simples}
    r_data = RData.from_blocks(r_blocks)
    s_from_r = s_matrix_from_r(labels, simple_by_label, fusion, r_data)
    s_from_twist = s_matrix_from_twist_fusion(labels, simple_by_label, fusion)
    s_from_object = s_matrix_from_object_formula(group, simples)
    balancing_error, balancing_worst = balancing_error_from_r(labels, simple_by_label, fusion, r_data)
    return {
        "balancing_ribbon_scalars": {
            "formula": "R_ab^c R_ba^c = theta_c / (theta_a theta_b) in the serialized ba_to_ab convention",
            "max_error": balancing_error,
            "worst_example": balancing_worst,
        },
        "s_from_r_matches_object_s": {
            "formula": "S_ab = |G|^-1 sum_c N_ab^c R_ab^c R_ba^c dim(c), compared with the Drinfeld-double character formula",
            "max_error": float(np.max(np.abs(s_from_r - s_from_object))),
        },
        "s_from_twist_fusion_matches_object_s": {
            "formula": "S_ab = |G|^-1 sum_c N_ab^c theta_c/(theta_a theta_b) dim(c), compared with the Drinfeld-double character formula",
            "max_error": float(np.max(np.abs(s_from_twist - s_from_object))),
        },
        "s_matrix_unit_row": {
            "formula": "S_0a = dim(a)/|G|",
            "max_error": float(
                max(abs(s_from_object[0, idx] - simple.quantum_dimension / len(group.elements)) for idx, simple in enumerate(simples))
            ),
        },
    }


def theta_complex(simple: SimpleObject) -> complex:
    twist = simple.twist
    return np.exp(2j * np.pi * twist["exponent"] / twist["root_order"])


def s_matrix_from_r(
    labels: list[str],
    simple_by_label: dict[str, SimpleObject],
    fusion: dict[tuple[str, str, str], int],
    r_data: RData,
) -> np.ndarray:
    total_dimension = sum(simple.quantum_dimension**2 for simple in simple_by_label.values()) ** 0.5
    matrix = np.zeros((len(labels), len(labels)), dtype=complex)
    for row, a in enumerate(labels):
        for col, b in enumerate(labels):
            value = 0j
            for c in labels:
                if fusion[(a, b, c)]:
                    value += (
                        r_data.matrices[(a, b, c)][0, 0]
                        * r_data.matrices[(b, a, c)][0, 0]
                        * simple_by_label[c].quantum_dimension
                    )
            matrix[row, col] = value / total_dimension
    return matrix


def s_matrix_from_twist_fusion(
    labels: list[str],
    simple_by_label: dict[str, SimpleObject],
    fusion: dict[tuple[str, str, str], int],
) -> np.ndarray:
    total_dimension = sum(simple.quantum_dimension**2 for simple in simple_by_label.values()) ** 0.5
    matrix = np.zeros((len(labels), len(labels)), dtype=complex)
    for row, a in enumerate(labels):
        for col, b in enumerate(labels):
            theta_ab = theta_complex(simple_by_label[a]) * theta_complex(simple_by_label[b])
            value = 0j
            for c in labels:
                if fusion[(a, b, c)]:
                    value += theta_complex(simple_by_label[c]) / theta_ab * simple_by_label[c].quantum_dimension
            matrix[row, col] = value / total_dimension
    return matrix


def s_matrix_from_object_formula(group: Dic12Group, simples: list[SimpleObject]) -> np.ndarray:
    total_dimension = len(group.elements)
    transporters = {
        (cls["label"], element): cls["transporters"][element]
        for cls in group.classes
        for element in cls["elements"]
    }
    matrix = np.zeros((len(simples), len(simples)), dtype=complex)
    for row, left in enumerate(simples):
        for col, right in enumerate(simples):
            value = 0j
            for g_elem in left.class_elements:
                t_g = transporters[(left.class_label, g_elem)]
                for h_elem in right.class_elements:
                    if group.mul(g_elem, h_elem) != group.mul(h_elem, g_elem):
                        continue
                    t_h = transporters[(right.class_label, h_elem)]
                    h_central = group.mul(group.mul(group.inv(t_g), h_elem), t_g)
                    g_central = group.mul(group.mul(group.inv(t_h), g_elem), t_h)
                    value += (
                        np.trace(left.centralizer_rep.matrix(group, h_central))
                        * np.trace(right.centralizer_rep.matrix(group, g_central))
                    )
            matrix[row, col] = value / total_dimension
    return matrix


def balancing_error_from_r(
    labels: list[str],
    simple_by_label: dict[str, SimpleObject],
    fusion: dict[tuple[str, str, str], int],
    r_data: RData,
) -> tuple[float, dict[str, Any] | None]:
    max_error = 0.0
    worst = None
    for a in labels:
        for b in labels:
            for c in labels:
                if not fusion[(a, b, c)]:
                    continue
                observed = r_data.matrices[(a, b, c)][0, 0] * r_data.matrices[(b, a, c)][0, 0]
                expected = theta_complex(simple_by_label[c]) / (theta_complex(simple_by_label[a]) * theta_complex(simple_by_label[b]))
                error = abs(observed - expected)
                if error > max_error:
                    max_error = float(error)
                    worst = {"a": a, "b": b, "c": c, "error": float(error)}
    return max_error, worst


def build_construction_payload(
    *,
    group: Dic12Group,
    simples: list[SimpleObject],
    skeleton_path: Path,
    fr_path: Path,
) -> dict[str, Any]:
    identity_certificate = build_identity_certificate(group, simples)
    return {
        "schema": SCHEMA_CONSTRUCTION,
        "status": "WORKING_NUMERIC_CONSTRUCTION_ACCOUNT",
        "title": "Construction account for untwisted Drinfeld double D(Dic_12) numeric F/R data",
        "purpose": "Record the construction route for working numeric F/R-symbol artifacts before any CTL admission.",
        "claim_boundary": {
            "not_admitted_to_ctl": True,
            "not_claimed": [
                "Exact arithmetic proof",
                "Twisted cocycle-family data",
                "Downstream link or Kirby evaluator integration",
            ],
        },
        "categorical_model": {
            "category": "Z(Vec_Dic12), equivalently Rep(D(Dic_12))",
            "object_model": "Untwisted Yetter-Drinfeld modules over Dic_12.",
            "braiding": "For homogeneous v_g, c(v_g tensor w)=g.w tensor v_g.",
            "associator": "Strict vector-space associator; nontrivial F-symbols arise from the chosen simple-channel Hom bases.",
        },
        "identity_certificate": identity_certificate,
        "group_data": group_payload(group),
        "simple_object_recipe": {
            "classification": "Pairs (conjugacy class C, irreducible representation rho of Z_G(r_C)).",
            "simple_count": len(simples),
            "global_dimension_squared": sum(simple.quantum_dimension**2 for simple in simples),
        },
        "fr_extraction_recipe": {
            "hom_basis": "Grading-preserving G-intertwiner nullspaces in Hom(a tensor b, c), SVD-normalized and phase-fixed.",
            "F": "Compare composites T_{x,c}^d (T_{a,b}^x tensor id_c) and T_{a,y}^d (id_a tensor T_{b,c}^y).",
            "R": "Compare T_{b,a}^c after the Yetter-Drinfeld braiding against the Hom(a tensor b, c) basis.",
            "coherence": "Pentagon and two hexagon scans are performed from the serialized F/R blocks.",
        },
        "working_artifacts": [
            {"role": "fusion_skeleton", "path": rel(skeleton_path), "schema": SCHEMA_SKELETON},
            {"role": "fr_data", "path": rel(fr_path), "schema": SCHEMA_FR},
        ],
    }


def build_identity_certificate(group: Dic12Group, simples: list[SimpleObject]) -> dict[str, Any]:
    class_sizes = [len(item["elements"]) for item in group.classes]
    centralizer_orders = [len(item["centralizer"]) for item in group.classes]
    centralizer_types = {
        "1A": "Dic_12",
        "aA": "C6",
        "a2A": "C6",
        "a3A": "Dic_12",
        "xA": "C4",
        "axA": "C4",
    }
    labels_by_class: dict[str, list[str]] = {}
    qdims_by_class: dict[str, list[int]] = {}
    centralizer_rep_dimensions_by_class: dict[str, list[int]] = {}
    for simple in simples:
        labels_by_class.setdefault(simple.class_label, []).append(simple.label)
        qdims_by_class.setdefault(simple.class_label, []).append(simple.quantum_dimension)
        centralizer_rep_dimensions_by_class.setdefault(simple.class_label, []).append(simple.centralizer_rep.dimension)
    qdim_distribution = Counter(str(simple.quantum_dimension) for simple in simples)
    twist_distribution = Counter(f"{simple.twist['root_order']}:{simple.twist['exponent']}" for simple in simples)
    return {
        "claimed_category": "Rep(D(Dic_12)) = Z(Vec_Dic12)",
        "identity_status": "WORKING_NUMERIC_IDENTITY_CERTIFICATE",
        "group_signature": {
            "name": "Dic_12",
            "convention": "dicyclic group of order 12",
            "presentation": "<a,x | a^6=1, x^2=a^3, x a x^-1=a^-1>",
            "order": len(group.elements),
            "element_encoding": "a^i x^j encoded as [i,j] with i mod 6 and j in {0,1}",
            "conjugacy_class_labels": [item["label"] for item in group.classes],
            "conjugacy_class_representatives": [group.fmt(item["representative"]) for item in group.classes],
            "conjugacy_class_sizes": class_sizes,
            "centralizer_orders": centralizer_orders,
            "centralizer_types": centralizer_types,
            "distinguishes_from_A4": "Dic_12 has six conjugacy classes with sizes [1,2,2,1,3,3]; A4 has four conjugacy classes with sizes [1,3,4,4].",
        },
        "double_simple_object_signature": {
            "classification": "simple objects are pairs (conjugacy class C, irreducible representation rho of Z_G(r_C))",
            "simple_count": len(simples),
            "labels_by_class": labels_by_class,
            "centralizer_rep_dimensions_by_class": centralizer_rep_dimensions_by_class,
            "quantum_dimensions_by_class": qdims_by_class,
            "quantum_dimension_distribution": dict(sorted(qdim_distribution.items(), key=lambda item: int(item[0]))),
            "dimension_formula": "qdim(C,rho)=|C|*dim(rho)",
            "global_dimension_squared": sum(simple.quantum_dimension**2 for simple in simples),
            "expected_global_dimension_squared": len(group.elements) ** 2,
        },
        "twist_signature": {
            "t_spectrum": dict(sorted(twist_distribution.items())),
            "twist_formula": "theta_(C,rho)=rho(r_C)/dim(rho) for untwisted D(G)",
        },
        "modular_identity_cross_checks": {
            "object_s_formula": "S_ab = |G|^-1 sum_{g in C_a, h in C_b, gh=hg} chi_a(t_g^-1 h t_g) chi_b(t_h^-1 g t_h)",
            "s_from_r_and_s_from_twist_fusion_are_checked_against_object_s": True,
            "balancing_ribbon_scalars_checked": True,
        },
    }


def group_payload(group: Dic12Group) -> dict[str, Any]:
    return {
        "name": "Dic_12",
        "order": 12,
        "presentation": "<a,x | a^6=1, x^2=a^3, x a x^-1=a^-1>",
        "element_encoding": "a^i x^j encoded as [i,j] with i mod 6 and j in {0,1}",
        "elements": [{"encoded": list(g), "label": group.fmt(g)} for g in group.elements],
        "conjugacy_classes": [
            {
                "label": item["label"],
                "representative": group.fmt(item["representative"]),
                "elements": [group.fmt(g) for g in item["elements"]],
                "centralizer": [group.fmt(g) for g in item["centralizer"]],
                "centralizer_size": len(item["centralizer"]),
            }
            for item in group.classes
        ],
    }


def simple_payload(group: Dic12Group, simple: SimpleObject) -> dict[str, Any]:
    return {
        "label": simple.label,
        "class_label": simple.class_label,
        "class_representative": group.fmt(simple.class_representative),
        "class_elements": [group.fmt(g) for g in simple.class_elements],
        "centralizer_size": len(simple.centralizer),
        "centralizer_rep_label": simple.centralizer_rep.label,
        "centralizer_rep_kind": simple.centralizer_rep.kind,
        "centralizer_rep_dimension": simple.centralizer_rep.dimension,
        "quantum_dimension": simple.quantum_dimension,
        "twist": simple.twist,
    }


def group_power(group: Dic12Group, element: Element, power: int) -> Element:
    result = group.identity
    for _ in range(power):
        result = group.mul(result, element)
    return result


def sparse_matrix_payload(matrix: np.ndarray) -> dict[str, Any]:
    entries = []
    for row in range(matrix.shape[0]):
        for col in range(matrix.shape[1]):
            value = matrix[row, col]
            if abs(value) > SPARSE_TOLERANCE:
                entries.append({"row": row, "column": col, "value": complex_payload(value)})
    return {"rows": matrix.shape[0], "columns": matrix.shape[1], "entries": entries}


def matrix_from_payload(payload: dict[str, Any]) -> np.ndarray:
    matrix = np.zeros((payload["rows"], payload["columns"]), dtype=complex)
    for entry in payload["entries"]:
        matrix[entry["row"], entry["column"]] = complex(float(entry["value"]["real"]), float(entry["value"]["imag"]))
    return matrix


def complex_payload(value: complex) -> dict[str, str]:
    real = 0.0 if abs(value.real) < SPARSE_TOLERANCE else float(value.real)
    imag = 0.0 if abs(value.imag) < SPARSE_TOLERANCE else float(value.imag)
    return {"real": format(real, ".17g"), "imag": format(imag, ".17g")}


def normalized_argv(args: argparse.Namespace) -> list[str]:
    argv = ["python", "experiments/scripts/build_drinfeld_double_dic12_mtc_data.py"]
    if args.output_dir != OUTPUT_DIR:
        argv += ["--output-dir", str(args.output_dir)]
    if getattr(args, "write_verification_hint", False):
        argv.append("--write-verification-hint")
    return argv


def repo_payload() -> dict[str, Any]:
    status = command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(status),
        "status_short": status,
    }


def tool_versions() -> dict[str, Any]:
    return {"python": sys.version, "numpy": np.__version__}


def command(argv: list[str]) -> str:
    return subprocess.check_output(argv, cwd=REPO_ROOT, text=True).strip()


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    raise SystemExit(main())
