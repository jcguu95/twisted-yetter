"""Explicit rank-two pointed categories for numeric controls."""

from __future__ import annotations

import cmath
from functools import lru_cache
from pathlib import Path
from typing import Any

from experiments.sage.morse_pivotal_contract import load_pivotal_profile


PIVOTAL_PROFILE_PATH = (
    Path(__file__).resolve().parents[1]
    / "inputs/category-pivotal/pointed-z2-symmetric-pivotal-v1.json"
)
SEMION_PIVOTAL_PROFILE_PATH = (
    Path(__file__).resolve().parents[1]
    / "inputs/category-pivotal/rank2-z2-semion-pivotal-v1.json"
)


class SymmetricZ2PremodularCategory:
    """Rep(Z2) or sVec in an explicit orthonormal pointed gauge."""

    labels = (0, 1)
    unit = 0
    path_basis_is_orthonormal = True

    def __init__(self, *, fermionic: bool):
        self.fermionic = bool(fermionic)
        self.category_id = "svec" if self.fermionic else "rep-z2"
        self.pivotal_profile = load_pivotal_profile(PIVOTAL_PROFILE_PATH)

    @staticmethod
    def dimension(_label):
        return 1.0

    def twist(self, label):
        return -1.0 if self.fermionic and label == 1 else 1.0

    @staticmethod
    def dual(label):
        return label

    @staticmethod
    def fusion_multiplicity(left, right, output):
        return int(output == (left ^ right))

    @staticmethod
    def fusion_outputs(left, right):
        return ((left ^ right, 1),)

    @staticmethod
    @lru_cache(maxsize=None)
    def f_block(a, b, c, _d):
        left = (a ^ b, 0, 0)
        right = (b ^ c, 0, 0)
        matrix = ((1.0 + 0.0j,),)
        return {
            "left_basis": (left,),
            "right_basis": (right,),
            "left_index": {left: 0},
            "right_index": {right: 0},
            "right_to_left": matrix,
            "left_to_right": matrix,
        }

    def r_matrix(self, left, right, _output, _positive):
        value = -1.0 if self.fermionic and left == right == 1 else 1.0
        return ((value + 0.0j,),)

    @staticmethod
    def reverse_bend(_label):
        return 1.0 + 0.0j

    @staticmethod
    def cost_profile():
        return {"f": 1.0, "r": 1.0, "source": "explicit pointed Z2 data"}


class Rank2Z2SemionModularCategory:
    """Semion or anti-semion in the checked pointed Z2 ribbon gauge."""

    labels = (0, 1)
    unit = 0
    path_basis_is_orthonormal = True

    def __init__(self, *, branch: str):
        if branch not in {"plus", "minus"}:
            raise ValueError("branch must be 'plus' or 'minus'")
        self.branch = branch
        self.category_id = f"rank2-cyclic-z2-semion-{branch}"
        self.pivotal_profile = load_pivotal_profile(SEMION_PIVOTAL_PROFILE_PATH)

    @staticmethod
    def dimension(_label):
        return 1.0

    def twist(self, label):
        if label == 0:
            return 1.0 + 0.0j
        return 1.0j if self.branch == "plus" else -1.0j

    @staticmethod
    def dual(label):
        return label

    @staticmethod
    def fusion_multiplicity(left, right, output):
        return int(output == (left ^ right))

    @staticmethod
    def fusion_outputs(left, right):
        return ((left ^ right, 1),)

    @staticmethod
    @lru_cache(maxsize=None)
    def f_block(a, b, c, _d):
        left = (a ^ b, 0, 0)
        right = (b ^ c, 0, 0)
        value = -1.0 + 0.0j if a == b == c == 1 else 1.0 + 0.0j
        matrix = ((value,),)
        return {
            "left_basis": (left,),
            "right_basis": (right,),
            "left_index": {left: 0},
            "right_index": {right: 0},
            "right_to_left": matrix,
            "left_to_right": matrix,
        }

    def r_matrix(self, left, right, _output, positive):
        value = self.twist(1) if left == right == 1 else 1.0 + 0.0j
        if not positive:
            value = 1.0 / value
        return ((value,),)

    @staticmethod
    def reverse_bend(_label):
        return 1.0 + 0.0j

    @staticmethod
    def cost_profile():
        return {
            "f": 1.0,
            "r": 1.0,
            "source": "rank2 cyclic Z2 semion ribbon snapshot gauge",
        }


def _phase(expression: str) -> complex:
    text = str(expression).strip()
    if text == "1":
        return 1.0 + 0.0j
    if text == "-1":
        return -1.0 + 0.0j
    if text == "i":
        return 1.0j
    if text == "-i":
        return -1.0j
    if text.startswith("zeta"):
        base, _, exponent_text = text.partition("^")
        order = int(base.removeprefix("zeta"))
        exponent = int(exponent_text or "1")
        return cmath.exp(2.0j * cmath.pi * exponent / order)
    if text.startswith("(") and ")*(" in text:
        factors = text.replace("(", "").replace(")", "").split("*")
        value = 1.0 + 0.0j
        for factor in factors:
            value *= _phase(factor)
        return value
    raise ValueError(f"unsupported phase expression: {expression!r}")


class SnapshotPointedModularCategory:
    """Pointed modular category materialized from a resolved snapshot."""

    path_basis_is_orthonormal = True

    def __init__(self, snapshot: dict[str, Any]):
        if snapshot.get("status") != "RESOLVED_RIBBON_REALIZATION":
            raise ValueError("snapshot is not a resolved ribbon realization")
        data = snapshot["category_data"]
        dimensions = data.get("dimensions", {})
        if set(dimensions.values()) != {"1"}:
            raise ValueError("snapshot is not pointed with all dimensions one")
        self.snapshot = snapshot
        self.category_data = data
        self.category_id = data["category_id"]
        self.labels = tuple(data["labels"])
        self.unit = data["unit"]
        self.modular_killing_loop_certificate = {
            "status": "PASS",
            "evidence_kind": "ribbon_realization_snapshot",
            "snapshot_content_hash": snapshot["content_hash"],
            "category_data_hash": snapshot["category_data_hash"],
        }
        self.pivotal_profile = {
            "schema": "twisted-yetter.morse-pivotal-profile.v1",
            "status": "SUPPORTED_FOR_NUMERIC_MORSE_CONTROLS",
            "category_ids": [self.category_id],
            "capabilities": {
                "rigid_bends": True,
                "ribbon_twist": True,
                "trivalent_pairing": True,
                "vacuum_projector": True,
            },
            "duality": {"convention": "snapshot-provided dual map"},
            "evaluation_coevaluation": {
                "normalization": "sqrt(quantum_dimension)"
            },
            "pivotal_structure": {
                "convention": "snapshot-provided positive pointed pivotal data"
            },
            "fusion_space_pairing": {
                "basis": data["fusion_pairing"],
                "orthonormal": True,
            },
            "reverse_bend_scalars": {
                "kind": "explicit-map",
                "values": {str(label): [1.0, 0.0] for label in self.labels},
            },
            "evidence": [
                {
                    "kind": "resolved-ribbon-realization-snapshot",
                    "snapshot_content_hash": snapshot["content_hash"],
                }
            ],
        }

    @staticmethod
    def dimension(_label):
        return 1.0

    def twist(self, label):
        return _phase(self.category_data["twists"][str(label)])

    def dual(self, label):
        return self.category_data["duals"][str(label)]

    def _fusion_output(self, left, right):
        fusion = self.category_data["fusion"][f"{left}*{right}"]
        if isinstance(fusion, dict):
            nonzero = [output for output, multiplicity in fusion.items() if multiplicity]
            if len(nonzero) != 1:
                raise ValueError("pointed fusion entry is not single-output")
            return nonzero[0]
        return fusion

    def fusion_multiplicity(self, left, right, output):
        return int(str(output) == self._fusion_output(left, right))

    def fusion_outputs(self, left, right):
        return ((self._fusion_output(left, right), 1),)

    def _f_symbol(self, a, b, c):
        f_symbols = self.category_data["f_symbols"]
        if isinstance(f_symbols, str):
            if "strict pointed gauge" in f_symbols:
                return 1.0 + 0.0j
            raise ValueError(f"unsupported F-symbol declaration: {f_symbols!r}")
        associator = f_symbols.get("associator")
        if associator == "omega(a,b,c)=(-1)^(a*b*c)":
            return -1.0 + 0.0j if a == b == c == "1" else 1.0 + 0.0j
        if "omega_m(a,b,c)" in str(associator):
            modulus = len(self.labels)
            parameter_m = int(f_symbols["parameter_m"])
            ai = int(a)
            bi = int(b)
            ci = int(c)
            wrap = bi + ci - ((bi + ci) % modulus)
            return cmath.exp(2.0j * cmath.pi * parameter_m * ai * wrap / 16)
        table = f_symbols.get("associator_table")
        if isinstance(table, dict):
            return _phase(table[f"omega({a},{b},{c})"])
        raise ValueError("unsupported snapshot F-symbol data")

    def f_block(self, a, b, c, _d):
        left = (self._fusion_output(a, b), 0, 0)
        right = (self._fusion_output(b, c), 0, 0)
        value = self._f_symbol(str(a), str(b), str(c))
        matrix = ((value,),)
        return {
            "left_basis": (left,),
            "right_basis": (right,),
            "left_index": {left: 0},
            "right_index": {right: 0},
            "right_to_left": matrix,
            "left_to_right": ((1.0 / value,),),
        }

    def _r_symbol(self, left, right, output):
        r_symbols = self.category_data["r_symbols"]
        keys = (
            f"{left},{right}",
            f"R_{left}_{right}_to_{output}",
            f"R_{left}{right}_to_{output}",
        )
        for key in keys:
            if key in r_symbols:
                return _phase(r_symbols[key])
        if r_symbols.get("all_other_channels") == "1":
            return 1.0 + 0.0j
        raise ValueError(f"missing R-symbol for {left!r}, {right!r} -> {output!r}")

    def r_matrix(self, left, right, output, positive):
        if positive:
            value = self._r_symbol(str(left), str(right), str(output))
        else:
            # A negative crossing maps left*right to right*left by the inverse
            # of the opposite braiding.  Symmetric examples hide this
            # distinction; non-symmetric Z2xZ2 snapshots do not.
            value = self._r_symbol(str(right), str(left), str(output))
            value = 1.0 / value
        return ((value,),)

    @staticmethod
    def reverse_bend(_label):
        return 1.0 + 0.0j

    @staticmethod
    def cost_profile():
        return {
            "f": 1.0,
            "r": 1.0,
            "source": "resolved pointed ribbon realization snapshot",
        }
