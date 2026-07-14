"""Explicit rank-two symmetric pointed categories for numeric controls."""

from __future__ import annotations

from functools import lru_cache
from pathlib import Path

from experiments.sage.morse_pivotal_contract import load_pivotal_profile


PIVOTAL_PROFILE_PATH = (
    Path(__file__).resolve().parents[1]
    / "inputs/category-pivotal/pointed-z2-symmetric-pivotal-v1.json"
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
