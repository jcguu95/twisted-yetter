"""Diagnose old SU(2)_2 braid oracle against generic SU(2)_k evaluator."""

from __future__ import annotations

import importlib.util
from itertools import product
from pathlib import Path
import sys

from sage.all import ComplexField


REPO_ROOT = Path(__file__).resolve().parents[2]
OLD_ORACLE = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"
GENERIC = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"

N_STRANDS = 5
BRAID_WORD = (
    1,
    1,
    2,
    3,
    3,
    2,
    1,
    2,
    3,
    2,
    2,
    -4,
    3,
    2,
    1,
    2,
    3,
    3,
    2,
    3,
    4,
    -3,
)
TOTAL_FRAMINGS = (4, 4, 1)
EXTRA_FRAMINGS = (2, 4, 1)
TOLERANCE = 1e-8


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main():
    old = load_module(OLD_ORACLE, "old_su2_2_braid_oracle_for_sector_diff")
    generic = load_module(GENERIC, "generic_su2k_for_sector_diff")
    evaluator = generic.SU2KBraidEvaluator(2, exact=False, precision=160)
    cf = ComplexField(80)
    print("blackboard_self_writhe", evaluator.blackboard_self_writhe(N_STRANDS, BRAID_WORD))
    print("total_framings", TOTAL_FRAMINGS)
    print("extra_framings", EXTRA_FRAMINGS)
    print("omega_old_total", old.omega_value(N_STRANDS, BRAID_WORD, TOTAL_FRAMINGS, (0, 0, 0)))
    print("omega_old_extra", old.omega_value(N_STRANDS, BRAID_WORD, EXTRA_FRAMINGS, (0, 0, 0)))
    print("omega_generic_total", evaluator.omega_value(N_STRANDS, BRAID_WORD, TOTAL_FRAMINGS, (0, 0, 0)))
    print("omega_generic_extra", evaluator.omega_value(N_STRANDS, BRAID_WORD, EXTRA_FRAMINGS, (0, 0, 0)))
    print("mismatching fixed sectors:")
    for labels in product((0, 1, 2), repeat=3):
        old_value = old.fixed_label_rt_value(N_STRANDS, BRAID_WORD, labels, TOTAL_FRAMINGS)
        generic_value = evaluator.fixed_label_value(N_STRANDS, BRAID_WORD, labels, TOTAL_FRAMINGS)
        difference = abs(cf(old_value) - cf(generic_value))
        if difference > TOLERANCE:
            print(labels, old_value, generic_value, difference)


if __name__ == "__main__":
    main()
