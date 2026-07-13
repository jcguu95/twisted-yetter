"""Shared category registry for the native Morse evaluator tooling."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys

import numpy as np

from experiments.sage.morse_category_adapters import (
    LoadedFRMorseAdapter,
    SU2KMorseAdapter,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
SU2_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
SU3_PATH = REPO_ROOT / "experiments" / "sage" / "su3_2_anyonwiki_fr_braid_evaluator.py"
GENERIC_FR_PATH = (
    REPO_ROOT
    / "experiments"
    / "sage"
    / "yasui_figure3_a3_da4_untwisted_chunked.sage.py"
)
MTC_ROOT = REPO_ROOT / "experiments" / "results" / "mtc-candidates"

CATEGORY_CHOICES = ("su2", "su3-2", "dic3", "da4", "da4-c3w1")

_PAYLOADS = {
    "dic3": MTC_ROOT / "drinfeld-double-dic12-omega0-mtc-fr-data-v1.json",
    "da4": MTC_ROOT / "drinfeld-double-a4-omega0-mtc-fr-data-v1.json",
    "da4-c3w1": MTC_ROOT / "drinfeld-double-a4-c3w1-mtc-fr-data-v1.json",
}

_DISPLAY_NAMES = {
    "dic3": "D(Dic_3)=D(Dic_12-order-12)",
    "da4": "D(A4) untwisted",
    "da4-c3w1": "D(A4) c3w1 twisted category",
}

_DA4_C3_DEGREE_BY_FLUX_CLASS = {"1A": 0, "2A": 0, "3A": 1, "3B": 2}

_DIC3_WITNESS_CHI_BY_CLASS = {
    "1A": 1,
    "aA": -1,
    "a2A": 1,
    "a3A": -1,
    "xA": 1j,
    "axA": -1j,
}


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def da4_c3_character(character_label, simple_label) -> complex:
    character = int(character_label) % 3
    flux_class = simple_label.split(":", 1)[0]
    degree = _DA4_C3_DEGREE_BY_FLUX_CLASS[flux_class]
    return complex(np.exp(2j * np.pi * character * degree / 3))


def _dic3_witness_z_scalar(rep: str) -> complex:
    for prefix in ("lin", "rho", "chi", "eta"):
        if rep.startswith(prefix):
            return complex((-1) ** int(rep[len(prefix) :]))
    raise ValueError(f"unknown D(Dic_3) centralizer irrep label: {rep!r}")


def dic3_witness_character(character_label, simple_label) -> complex:
    power = int(character_label) % 4
    class_name, rep = simple_label.split(":", 1)
    monodromy = complex(_DIC3_WITNESS_CHI_BY_CLASS[class_name]) * _dic3_witness_z_scalar(rep)
    return monodromy**power


def build_category(category_name: str, level: int | None = None):
    """Return ``(adapter, display_name, stable_category_id)``."""

    if category_name == "su2":
        if level not in {2, 3, 4, 5, 6, 8}:
            raise ValueError("--category su2 requires --level 2, 3, 4, 5, 6, or 8")
        module = load_module(SU2_PATH, f"su2k_native_morse_level_{level}")
        backend = module.SU2KBraidEvaluator(level, exact=False)
        return SU2KMorseAdapter(backend), f"SU(2)_{level}", f"su2-k{level}"

    if category_name == "su3-2":
        module = load_module(SU3_PATH, "su3_2_native_morse")
        backend = module.SU32AnyonWikiFRBraidEvaluator()
        return (
            LoadedFRMorseAdapter(
                backend,
                character=module.character_value,
                adapter_name="SU(3)_2 AnyonWiki FR",
            ),
            "SU(3)_2",
            "su3-k2-anyonwiki-fr",
        )

    if category_name in _PAYLOADS:
        module = load_module(
            GENERIC_FR_PATH, f"{category_name.replace('-', '_')}_native_morse_generic_fr"
        )
        payload_path = _PAYLOADS[category_name]
        payload = json.loads(payload_path.read_text())
        backend = module.DA4FRBraidEvaluator(payload)
        character = {
            "dic3": dic3_witness_character,
            "da4-c3w1": da4_c3_character,
        }.get(category_name)
        return (
            LoadedFRMorseAdapter(
                backend,
                character=character,
                adapter_name=f"{_DISPLAY_NAMES[category_name]} numeric FR",
            ),
            _DISPLAY_NAMES[category_name],
            payload.get("mtc_id", category_name),
        )

    raise ValueError(f"unknown category: {category_name!r}")


def category_payload_path(category_name: str) -> Path | None:
    return _PAYLOADS.get(category_name)
