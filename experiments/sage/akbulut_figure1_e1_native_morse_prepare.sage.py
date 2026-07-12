"""Prepare the recorded Akbulut Figure 1 E(1) braid as native Morse input."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys

from sage.all import ZZ  # Initialize Sage's parent/ring registry before Link.
from sage.knots.link import Link

from experiments.sage.braid_closure_morse import (
    braid_closure_morse_forms,
    trace_fundamental_forms,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE_SCRIPT = REPO_ROOT / "experiments" / "sage" / "akbulut_figure1_e1_su2_2_untwisted_comparison.sage.py"
SOURCE_INPUT = REPO_ROOT / "experiments" / "inputs" / "akbulut" / "figure1-e1-crossing-table.json"
OUTPUT = REPO_ROOT / "experiments" / "inputs" / "akbulut" / "figure1-e1-braid-closure-morse-v1.json"


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def main():
    source = load_module(SOURCE_SCRIPT, "akbulut_figure1_source_conversion")
    payload = json.loads(SOURCE_INPUT.read_text())
    component_words, crossing_signs, _ = source.source_oriented_gauss_code(payload)
    braid = Link([component_words, crossing_signs]).braid()
    n_strands = int(braid.parent().strands())
    braid_word = tuple(int(generator) for generator in braid.Tietze())
    source_components = source.component_order(payload)
    source_target_matrix = source.target_matrix(payload)
    from twisted_yetter.local_piece import braid_closure_linking_matrix

    braid_linking = [
        [int(entry) for entry in row]
        for row in braid_closure_linking_matrix(n_strands, braid_word)
    ]
    candidates = source.component_permutations(source_target_matrix, braid_linking)
    selected = source.choose_permutation(source_components, candidates)
    if selected is None:
        raise ValueError("could not match braid components to source components")
    component_order = [source_components[index] for index in selected]
    framings = [source.component_framings(payload)[index] for index in selected]
    forms, component_index = braid_closure_morse_forms(
        n_strands, braid_word, framings
    )
    drawing = trace_fundamental_forms(forms)
    OUTPUT.write_text(
        json.dumps(
            {
                "schema": "twisted-yetter.akbulut-figure1-braid-closure-morse.v1",
                "status": "MECHANICALLY_DERIVED_FROM_ADMITTED_CROSSING_TABLE_PIPELINE",
                "source_input": str(SOURCE_INPUT.relative_to(REPO_ROOT)),
                "source_conversion_script": str(SOURCE_SCRIPT.relative_to(REPO_ROOT)),
                "n_strands": n_strands,
                "braid_word": list(braid_word),
                "braid_word_length": len(braid_word),
                "component_order_in_braid": component_order,
                "framings_in_braid_order": framings,
                "morse_component_to_braid_component_index": component_index,
                **drawing,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    print(OUTPUT.resolve())


if __name__ == "__main__":
    main()
