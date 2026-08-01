#!/usr/bin/env python3
"""Fail closed if the independent semantic entry imports downstream code."""

from __future__ import annotations

import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parent
INDEPENDENT_PREFIX = (
    "TwistedYetter.Kirby.Final.Semantics.Independent."
)
FORBIDDEN_SOURCE_TOKENS = (
    "KnotInS3",
    "EmbeddedDiskInS3",
    "IntersectionPoint",
    "IndependentPresentationSpecification",
    "IndependentHomologyMarkingSpecification",
    "IndependentMoveHomologyTransportSpecification",
    "IndependentGraphicalCalculusSpecification",
    "IndependentEvaluatorSpecification",
    "IndependentPublicInvariantSpecification",
)
PROOF_HOLES = re.compile(r"\b(sorry|admit)\b")


def main() -> int:
    failures: list[str] = []
    lean_files = sorted(ROOT.glob("*.lean"))

    for path in lean_files:
        text = path.read_text(encoding="utf-8")
        for line_number, line in enumerate(text.splitlines(), start=1):
            if line.startswith("import "):
                module = line.removeprefix("import ").strip()
                if not (
                    module == "Mathlib"
                    or module.startswith("Mathlib.")
                    or module.startswith(INDEPENDENT_PREFIX)
                ):
                    failures.append(
                        f"{path.name}:{line_number}: forbidden import {module}"
                    )

        for token in FORBIDDEN_SOURCE_TOKENS:
            if token in text:
                failures.append(f"{path.name}: forbidden token {token}")

        if PROOF_HOLES.search(text):
            failures.append(f"{path.name}: proof hole")

    entry = (ROOT / "Entry.lean").read_text(encoding="utf-8")
    for module in (
        "Algebra",
        "Diagram",
        "Homology",
        "Moves",
        "Graphical",
        "Evaluator",
        "Invariant",
    ):
        expected = f"import {INDEPENDENT_PREFIX}{module}"
        if expected not in entry:
            failures.append(f"Entry.lean: missing {module} import")

    if failures:
        print("\n".join(failures))
        return 1

    print(
        "PASS: independent semantic imports and source tokens are quarantined"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
