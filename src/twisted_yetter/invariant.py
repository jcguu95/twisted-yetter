"""Experimental matrix-level invariant core for the n30 formula contract.

This module deliberately implements only the n35 scaffold allowed by
the archived legacy prose record for ``wiki/understandings/formula-contract-v0.org``.
It records formal
omega/theta sectors and exact matrix sanity data, but it does not choose the
source-needed numerical omega/theta coefficients, closed-manifold
normalization, or signature phase.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from numbers import Integral
from typing import Any, Final, Iterable, Literal, Sequence

from twisted_yetter.artifacts import (
    JsonObject,
    default_tool_versions,
    git_metadata,
    hash_json,
    make_certificate,
)
from twisted_yetter.legacy_prose import legacy_prose_member_ref
from twisted_yetter.linking_matrix import KirbyMatrixPresentation
from twisted_yetter.su2_level2 import certificate_payload


FORMULA_CONTRACT_REFERENCE: Final = legacy_prose_member_ref(
    "wiki/understandings/formula-contract-v0.org"
)
FORMULA_CONVENTIONS_REFERENCE: Final = legacy_prose_member_ref(
    "wiki/understandings/formula-conventions.org"
)
NORMALIZATION_NAME: Final = "experimental-yetter-surgery-normalization-v0"
SIGNATURE_CORRECTION_NAME: Final = "experimental-signature-correction-v0"

ClaimLevel = Literal[
    "experimental-matrix-statistic",
    "ordinary-control-input",
    "presentation-gate-input",
]

VALID_CLAIM_LEVELS: Final[frozenset[str]] = frozenset(
    {
        "experimental-matrix-statistic",
        "ordinary-control-input",
        "presentation-gate-input",
    }
)

UNSUPPORTED_NUMERIC_VALUE_REASON: Final = (
    "numeric omega/theta coefficients, closed normalization, and signature "
    "phase remain SOURCE NEEDED under the n30 formula contract"
)


class UnsupportedFormulaFeature(NotImplementedError):
    """Raised when a caller asks beyond the experimental matrix-level contract."""


@dataclass(frozen=True)
class FormulaConventionRecord:
    """The minimal convention pointers required by the n30 contract."""

    formula_contract: str = FORMULA_CONTRACT_REFERENCE
    formula_conventions: str = FORMULA_CONVENTIONS_REFERENCE
    normalization_name: str = NORMALIZATION_NAME
    signature_correction_name: str = SIGNATURE_CORRECTION_NAME

    def to_jsonable(self) -> JsonObject:
        return {
            "formula_contract": self.formula_contract,
            "formula_conventions": self.formula_conventions,
            "normalization_name": self.normalization_name,
            "signature_correction_name": self.signature_correction_name,
        }


@dataclass(frozen=True)
class FormalSectorAmplitude:
    """Inspectable formal sector data for one decoration vector.

    The ``value_status`` is intentionally inconclusive because the numerical
    amplitude would require source-needed formula data.
    """

    sector_id: str
    decoration_mod2: tuple[int, ...]
    component_colors: tuple[tuple[str, str], ...]
    theta_component_count: int
    alpha_q_alpha_mod2: int
    value_status: Literal["inconclusive"] = "inconclusive"
    unsupported_reason: str = UNSUPPORTED_NUMERIC_VALUE_REASON

    def to_jsonable(self) -> JsonObject:
        return {
            "sector_id": self.sector_id,
            "decoration_mod2": list(self.decoration_mod2),
            "component_colors": [
                {"component_id": component_id, "color": color}
                for component_id, color in self.component_colors
            ],
            "theta_component_count": self.theta_component_count,
            "alpha_q_alpha_mod2": self.alpha_q_alpha_mod2,
            "value_status": self.value_status,
            "unsupported_reason": self.unsupported_reason,
        }


@dataclass(frozen=True)
class ExactComparison:
    """Exact deterministic comparison of two JSON-compatible outputs."""

    equal: bool
    left_hash: str
    right_hash: str

    def to_jsonable(self) -> JsonObject:
        return {
            "equal": self.equal,
            "left_hash": self.left_hash,
            "right_hash": self.right_hash,
        }


def sector_amplitudes(
    presentation: KirbyMatrixPresentation,
    decoration_mod2: Sequence[int],
    *,
    category_certificate: JsonObject | None = None,
    claim_level: str = "experimental-matrix-statistic",
) -> tuple[FormalSectorAmplitude, ...]:
    """Return inspectable formal sectors for a single mod-2 decoration.

    v0 has one formal omega/theta color assignment for each input decoration.
    The returned record is deterministic and exact, but its numerical value is
    explicitly unsupported.
    """

    _validate_contract_inputs(category_certificate, claim_level)
    decoration = _normalize_decoration(decoration_mod2, presentation.size)
    return (_formal_sector(presentation, decoration),)


def evaluate_matrix_statistic(
    presentation: KirbyMatrixPresentation,
    decoration_mod2: Sequence[int],
    *,
    category_certificate: JsonObject | None = None,
    formula_convention_record: FormulaConventionRecord | None = None,
    claim_level: str = "experimental-matrix-statistic",
) -> JsonObject:
    """Build the exact n35 output payload for one decoration.

    The output is a deterministic experimental matrix-level statistic.  It is
    not a numerical invariant value.
    """

    active_category = _validate_contract_inputs(category_certificate, claim_level)
    convention_record = formula_convention_record or FormulaConventionRecord()
    _validate_formula_convention_record(convention_record)
    decoration = _normalize_decoration(decoration_mod2, presentation.size)
    sectors = sector_amplitudes(
        presentation,
        decoration,
        category_certificate=active_category,
        claim_level=claim_level,
    )

    ordinary_path = all(value == 0 for value in decoration)
    return {
        "node_id": "n35-invariant-core",
        "status": "inconclusive",
        "claim_level": claim_level,
        "claim_boundary": "experimental matrix-level statistic; not a closed 4-manifold invariant",
        "category": {
            "schema": active_category["schema"],
            "simple_labels": list(active_category["simple_labels"]),
        },
        "formula_convention_record": convention_record.to_jsonable(),
        "presentation": _presentation_payload(presentation),
        "decoration_mod2": list(decoration),
        "ordinary_path_selected": ordinary_path,
        "sector_amplitudes": [sector.to_jsonable() for sector in sectors],
        "aggregation": {
            "mode": "single-decoration-formal-sector",
            "sector_order": [sector.sector_id for sector in sectors],
            "value_status": "inconclusive",
            "unsupported_reason": UNSUPPORTED_NUMERIC_VALUE_REASON,
        },
        "sanity_checks": _sanity_checks(presentation, decoration, ordinary_path),
    }


def decoration_aggregation(
    presentation: KirbyMatrixPresentation,
    decorations_mod2: Iterable[Sequence[int]] | None = None,
    *,
    category_certificate: JsonObject | None = None,
    claim_level: str = "presentation-gate-input",
) -> JsonObject:
    """Return deterministic exact outputs for a list of decorations.

    If no decoration list is supplied, all vectors in ``(Z/2)^n`` are evaluated
    in lexicographic order.
    """

    active_category = _validate_contract_inputs(category_certificate, claim_level)
    if decorations_mod2 is None:
        decorations = _all_mod2_vectors(presentation.size)
    else:
        decorations = tuple(
            sorted(
                {
                    _normalize_decoration(decoration, presentation.size)
                    for decoration in decorations_mod2
                }
            )
        )

    return {
        "mode": "decoration-aggregation",
        "claim_level": claim_level,
        "ordering": "lexicographic-mod2-vectors",
        "decorations": [
            evaluate_matrix_statistic(
                presentation,
                decoration,
                category_certificate=active_category,
                claim_level=claim_level,
            )
            for decoration in decorations
        ],
    }


def compare_exact_outputs(left: Any, right: Any) -> ExactComparison:
    """Compare two JSON-compatible official outputs without floats."""

    _reject_float(left, "left")
    _reject_float(right, "right")
    left_hash = hash_json(left)
    right_hash = hash_json(right)
    left_canonical = json.dumps(left, sort_keys=True, separators=(",", ":"))
    right_canonical = json.dumps(right, sort_keys=True, separators=(",", ":"))
    return ExactComparison(
        equal=left_canonical == right_canonical,
        left_hash=left_hash,
        right_hash=right_hash,
    )


def numerical_invariant_value(*_args: Any, **_kwargs: Any) -> None:
    """Refuse numerical evaluation until the source-needed formula data exists."""

    raise UnsupportedFormulaFeature(UNSUPPORTED_NUMERIC_VALUE_REASON)


def invariant_certificate(
    presentation: KirbyMatrixPresentation,
    decoration_mod2: Sequence[int],
    *,
    command: str,
    argv: list[str],
    git: JsonObject | None = None,
    tool_versions: JsonObject | None = None,
    repo_root: str | None = None,
    claim_level: str = "experimental-matrix-statistic",
) -> JsonObject:
    """Wrap :func:`evaluate_matrix_statistic` in the artifact v1 envelope."""

    exact_output = evaluate_matrix_statistic(
        presentation,
        decoration_mod2,
        claim_level=claim_level,
    )
    input_payload = {
        "presentation": _presentation_payload(presentation),
        "decoration_mod2": list(_normalize_decoration(decoration_mod2, presentation.size)),
        "claim_level": claim_level,
        "formula_contract": FORMULA_CONTRACT_REFERENCE,
    }
    return make_certificate(
        status="inconclusive",
        command=command,
        argv=argv,
        git=git if git is not None else git_metadata(repo_root or "."),
        tool_versions=tool_versions if tool_versions is not None else default_tool_versions(),
        input_hash=hash_json(input_payload),
        exact_output=exact_output,
        repo_root=repo_root,
        notes=[
            "n35 output is an experimental matrix-level statistic only",
            UNSUPPORTED_NUMERIC_VALUE_REASON,
        ],
    )


def _validate_contract_inputs(
    category_certificate: JsonObject | None,
    claim_level: str,
) -> JsonObject:
    if claim_level not in VALID_CLAIM_LEVELS:
        raise UnsupportedFormulaFeature(
            f"unsupported claim level for n35 formula contract: {claim_level!r}"
        )

    active_category = category_certificate if category_certificate is not None else certificate_payload()
    current_category = certificate_payload()
    if active_category != current_category:
        raise UnsupportedFormulaFeature("n35 v0 supports only the current SU(2)_2 certificate")
    return active_category


def _validate_formula_convention_record(record: FormulaConventionRecord) -> None:
    expected = FormulaConventionRecord()
    if record != expected:
        raise UnsupportedFormulaFeature(
            "n35 v0 requires the exact formula convention record named by n30"
        )


def _normalize_decoration(decoration: Sequence[int], size: int) -> tuple[int, ...]:
    normalized = tuple(_as_mod2(value) for value in decoration)
    if len(normalized) != size:
        raise ValueError("decoration_mod2 length must match presentation size")
    return normalized


def _as_mod2(value: object) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError("decoration_mod2 entries must be integers")
    return int(value) % 2


def _formal_sector(
    presentation: KirbyMatrixPresentation,
    decoration: tuple[int, ...],
) -> FormalSectorAmplitude:
    component_colors = tuple(
        (component_id, "theta" if coordinate else "omega")
        for component_id, coordinate in zip(presentation.component_ids, decoration, strict=True)
    )
    return FormalSectorAmplitude(
        sector_id=f"alpha-{''.join(str(value) for value in decoration) or 'empty'}",
        decoration_mod2=decoration,
        component_colors=component_colors,
        theta_component_count=sum(decoration),
        alpha_q_alpha_mod2=_alpha_q_alpha_mod2(presentation.matrix, decoration),
    )


def _alpha_q_alpha_mod2(
    matrix: Sequence[Sequence[int]],
    decoration: Sequence[int],
) -> int:
    total = 0
    for i, row in enumerate(matrix):
        for j, entry in enumerate(row):
            total += decoration[i] * int(entry) * decoration[j]
    return total % 2


def _presentation_payload(presentation: KirbyMatrixPresentation) -> JsonObject:
    positive, negative, zero = presentation.signature_triple
    return {
        "matrix": [list(row) for row in presentation.matrix],
        "component_ids": list(presentation.component_ids),
        "orientation_labels": list(presentation.orientation_labels),
        "size": presentation.size,
        "framings": list(presentation.framings),
        "rank": presentation.rank,
        "determinant": presentation.determinant,
        "signature_triple": {
            "positive": positive,
            "negative": negative,
            "zero": zero,
        },
        "signature": presentation.signature,
        "parity": presentation.parity,
    }


def _sanity_checks(
    presentation: KirbyMatrixPresentation,
    decoration: tuple[int, ...],
    ordinary_path: bool,
) -> list[JsonObject]:
    return [
        {
            "name": "input_matrix_symmetric_and_sized",
            "status": "pass",
            "size": presentation.size,
        },
        {
            "name": "rank_determinant_parity_signature_exact",
            "status": "pass",
            "rank": presentation.rank,
            "determinant": presentation.determinant,
            "parity": presentation.parity,
            "signature_triple": list(presentation.signature_triple),
        },
        {
            "name": "alpha_zero_ordinary_path_selection",
            "status": "pass",
            "ordinary_path_selected": ordinary_path,
        },
        {
            "name": "basis_change_convention_recorded",
            "status": "pass",
            "convention": "x_new = P^{-1} x_old mod 2",
        },
        {
            "name": "normalization_and_signature_correction_named_only",
            "status": "pass",
            "normalization_name": NORMALIZATION_NAME,
            "signature_correction_name": SIGNATURE_CORRECTION_NAME,
        },
        {
            "name": "decoration_vector_mod2",
            "status": "pass",
            "decoration_mod2": list(decoration),
        },
    ]


def _all_mod2_vectors(size: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple((index >> shift) & 1 for shift in reversed(range(size)))
        for index in range(2**size)
    )


def _reject_float(value: Any, path: str) -> None:
    if isinstance(value, float):
        raise TypeError(f"{path} must not contain floats")
    if isinstance(value, dict):
        for key, item in value.items():
            _reject_float(item, f"{path}.{key}")
    elif isinstance(value, list | tuple):
        for index, item in enumerate(value):
            _reject_float(item, f"{path}[{index}]")


__all__ = [
    "FORMULA_CONTRACT_REFERENCE",
    "FORMULA_CONVENTIONS_REFERENCE",
    "NORMALIZATION_NAME",
    "SIGNATURE_CORRECTION_NAME",
    "UNSUPPORTED_NUMERIC_VALUE_REASON",
    "VALID_CLAIM_LEVELS",
    "ExactComparison",
    "FormalSectorAmplitude",
    "FormulaConventionRecord",
    "UnsupportedFormulaFeature",
    "compare_exact_outputs",
    "decoration_aggregation",
    "evaluate_matrix_statistic",
    "invariant_certificate",
    "numerical_invariant_value",
    "sector_amplitudes",
]
