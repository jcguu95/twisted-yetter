"""Fail-closed pivotal capability contract for the native Morse evaluator."""

from __future__ import annotations

from pathlib import Path
import json
from typing import Any, Iterable


PROFILE_SCHEMA = "twisted-yetter.morse-pivotal-profile.v1"
REQUIRED_PROFILE_FIELDS = frozenset(
    {
        "schema",
        "status",
        "category_ids",
        "capabilities",
        "duality",
        "evaluation_coevaluation",
        "pivotal_structure",
        "fusion_space_pairing",
        "reverse_bend_scalars",
        "evidence",
    }
)
KNOWN_CAPABILITIES = frozenset(
    {
        "rigid_bends",
        "trivalent_pairing",
        "vacuum_projector",
        "ribbon_twist",
    }
)


class PivotalCapabilityError(ValueError):
    """Raised when graph evaluation would use unprovided pivotal data."""


def load_pivotal_profile(path: Path) -> dict[str, Any]:
    profile = json.loads(path.read_text())
    validate_pivotal_profile(profile)
    return profile


def validate_pivotal_profile(
    profile: Any, *, expected_category_id: str | None = None
) -> dict[str, Any]:
    if not isinstance(profile, dict):
        raise PivotalCapabilityError("category has no explicit pivotal profile")
    missing = REQUIRED_PROFILE_FIELDS - set(profile)
    if missing:
        raise PivotalCapabilityError(
            f"pivotal profile is missing required fields: {sorted(missing)!r}"
        )
    if profile["schema"] != PROFILE_SCHEMA:
        raise PivotalCapabilityError(
            f"unsupported pivotal profile schema: {profile['schema']!r}"
        )
    if profile["status"] != "SUPPORTED_FOR_NUMERIC_MORSE_CONTROLS":
        raise PivotalCapabilityError(
            f"pivotal profile status is not supported: {profile['status']!r}"
        )
    category_ids = profile["category_ids"]
    if not isinstance(category_ids, list) or not category_ids:
        raise PivotalCapabilityError("pivotal profile needs nonempty category_ids")
    if expected_category_id is not None and expected_category_id not in category_ids:
        raise PivotalCapabilityError(
            f"pivotal profile does not cover category {expected_category_id!r}"
        )
    capabilities = profile["capabilities"]
    if not isinstance(capabilities, dict):
        raise PivotalCapabilityError("pivotal profile capabilities must be an object")
    unknown = set(capabilities) - KNOWN_CAPABILITIES
    if unknown:
        raise PivotalCapabilityError(
            f"pivotal profile has unknown capabilities: {sorted(unknown)!r}"
        )
    for field in (
        "duality",
        "evaluation_coevaluation",
        "pivotal_structure",
        "fusion_space_pairing",
        "reverse_bend_scalars",
    ):
        if not isinstance(profile[field], dict) or not profile[field]:
            raise PivotalCapabilityError(
                f"pivotal profile field {field!r} must be a nonempty object"
            )
    if not isinstance(profile["evidence"], list) or not profile["evidence"]:
        raise PivotalCapabilityError("pivotal profile needs nonempty evidence")
    if (
        capabilities.get("trivalent_pairing")
        or capabilities.get("vacuum_projector")
    ) and profile["fusion_space_pairing"].get("orthonormal") is not True:
        raise PivotalCapabilityError(
            "trivalent/projector capabilities require an explicitly orthonormal fusion-space pairing"
        )
    if capabilities.get("rigid_bends") and profile[
        "evaluation_coevaluation"
    ].get("normalization") != "sqrt(quantum_dimension)":
        raise PivotalCapabilityError(
            "rigid bends require the recorded sqrt(quantum_dimension) normalization"
        )
    return profile


def require_pivotal_capabilities(
    category: Any, capabilities: Iterable[str]
) -> dict[str, Any]:
    required = frozenset(capabilities)
    unknown = required - KNOWN_CAPABILITIES
    if unknown:
        raise PivotalCapabilityError(
            f"unknown requested pivotal capabilities: {sorted(unknown)!r}"
        )
    profile = validate_pivotal_profile(
        getattr(category, "pivotal_profile", None),
        expected_category_id=getattr(category, "category_id", None),
    )
    absent = sorted(
        capability
        for capability in required
        if profile["capabilities"].get(capability) is not True
    )
    if absent:
        raise PivotalCapabilityError(
            f"category lacks required pivotal capabilities: {absent!r}"
        )
    return profile


def reverse_bend_scalar(category: Any, label: Any) -> complex:
    profile = require_pivotal_capabilities(category, {"rigid_bends"})
    specification = profile["reverse_bend_scalars"]
    kind = specification.get("kind")
    if kind == "explicit-map":
        key = str(label)
        try:
            real, imaginary = specification["values"][key]
        except (KeyError, TypeError, ValueError) as exc:
            raise PivotalCapabilityError(
                f"pivotal profile has no reverse-bend scalar for {label!r}"
            ) from exc
        return complex(float(real), float(imaginary))
    if kind == "integer-label-parity":
        parity = "even" if int(label) % 2 == 0 else "odd"
        real, imaginary = specification[parity]
        return complex(float(real), float(imaginary))
    raise PivotalCapabilityError(
        f"unsupported reverse-bend scalar specification: {kind!r}"
    )


def required_capabilities_for_forms(
    forms: Iterable[dict[str, Any]],
) -> frozenset[str]:
    required: set[str] = set()
    for form in forms:
        kind = form.get("kind")
        if kind in {"cup", "cap", "coevaluation", "evaluation"}:
            required.add("rigid_bends")
        elif kind in {"fuse", "split"}:
            required.add("trivalent_pairing")
        elif kind == "vacuum-projector":
            required.add("vacuum_projector")
        elif kind == "kink":
            required.add("ribbon_twist")
    return frozenset(required)


def test_pivotal_profile(
    *,
    category_id: str,
    reverse_bend_values: dict[str, list[float]] | None = None,
) -> dict[str, Any]:
    """Build an explicit test-only profile; production adapters load JSON."""

    return {
        "schema": PROFILE_SCHEMA,
        "status": "SUPPORTED_FOR_NUMERIC_MORSE_CONTROLS",
        "category_ids": [category_id],
        "capabilities": {capability: True for capability in KNOWN_CAPABILITIES},
        "duality": {"convention": "test fixture explicit dual method"},
        "evaluation_coevaluation": {
            "normalization": "sqrt(quantum_dimension)",
        },
        "pivotal_structure": {"convention": "test fixture"},
        "fusion_space_pairing": {
            "basis": "orthonormal test basis",
            "orthonormal": True,
        },
        "reverse_bend_scalars": {
            "kind": "explicit-map",
            "values": reverse_bend_values or {"0": [1.0, 0.0], "1": [1.0, 0.0]},
        },
        "evidence": [{"kind": "unit-test-fixture"}],
    }
