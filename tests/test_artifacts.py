import json

import pytest

from twisted_yetter.artifacts import (
    ARTIFACT_SCHEMA,
    ArtifactValidationError,
    LogReference,
    dumps_certificate,
    hash_json,
    make_certificate,
    validate_certificate,
)


def _base_certificate(status: str = "pass") -> dict:
    return make_certificate(
        status=status,  # type: ignore[arg-type]
        command="uv run python experiments/example.py",
        argv=["experiments/example.py", "--case", "toy"],
        git={"commit": "0" * 40, "dirty": False},
        tool_versions={"python": "3.11.0", "twisted_yetter": "0.1.0"},
        input_hash=hash_json({"case": "toy", "alpha": [0, 1]}),
        exact_output={
            "value": {
                "kind": "rational",
                "numerator": 1,
                "denominator": 2,
            },
            "sanity_checks": [
                {"name": "alpha_zero_matches_ordinary", "status": "pass"},
            ],
        },
        generator_script="experiments/example.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "uv run python experiments/example.py --case toy"
        ),
        log_references=[
            LogReference(
                path="experiments/results/example.log",
                sha256="1" * 64,
                bytes=1234,
                description="full stdout/stderr from toy run",
            )
        ],
    )


@pytest.mark.parametrize("status", ["pass", "fail", "inconclusive"])
def test_certificate_schema_accepts_all_research_statuses(status: str) -> None:
    certificate = _base_certificate(status)

    validate_certificate(certificate)

    assert certificate["schema"] == ARTIFACT_SCHEMA
    assert certificate["status"] == status
    assert certificate["git"] == {"commit": "0" * 40, "dirty": False}
    assert certificate["log_references"][0]["path"] == "experiments/results/example.log"


def test_certificate_requires_audit_metadata() -> None:
    certificate = _base_certificate()
    del certificate["input_hash"]

    with pytest.raises(ArtifactValidationError, match="input_hash"):
        validate_certificate(certificate)


def test_certificate_requires_git_dirty_flag() -> None:
    certificate = _base_certificate()
    certificate["git"] = {"commit": "0" * 40}

    with pytest.raises(ArtifactValidationError, match="git.dirty"):
        validate_certificate(certificate)


def test_certificate_preserves_exact_output_without_float_requirement() -> None:
    certificate = _base_certificate()

    assert certificate["exact_output"]["value"] == {
        "kind": "rational",
        "numerator": 1,
        "denominator": 2,
    }


def test_certificate_rejects_float_in_exact_output() -> None:
    certificate = _base_certificate()
    certificate["exact_output"] = {"value": 0.5}

    with pytest.raises(ArtifactValidationError, match="exact_output.value"):
        validate_certificate(certificate)


def test_certificate_serializes_as_stable_json() -> None:
    encoded = dumps_certificate(_base_certificate())

    decoded = json.loads(encoded)
    assert decoded["schema"] == ARTIFACT_SCHEMA
    assert encoded.endswith("\n")
