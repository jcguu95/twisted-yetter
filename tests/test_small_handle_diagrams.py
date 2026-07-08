import json
from pathlib import Path

from twisted_yetter.artifacts import file_sha256, validate_certificate


MANIFEST = Path(
    "experiments/results/small-handle-examples/kirby-diagram-svg-manifest-v1.json"
)


def test_small_handle_kirby_svg_manifest_is_reproducible() -> None:
    certificate = json.loads(MANIFEST.read_text())
    validate_certificate(certificate)

    exact = certificate["exact_output"]
    assert exact["status"] == "pass"
    assert exact["schema"] == "twisted-yetter.small-special-handle-kirby-svg-diagrams.v1"
    assert exact["mathematical_status"] == (
        "KIRBY_DIAGRAM_FIXTURES_NOT_THEOREM_LEVEL_RECOGNITION"
    )
    assert exact["diagram_count"] == 16
    assert exact["claim_boundary"] == {
        "not_rt_evaluation": True,
        "not_closed_4d_invariant": True,
        "not_kirby_slide_proof": True,
        "purpose": (
            "make every small special-handle algebra fixture visible "
            "as a fixed dotted Kirby diagram input"
        ),
    }


def test_all_small_handle_svg_diagram_hashes_match_manifest() -> None:
    certificate = json.loads(MANIFEST.read_text())

    for diagram in certificate["exact_output"]["diagrams"]:
        path = Path(diagram["path"])
        text = path.read_text()
        assert path.exists()
        assert text.startswith("<svg ")
        assert text.endswith("</svg>\n")
        assert file_sha256(path) == diagram["sha256"]
        assert diagram["diagram_status"] == "CONCRETE_SVG_KIRBY_FIXTURE_NOT_SLIDE_PROOF"


def test_nontrivial_small_handle_svg_records_dotted_and_relation_data() -> None:
    certificate = json.loads(MANIFEST.read_text())
    diagrams = {
        diagram["example_id"]: diagram for diagram in certificate["exact_output"]["diagrams"]
    }

    paired = diagrams["cp2-paired-one-handle"]
    assert paired["one_handles"] == ["D"]
    assert paired["two_handles"] == ["A", "B"]
    assert paired["d2_matrix_c2_to_c1"] == [[1, 1]]

    kernel_image = diagrams["cp2-kernel-image-all-handles"]
    assert kernel_image["three_handles"] == ["T"]
    assert kernel_image["d3_matrix_c3_to_c2"] == [[1], [-1], [0]]
    assert "3-handle T: A - B = 0" in Path(kernel_image["path"]).read_text()
