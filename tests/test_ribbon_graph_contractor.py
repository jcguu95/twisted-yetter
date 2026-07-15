import numpy as np

from experiments.sage.morse_pivotal_contract import (
    test_pivotal_profile as make_test_pivotal_profile,
)
from experiments.sage.ribbon_category_v2 import LegacyRibbonCategoryV2Adapter
from experiments.sage.ribbon_graph_contractor import (
    iter_weighted_projector_terms,
    projector_term_specs,
    ribbon_embedding_certificate,
    vacuum_path_gram_matrix,
)
from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.special_dotted_morphism import (
    build_ribbon_graph_ir_v2,
    compile_projected_morphism,
    validate_ribbon_graph_ir_v2,
)


class LegacyVec:
    labels = (0,)
    unit = 0
    category_id = "contractor-test-vec"
    pivotal_profile = make_test_pivotal_profile(category_id=category_id)

    def dual(self, label):
        return label

    def dimension(self, label):
        return 1.0

    def twist(self, label):
        return 1.0

    def fusion_multiplicity(self, left, right, output):
        return int(left == right == output == 0)

    def f_block(self, a, b, c, d):
        basis = ((0, 0, 0),)
        return {
            "left_basis": basis,
            "right_basis": basis,
            "left_index": {basis[0]: 0},
            "right_index": {basis[0]: 0},
            "right_to_left": np.eye(1, dtype=np.complex128),
            "left_to_right": np.eye(1, dtype=np.complex128),
        }

    def r_matrix(self, a, b, c, positive):
        return np.eye(1, dtype=np.complex128)


def vec(pairing=1.0):
    category = LegacyRibbonCategoryV2Adapter(LegacyVec())
    category.fusion_pairing = (
        lambda a, b, c: np.array([[complex(pairing)]], dtype=np.complex128)
    )
    category.fusion_pairing_inverse = (
        lambda a, b, c: np.array([[1.0 / complex(pairing)]], dtype=np.complex128)
    )
    category._coherence_certificate = {
        "status": "PASS_FULL_NUMERIC_RIBBON_COHERENCE",
        "category_data_hash": category.category_data_hash,
        "maximum_residual": 0.0,
    }
    return category


def one_puncture():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", at="far-right")
    m.cross(over="A1.left", under="red1.right")
    m.cross(over="red1.left", under="A1.left")
    m.cap("red1")
    m.cap("A1")
    mapping = {"red1": "red", "A1": "A"}
    ir = compile_projected_morphism(
        m.forms, component_by_piece=mapping, special_components=("red",)
    )
    return build_ribbon_graph_ir_v2(m.forms, ir)


def two_punctures():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", at="far-right")
    m.cross(over="A1.left", under="red1.right")
    m.cross(over="red1.left", under="A1.left")
    m.cross(over="A1.left", under="red1.left")
    m.cross(over="red1.right", under="A1.left")
    m.cap("red1")
    m.cap("A1")
    mapping = {"red1": "red", "A1": "A"}
    ir = compile_projected_morphism(
        m.forms, component_by_piece=mapping, special_components=("red",)
    )
    return build_ribbon_graph_ir_v2(m.forms, ir)


def test_projector_term_uses_inverse_nonorthogonal_path_pairing():
    category = vec(pairing=2.0)
    graph = two_punctures()
    coupon = next(node for node in graph["nodes"] if node["kind"] == "vacuum-projector-coupon")
    tree, basis, specs = projector_term_specs(category, coupon, {"A": 0})
    gram, inverse, residual = vacuum_path_gram_matrix(category, tree, basis)
    assert gram.tolist() == [[2.0 + 0.0j]]
    assert inverse.tolist() == [[0.5 + 0.0j]]
    assert residual == 0.0
    assert len(specs) == 1
    assert specs[0].coefficient == 0.5 + 0.0j


def test_one_factor_projector_expands_to_weighted_trivalent_graph():
    terms = list(iter_weighted_projector_terms(vec(), one_puncture(), {"A": 0}))
    assert len(terms) == 1
    assert terms[0].coefficient == 1.0 + 0.0j
    assert not any(
        node["kind"] == "vacuum-projector-coupon"
        for node in terms[0].graph["nodes"]
    )
    assert any(
        node["kind"] == "unit-channel-identity"
        for node in terms[0].graph["nodes"]
    )
    assert validate_ribbon_graph_ir_v2(terms[0].graph)["coupon_count"] == 0
    embedding = ribbon_embedding_certificate(terms[0].graph)
    assert embedding["status"] == (
        "PASS_GENUS_ZERO_ROTATION_SYSTEM_NO_ADDED_CROSSINGS"
    )
    assert embedding["unexpected_crossing_count"] == 0


def test_multiple_zero_puncture_coupons_expand_without_special_cases():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", between=("red1.left", "red1.right"))
    m.cup("blue1", at="far-right")
    m.cap("blue1")
    m.cap("A1")
    m.cap("red1")
    mapping = {"red1": "red", "blue1": "blue", "A1": "A"}
    ir = compile_projected_morphism(
        m.forms,
        component_by_piece=mapping,
        special_components=("red", "blue"),
    )
    graph = build_ribbon_graph_ir_v2(m.forms, ir)
    terms = list(iter_weighted_projector_terms(vec(), graph, {"A": 0}))
    assert len(terms) == 1
    assert terms[0].coefficient == 1.0 + 0.0j
    assert terms[0].graph["coupon_node_ids"] == {}
    assert validate_ribbon_graph_ir_v2(terms[0].graph)["coupon_count"] == 0
    assert ribbon_embedding_certificate(terms[0].graph)[
        "connected_component_count"
    ] == 1
