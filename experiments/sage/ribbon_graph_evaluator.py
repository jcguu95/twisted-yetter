"""Coupon-aware ribbon-graph evaluation through a modular killing loop.

For a single crossing-free special disk in a modular category, the vacuum
projector is represented by the original special loop colored by Omega and
divided by ``sum_i d_i^2``.  This backend keeps the graph/IR certificates as
the public input and uses the source Morse diagram only as a checked witness
for contracting that equivalent ribbon graph.
"""

from __future__ import annotations

from collections import defaultdict
from typing import Any, Iterable

from experiments.sage.morse_fusion_evaluator import (
    MorseEvaluator,
    analyze_topology,
    vacuum_coupon_path_basis,
)
from experiments.sage.morse_pivotal_contract import require_pivotal_capabilities
from experiments.scripts.special_dotted_morphism import (
    linearize_horizontal_disk_projector,
    piece_of,
    preflight_horizontal_disk_corridor,
    stable_json_hash,
)


SUPPORTED_KILLING_LOOP_CATEGORY_IDS = frozenset(
    {"su2-k2", "su2-k3", "su2-k4", "su2-k5", "su2-k6", "su2-k8"}
)


class RibbonGraphContractError(ValueError):
    """Raised when a graph cannot be contracted by the certified backend."""


def _semantic_topology_components(
    forms: tuple[dict[str, Any], ...], component_by_piece: dict[str, str]
) -> dict[str, str]:
    topology = analyze_topology(forms)
    semantic_by_topology: dict[str, set[str]] = defaultdict(set)
    for strand, topology_component in topology.component_by_strand.items():
        semantic_by_topology[topology_component].add(
            component_by_piece[piece_of(strand)]
        )
    ambiguous = {
        component: sorted(names)
        for component, names in semantic_by_topology.items()
        if len(names) != 1
    }
    if ambiguous:
        raise RibbonGraphContractError(
            f"topological components mix semantic labels: {ambiguous!r}"
        )
    return {
        next(iter(names)): topology_component
        for topology_component, names in semantic_by_topology.items()
    }


def _visible_self_writhe(
    forms: tuple[dict[str, Any], ...],
    component_by_piece: dict[str, str],
    projected_ir: dict[str, Any],
) -> dict[str, int]:
    visible = defaultdict(int)
    for crossing in projected_ir.get("crossings", ()):
        over = crossing["over_component"]
        under = crossing["under_component"]
        if over == under:
            visible[over] += int(crossing["sign"])
    for form in forms:
        if form.get("kind") != "kink":
            continue
        component = component_by_piece[piece_of(form["strand"])]
        sign = 1 if form["sign"] == "+" else -1
        visible[component] += sign * int(form.get("times", 1))
    return dict(visible)


class RibbonGraphEvaluator:
    """Evaluate one-special-component coupon graphs in certified SU(2)_k data.

    The category-independent coupon graph remains the semantic input.  The
    checked source Morse witness realizes the same projector by the modular
    killing-loop identity, so no new crossings or 3D routing are invented.
    """

    def __init__(
        self,
        category: Any,
        *,
        source_forms: Iterable[dict[str, Any]],
        component_by_piece: dict[str, str],
        projected_ir: dict[str, Any],
        total_framings: dict[str, int] | None = None,
    ):
        self.category = category
        self.source_forms = tuple(dict(form) for form in source_forms)
        self.component_by_piece = dict(component_by_piece)
        self.projected_ir = projected_ir
        category_id = getattr(category, "category_id", None)
        if category_id not in SUPPORTED_KILLING_LOOP_CATEGORY_IDS:
            raise RibbonGraphContractError(
                "modular killing-loop contraction is not certified for "
                f"category {category_id!r}"
            )
        require_pivotal_capabilities(
            category,
            {"rigid_bends", "ribbon_twist", "vacuum_projector"},
        )
        if projected_ir.get("special_component_count") != 1:
            raise RibbonGraphContractError(
                "killing-loop backend requires exactly one special component"
            )
        self.special = projected_ir["special_disk_certificates"][0][
            "special_component"
        ]
        if projected_ir.get("component_by_piece") != self.component_by_piece:
            raise RibbonGraphContractError(
                "projected IR component map does not match source witness"
            )
        semantic_components = set(self.component_by_piece.values())
        if set(projected_ir.get("component_order", ())) != semantic_components:
            raise RibbonGraphContractError(
                "projected IR component order does not match source witness"
            )
        if total_framings is None:
            raise RibbonGraphContractError(
                "total framings must be supplied explicitly; blackboard writhe "
                "is not silently promoted to the framed-link contract"
            )
        missing_framings = semantic_components - set(total_framings)
        extra_framings = set(total_framings) - semantic_components
        if missing_framings or extra_framings:
            raise RibbonGraphContractError(
                "total framing components mismatch: "
                f"missing={sorted(missing_framings)!r}, "
                f"extra={sorted(extra_framings)!r}"
            )
        self.total_framings = {
            component: int(total_framings[component])
            for component in semantic_components
        }
        self.visible_self_writhe = _visible_self_writhe(
            self.source_forms, self.component_by_piece, projected_ir
        )
        self.framing_corrections = {
            component: self.total_framings[component]
            - self.visible_self_writhe.get(component, 0)
            for component in semantic_components
        }
        self.semantic_to_topology = _semantic_topology_components(
            self.source_forms, self.component_by_piece
        )
        if set(self.semantic_to_topology) != semantic_components:
            raise RibbonGraphContractError(
                "source Morse topology does not realize every semantic component"
            )
        for form in self.source_forms:
            if form.get("kind") != "kink":
                continue
            if self.component_by_piece[piece_of(form["strand"])] == self.special:
                raise RibbonGraphContractError(
                    "special killing loop must have zero self-framing"
                )
        if self.framing_corrections[self.special] != 0:
            raise RibbonGraphContractError(
                "special dotted component must have zero total framing and "
                "zero visible self-writhe"
            )
        self.global_dimension_squared = sum(
            float(category.dimension(label)) ** 2 for label in category.labels
        )
        if self.global_dimension_squared <= 0:
            raise RibbonGraphContractError("category global dimension is not positive")
        self.morse = MorseEvaluator(category)

    def _validate_graph(self, graph: dict[str, Any]) -> dict[str, Any]:
        if graph.get("source_projected_ir_hash") != stable_json_hash(
            self.projected_ir
        ):
            raise RibbonGraphContractError(
                "coupon graph was not built from the supplied projected IR"
            )
        if graph.get("special_component") != self.special:
            raise RibbonGraphContractError("coupon graph special component mismatch")
        coupon_nodes = [
            node
            for node in graph.get("nodes", ())
            if node.get("kind") == "vacuum-projector-coupon"
        ]
        if len(coupon_nodes) != 1:
            raise RibbonGraphContractError(
                "coupon graph must contain exactly one vacuum projector"
            )
        coupon = coupon_nodes[0]
        if coupon.get("normalization") != (
            "IDEMPOTENT_UNIT_CHANNEL_NO_GLOBAL_DIMENSION_FACTOR"
        ):
            raise RibbonGraphContractError("unsupported coupon normalization")
        return coupon

    def fixed_label_value(
        self,
        graph: dict[str, Any],
        component_labels: dict[str, Any],
    ) -> tuple[complex, dict[str, Any]]:
        """Return the scalar after inserting the disk vacuum projector."""

        coupon = self._validate_graph(graph)
        ordinary_components = tuple(
            component
            for component in self.projected_ir["component_order"]
            if component != self.special
        )
        missing = set(ordinary_components) - set(component_labels)
        extra = set(component_labels) - set(ordinary_components)
        if missing or extra:
            raise RibbonGraphContractError(
                "ordinary component labels mismatch: "
                f"missing={sorted(missing)!r}, extra={sorted(extra)!r}"
            )

        contributions = []
        total = 0.0 + 0.0j
        for special_label in self.category.labels:
            semantic_labels = dict(component_labels)
            semantic_labels[self.special] = special_label
            topology_labels = {
                self.semantic_to_topology[component]: label
                for component, label in semantic_labels.items()
            }
            source_value, source_stats = self.morse.fixed_label_value(
                self.source_forms, topology_labels
            )
            blackboard_source_value = source_value
            framing_phase = 1.0 + 0.0j
            for component, label in semantic_labels.items():
                framing_phase *= complex(self.category.twist(label)) ** (
                    self.framing_corrections[component]
                )
            source_value *= framing_phase
            omega_coefficient = float(self.category.dimension(special_label))
            weighted = omega_coefficient * source_value
            total += weighted
            contributions.append(
                {
                    "special_label": special_label,
                    "omega_coefficient": omega_coefficient,
                    "blackboard_source_value": blackboard_source_value,
                    "framing_phase": framing_phase,
                    "source_value": source_value,
                    "weighted_source_value": weighted,
                    "source_stats": source_stats,
                }
            )
        value = total / self.global_dimension_squared
        return value, {
            "backend": "MODULAR_KILLING_LOOP_SOURCE_MORSE_WITNESS",
            "category_id": self.category.category_id,
            "special_component": self.special,
            "coupon_factor_count": len(coupon.get("factor_order", ())),
            "global_dimension_squared": self.global_dimension_squared,
            "normalization": "OMEGA_SPECIAL_LOOP_DIVIDED_BY_SUM_D_SQUARED",
            "total_framings": self.total_framings,
            "visible_self_writhe": self.visible_self_writhe,
            "framing_corrections": self.framing_corrections,
            "special_label_contributions": contributions,
        }


class DirectVacuumProjectorEvaluator:
    """Evaluate a certified horizontal special disk without modularity.

    This backend removes the special component and inserts the idempotent
    unit-channel projector directly in the ordinary Morse diagram.  It only
    accepts disks whose punctures admit the common horizontal slice certified
    by ``linearize_horizontal_disk_projector``.  General graph-level coupons
    remain unsupported and fail closed.
    """

    def __init__(
        self,
        category: Any,
        *,
        source_forms: Iterable[dict[str, Any]],
        component_by_piece: dict[str, str],
        projected_ir: dict[str, Any],
        total_framings: dict[str, int] | None = None,
    ):
        self.category = category
        self.source_forms = tuple(dict(form) for form in source_forms)
        self.component_by_piece = dict(component_by_piece)
        self.projected_ir = projected_ir
        require_pivotal_capabilities(
            category,
            {"rigid_bends", "ribbon_twist", "vacuum_projector"},
        )
        if projected_ir.get("special_component_count") != 1:
            raise RibbonGraphContractError(
                "direct projector backend requires exactly one special component"
            )
        self.special = projected_ir["special_disk_certificates"][0][
            "special_component"
        ]
        if projected_ir.get("component_by_piece") != self.component_by_piece:
            raise RibbonGraphContractError(
                "projected IR component map does not match source witness"
            )
        semantic_components = set(self.component_by_piece.values())
        if set(projected_ir.get("component_order", ())) != semantic_components:
            raise RibbonGraphContractError(
                "projected IR component order does not match source witness"
            )
        if total_framings is None:
            raise RibbonGraphContractError(
                "total framings must be supplied explicitly; blackboard writhe "
                "is not silently promoted to the framed-link contract"
            )
        missing_framings = semantic_components - set(total_framings)
        extra_framings = set(total_framings) - semantic_components
        if missing_framings or extra_framings:
            raise RibbonGraphContractError(
                "total framing components mismatch: "
                f"missing={sorted(missing_framings)!r}, "
                f"extra={sorted(extra_framings)!r}"
            )
        self.total_framings = {
            component: int(total_framings[component])
            for component in semantic_components
        }
        self.visible_self_writhe = _visible_self_writhe(
            self.source_forms, self.component_by_piece, projected_ir
        )
        self.framing_corrections = {
            component: self.total_framings[component]
            - self.visible_self_writhe.get(component, 0)
            for component in semantic_components
        }
        if self.framing_corrections[self.special] != 0:
            raise RibbonGraphContractError(
                "special dotted component must have zero total framing and "
                "zero visible self-writhe"
            )

        self.linearization = linearize_horizontal_disk_projector(
            self.source_forms, projected_ir
        )
        if self.linearization["status"] != (
            "PASS_HORIZONTAL_DISK_PROJECTOR_LINEARIZATION"
        ):
            preflight = self.linearization.get("preflight", {})
            raise RibbonGraphContractError(
                "direct projector cannot lower this coupon: "
                f"{self.linearization['status']}: {preflight.get('reason', '')}"
            )
        self.compiled_forms = tuple(self.linearization["compiled_forms"])
        ordinary_piece_map = {
            piece: component
            for piece, component in self.component_by_piece.items()
            if component != self.special
        }
        self.semantic_to_topology = _semantic_topology_components(
            self.compiled_forms, ordinary_piece_map
        )
        self.ordinary_components = tuple(
            component
            for component in projected_ir["component_order"]
            if component != self.special
        )
        if set(self.semantic_to_topology) != set(self.ordinary_components):
            raise RibbonGraphContractError(
                "compiled direct-projector diagram does not realize every "
                "ordinary component"
            )
        self.morse = MorseEvaluator(category)

    def _validate_graph(self, graph: dict[str, Any]) -> dict[str, Any]:
        if graph.get("source_projected_ir_hash") != stable_json_hash(
            self.projected_ir
        ):
            raise RibbonGraphContractError(
                "coupon graph was not built from the supplied projected IR"
            )
        if graph.get("special_component") != self.special:
            raise RibbonGraphContractError("coupon graph special component mismatch")
        coupons = [
            node
            for node in graph.get("nodes", ())
            if node.get("kind") == "vacuum-projector-coupon"
        ]
        if len(coupons) != 1:
            raise RibbonGraphContractError(
                "coupon graph must contain exactly one vacuum projector"
            )
        coupon = coupons[0]
        if coupon.get("normalization") != (
            "IDEMPOTENT_UNIT_CHANNEL_NO_GLOBAL_DIMENSION_FACTOR"
        ):
            raise RibbonGraphContractError("unsupported coupon normalization")
        return coupon

    def fixed_label_value(
        self,
        graph: dict[str, Any],
        component_labels: dict[str, Any],
    ) -> tuple[complex, dict[str, Any]]:
        """Return the scalar from a direct unit-channel projector."""

        coupon = self._validate_graph(graph)
        missing = set(self.ordinary_components) - set(component_labels)
        extra = set(component_labels) - set(self.ordinary_components)
        if missing or extra:
            raise RibbonGraphContractError(
                "ordinary component labels mismatch: "
                f"missing={sorted(missing)!r}, extra={sorted(extra)!r}"
            )
        topology_labels = {
            self.semantic_to_topology[component]: label
            for component, label in component_labels.items()
        }
        value, morse_stats = self.morse.fixed_label_value(
            self.compiled_forms, topology_labels
        )
        framing_phase = 1.0 + 0.0j
        for component, label in component_labels.items():
            framing_phase *= complex(self.category.twist(label)) ** (
                self.framing_corrections[component]
            )
        value *= framing_phase
        projector_plans = [
            plan
            for plan in morse_stats.get("plans", ())
            if plan.get("kind") == "vacuum-projector"
        ]
        return value, {
            "backend": "DIRECT_HORIZONTAL_VACUUM_PROJECTOR",
            "category_id": getattr(self.category, "category_id", None),
            "special_component": self.special,
            "coupon_factor_count": len(coupon.get("factor_order", ())),
            "normalization": "IDEMPOTENT_UNIT_CHANNEL_NO_GLOBAL_DIMENSION_FACTOR",
            "total_framings": self.total_framings,
            "visible_self_writhe": self.visible_self_writhe,
            "framing_corrections": self.framing_corrections,
            "framing_phase": framing_phase,
            "linearization_status": self.linearization["status"],
            "projector_plans": projector_plans,
            "morse_stats": morse_stats,
        }


class PointedVacuumProjectorEvaluator:
    """Evaluate an arbitrary one-disk coupon in a unitary pointed category.

    In a pointed category every tensor word has one simple root and a
    one-dimensional fusion space.  Consequently the collective vacuum
    projector is exactly zero when that root is nontrivial, and the identity
    when it is the tensor unit.  This permits graph-level special disks at
    unrelated Morse heights without a killing-loop identity or invented
    routing.
    """

    def __init__(
        self,
        category: Any,
        *,
        source_forms: Iterable[dict[str, Any]],
        component_by_piece: dict[str, str],
        projected_ir: dict[str, Any],
        total_framings: dict[str, int] | None = None,
    ):
        self.category = category
        self.source_forms = tuple(dict(form) for form in source_forms)
        self.component_by_piece = dict(component_by_piece)
        self.projected_ir = projected_ir
        require_pivotal_capabilities(
            category,
            {"rigid_bends", "ribbon_twist", "vacuum_projector"},
        )
        self._validate_pointed_category()
        if projected_ir.get("special_component_count") != 1:
            raise RibbonGraphContractError(
                "pointed projector backend requires exactly one special component"
            )
        self.special = projected_ir["special_disk_certificates"][0][
            "special_component"
        ]
        if projected_ir.get("component_by_piece") != self.component_by_piece:
            raise RibbonGraphContractError(
                "projected IR component map does not match source witness"
            )
        semantic_components = set(self.component_by_piece.values())
        if set(projected_ir.get("component_order", ())) != semantic_components:
            raise RibbonGraphContractError(
                "projected IR component order does not match source witness"
            )
        if total_framings is None:
            raise RibbonGraphContractError(
                "total framings must be supplied explicitly; blackboard writhe "
                "is not silently promoted to the framed-link contract"
            )
        missing_framings = semantic_components - set(total_framings)
        extra_framings = set(total_framings) - semantic_components
        if missing_framings or extra_framings:
            raise RibbonGraphContractError(
                "total framing components mismatch: "
                f"missing={sorted(missing_framings)!r}, "
                f"extra={sorted(extra_framings)!r}"
            )
        self.total_framings = {
            component: int(total_framings[component])
            for component in semantic_components
        }
        self.visible_self_writhe = _visible_self_writhe(
            self.source_forms, self.component_by_piece, projected_ir
        )
        self.framing_corrections = {
            component: self.total_framings[component]
            - self.visible_self_writhe.get(component, 0)
            for component in semantic_components
        }
        if self.framing_corrections[self.special] != 0:
            raise RibbonGraphContractError(
                "special dotted component must have zero total framing and "
                "zero visible self-writhe"
            )
        self.ordinary_forms = tuple(projected_ir["ordinary_forms"])
        ordinary_piece_map = {
            piece: component
            for piece, component in self.component_by_piece.items()
            if component != self.special
        }
        self.semantic_to_topology = _semantic_topology_components(
            self.ordinary_forms, ordinary_piece_map
        )
        self.ordinary_components = tuple(
            component
            for component in projected_ir["component_order"]
            if component != self.special
        )
        if set(self.semantic_to_topology) != set(self.ordinary_components):
            raise RibbonGraphContractError(
                "ordinary pointed diagram does not realize every component"
            )
        self.morse = MorseEvaluator(category)

    def _validate_pointed_category(self) -> None:
        labels = tuple(self.category.labels)
        if not labels or self.category.unit not in labels:
            raise RibbonGraphContractError("pointed category has invalid labels/unit")
        for label in labels:
            dimension = complex(self.category.dimension(label))
            if abs(dimension.imag) > 1e-10 or abs(dimension.real - 1.0) > 1e-10:
                raise RibbonGraphContractError(
                    "pointed backend requires every quantum dimension to be one"
                )
            dual = self.category.dual(label)
            if self.category.fusion_multiplicity(
                label, dual, self.category.unit
            ) != 1:
                raise RibbonGraphContractError(
                    f"label {label!r} is not invertible with its recorded dual"
                )
        for left in labels:
            for right in labels:
                outputs = tuple(self.category.fusion_outputs(left, right))
                if len(outputs) != 1 or int(outputs[0][1]) != 1:
                    raise RibbonGraphContractError(
                        "pointed backend requires one multiplicity-one output "
                        f"for {left!r} tensor {right!r}"
                    )

    def _validate_graph(self, graph: dict[str, Any]) -> dict[str, Any]:
        if graph.get("source_projected_ir_hash") != stable_json_hash(
            self.projected_ir
        ):
            raise RibbonGraphContractError(
                "coupon graph was not built from the supplied projected IR"
            )
        if graph.get("special_component") != self.special:
            raise RibbonGraphContractError("coupon graph special component mismatch")
        coupons = [
            node
            for node in graph.get("nodes", ())
            if node.get("kind") == "vacuum-projector-coupon"
        ]
        if len(coupons) != 1:
            raise RibbonGraphContractError(
                "coupon graph must contain exactly one vacuum projector"
            )
        coupon = coupons[0]
        if coupon.get("normalization") != (
            "IDEMPOTENT_UNIT_CHANNEL_NO_GLOBAL_DIMENSION_FACTOR"
        ):
            raise RibbonGraphContractError("unsupported coupon normalization")
        return coupon

    def fixed_label_value(
        self,
        graph: dict[str, Any],
        component_labels: dict[str, Any],
    ) -> tuple[complex, dict[str, Any]]:
        """Return the pointed fixed-sector scalar and projector certificate."""

        coupon = self._validate_graph(graph)
        missing = set(self.ordinary_components) - set(component_labels)
        extra = set(component_labels) - set(self.ordinary_components)
        if missing or extra:
            raise RibbonGraphContractError(
                "ordinary component labels mismatch: "
                f"missing={sorted(missing)!r}, extra={sorted(extra)!r}"
            )
        _tree, basis, projector = vacuum_coupon_path_basis(
            self.category, coupon, component_labels
        )
        projector_rank = projector["root_multiplicity_rank"]
        if projector_rank not in {0, 1} or len(basis) != projector_rank:
            raise RibbonGraphContractError(
                "pointed category produced a non-Boolean vacuum projector rank"
            )
        common_stats = {
            "backend": "DIRECT_POINTED_GRAPH_VACUUM_PROJECTOR",
            "category_id": getattr(self.category, "category_id", None),
            "special_component": self.special,
            "coupon_factor_count": len(coupon.get("factor_order", ())),
            "normalization": "IDEMPOTENT_UNIT_CHANNEL_NO_GLOBAL_DIMENSION_FACTOR",
            "projector": projector,
            "projector_rank": projector_rank,
            "total_framings": self.total_framings,
            "visible_self_writhe": self.visible_self_writhe,
            "framing_corrections": self.framing_corrections,
        }
        if projector_rank == 0:
            return 0.0 + 0.0j, {
                **common_stats,
                "status": "PRUNED_NO_VACUUM",
                "framing_phase": None,
                "morse_stats": None,
            }
        topology_labels = {
            self.semantic_to_topology[component]: label
            for component, label in component_labels.items()
        }
        value, morse_stats = self.morse.fixed_label_value(
            self.ordinary_forms, topology_labels
        )
        framing_phase = 1.0 + 0.0j
        for component, label in component_labels.items():
            framing_phase *= complex(self.category.twist(label)) ** (
                self.framing_corrections[component]
            )
        value *= framing_phase
        return value, {
            **common_stats,
            "status": "EVALUATED_POINTED_VACUUM_SECTOR",
            "framing_phase": framing_phase,
            "morse_stats": morse_stats,
        }


def _has_unitary_pointed_fusion_rules(category: Any) -> bool:
    try:
        labels = tuple(category.labels)
        if not labels or category.unit not in labels:
            return False
        for label in labels:
            dimension = complex(category.dimension(label))
            if abs(dimension.imag) > 1e-10 or abs(dimension.real - 1.0) > 1e-10:
                return False
        return all(
            len(outputs := tuple(category.fusion_outputs(left, right))) == 1
            and int(outputs[0][1]) == 1
            for left in labels
            for right in labels
        )
    except (AttributeError, TypeError, ValueError):
        return False


def build_vacuum_projector_evaluator(
    category: Any,
    *,
    source_forms: Iterable[dict[str, Any]],
    component_by_piece: dict[str, str],
    projected_ir: dict[str, Any],
    total_framings: dict[str, int] | None = None,
) -> DirectVacuumProjectorEvaluator | PointedVacuumProjectorEvaluator | RibbonGraphEvaluator:
    """Choose the strongest certified special-disk backend.

    Direct projector semantics always take precedence.  The modular
    killing-loop identity is only used when direct lowering is unavailable,
    the category is nonpointed, and its category id is explicitly certified.
    """

    forms = tuple(dict(form) for form in source_forms)
    preflight = preflight_horizontal_disk_corridor(forms, projected_ir)
    common = {
        "source_forms": forms,
        "component_by_piece": component_by_piece,
        "projected_ir": projected_ir,
        "total_framings": total_framings,
    }
    if preflight["status"] == "PASS_COMMON_HORIZONTAL_PROJECTOR_SLICE":
        return DirectVacuumProjectorEvaluator(category, **common)
    if _has_unitary_pointed_fusion_rules(category):
        return PointedVacuumProjectorEvaluator(category, **common)
    category_id = getattr(category, "category_id", None)
    if category_id in SUPPORTED_KILLING_LOOP_CATEGORY_IDS:
        return RibbonGraphEvaluator(category, **common)
    raise RibbonGraphContractError(
        "no certified vacuum-projector backend: horizontal direct lowering "
        f"failed with {preflight['status']!r}; category {category_id!r} is "
        "neither unitary pointed nor certified for the modular killing loop; "
        "general nonpointed nonhorizontal premodular contraction is not implemented"
    )
