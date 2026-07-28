import TwistedYetter.Kirby.Final.Semantics.IndependentEvaluatorSpecification
import TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance

/-!
# Fixed-H₂ local semantic conformance

This file checks the evaluator and the eight local moves for one arbitrary
fixed additive commutative group `H2`.  It intentionally does not construct
the public manifold-dependent family `X ↦ H₂(X)`.

The right-hand sides below are copied from the independently pinned human
semantics: dotted cuts are plain tensor-unit projectors and the dual-handle
normalization is `D / D ^ h₃`.
-/

namespace TwistedYetter.Kirby.Final.FixedH2LocalSemanticConformance

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.PremodularDottedCutting
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The implemented dotted operator is exactly the tensor-unit projector. -/
theorem dottedCut_is_plainTensorUnitProjector
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (X : C) :
    specialDottedCutOperator 𝒞 X =
      TwistedYetter.Kirby.ModularVacuumProjector.unitSummandProjector
        𝒞.toFusionCategoryData X :=
  rfl

/-- The implemented scalar is exactly Tham's dual-handle normalization. -/
theorem normalization_is_dualHandleNormalization
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation H2) :
    CanonicalPresentation.roleAwareNormalizationFactor 𝒞 presentation =
      𝒞.globalDimension /
        𝒞.globalDimension ^ presentation.topology.counts.h3 :=
  rfl

#print axioms
  TwistedYetter.Kirby.RoleAwareRepresentativeIndependence.Presentation.roleAwareCycleEval_respects_homology_class

#print axioms
  TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance.elementaryMove_invariant

end TwistedYetter.Kirby.Final.FixedH2LocalSemanticConformance
