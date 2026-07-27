import TwistedYetter.Kirby.LiteratureBackedHomologicalFourManifoldTopology
import TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance

/-!
# Presentation descent for the role-aware premodular evaluator

This module instantiates the generic Kirby quotient with the exact
role-aware presentation and its eight-event move language.
-/

namespace TwistedYetter.Kirby.PremodularRoleAwareFourManifoldInvariant

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.LiteratureBackedHomologicalFourManifoldTopology
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance
open TwistedYetter.Kirby.RoleAwarePresentationEvaluation
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
open TwistedYetter.Kirby.RoleAwareTableTwoMove
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The role-aware handle-presentation calculus. -/
noncomputable def handlePresentationTheory
    (H2 : Type uH) [AddCommGroup H2]
    (_localGeometry : LocalGeometryRealization H2) :
    HandlePresentationTheory where
  Presentation := Presentation H2
  Marking := fun presentation =>
    presentation.canonicalPresentation.topology.handleChain.SecondHomology
  ElementaryMove := fun source target =>
    TopologicalTableTwoMove
      source.canonicalPresentation.topology
      target.canonicalPresentation.topology
  transport := fun move =>
    (CanonicalSourceBackedMove.enrichedMove move).homologyTransport
      |>.chainEquivalence.secondHomologyAddEquiv

/-- The homology-level role-aware premodular presentation formula. -/
noncomputable def presentationEvaluation
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (H2 : Type uH) [AddCommGroup H2]
    (localGeometry : LocalGeometryRealization H2) :
    PresentationEvaluation
      (handlePresentationTheory H2 localGeometry) K where
  value := fun presentation alpha =>
    roleAwareEvalH2 𝒞 η presentation alpha

/-- Exhaustive eight-event invariance of the presentation formula. -/
theorem presentationEvaluation_localInvariant
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (H2 : Type uH) [AddCommGroup H2]
    (twoOverTwoEndpoints :
      RoleAwareTwoOverTwoBandMovie.CleanEndpointResolver 𝒞 η H2)
    (localGeometry : LocalGeometryRealization H2) :
    IsInvariantUnderElementaryMoves
      (presentationEvaluation 𝒞 η H2 localGeometry) := by
  intro source target move alpha
  have calculation :=
    elementaryMove_invariant 𝒞 η twoOverTwoEndpoints
      (localGeometry.realize move) alpha
  simpa [handlePresentationTheory, ElementaryMove.transport,
    localGeometry.forget_realize move] using calculation

end TwistedYetter.Kirby.PremodularRoleAwareFourManifoldInvariant
